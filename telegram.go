package main

import (
	"bytes"
	"context"
	"crypto/rand"
	"encoding/binary"
	"fmt"
	"io"
	"math/bits"
	"net"
	"strings"
	"time"
)

// Telegram's MTProto data centres. The addresses are hardcoded on purpose: a
// client dials them directly, so resolving a name first would test a path
// Telegram itself never takes.
//
// ponytail: IPv4 only. The tunnel carries both families whatever -6 selects, so
// a v6 scan reaches these as well; add the v6 DCs if a network turns up where it
// does not.
var telegramDCs = []string{
	"149.154.175.50:443",  // DC1
	"149.154.167.51:443",  // DC2
	"149.154.175.100:443", // DC3
	"149.154.167.91:443",  // DC4
	"91.108.56.130:443",   // DC5
}

type dialFunc func(ctx context.Context, addr string) (net.Conn, error)

// allDCs is the reachedDCs mask with every entry of telegramDCs set.
var allDCs = uint8(1<<len(telegramDCs)) - 1

// Every address at once under one deadline. Walking them in turn would cost
// len(addrs) x timeout on a blocked exit, where each dial runs the clock out
// in full - a scan pays that per endpoint.
//
// An account lives on one DC and the client cannot pick another, so an exit
// where only some DCs answer is an exit where some accounts never connect
// (seen live: WARP exits in FRA reached DC1/3/5 while DC2/4 never answered,
// and Telegram Desktop sat in "connecting..."). reached is therefore a bitmask
// (bit i = addrs[i]) and the caller wants all of it set; rtt is the slowest
// answer, since the DC a client sits on may well be that one.
func reachedDCs(ctx context.Context, dial dialFunc, addrs []string, timeout time.Duration) (rtt time.Duration, reached uint8) {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	type result struct {
		i   int
		rtt time.Duration
		ok  bool
	}
	res := make(chan result, len(addrs))
	for i, addr := range addrs {
		go func(i int, addr string) {
			// Each dial times itself: one shared start would bill the wait for a
			// goroutine to get scheduled (real under a loaded pool) to the DC, and
			// this number is what the TG column reports.
			start := time.Now()
			conn, err := dial(ctx, addr)
			if err != nil {
				res <- result{i: i}
				return
			}
			conn.Close()
			res <- result{i, time.Since(start), true}
		}(i, addr)
	}

	for range addrs {
		r := <-res // every dial honours ctx, so this returns by the deadline
		if r.ok {
			reached |= 1 << r.i
			rtt = max(rtt, r.rtt)
		}
	}
	return rtt, reached
}

// tgPartialStr renders a mask short of allDCs for the TG column.
func tgPartialStr(reached uint8) string {
	if reached == 0 {
		return "blocked"
	}
	return fmt.Sprintf("%d/%d", bits.OnesCount8(reached), len(telegramDCs))
}

// dcNames lists the DCs in mask as "DC2, DC4".
func dcNames(mask uint8) string {
	var names []string
	for i := range telegramDCs {
		if mask&(1<<i) != 0 {
			names = append(names, fmt.Sprintf("DC%d", i+1))
		}
	}
	return strings.Join(names, ", ")
}

// buildReqPQ frames an unencrypted req_pq_multi with mdlen bytes of message
// (constructor + nonce + random padding). mtprotoProbe uses mdlen 20,
// mtuProbe mtuProbeLen. Shared framing keeps both probes' bytes identical
// where they overlap: the fake DC in TestMTProtoProbe asserts the 48-byte
// plain request exactly.
func buildReqPQ(mdlen int) (msg []byte, nonce [16]byte) {
	msg = make([]byte, 0, 4+4+20+mdlen)
	msg = append(msg, 0xee, 0xee, 0xee, 0xee)                                  // intermediate transport
	msg = binary.LittleEndian.AppendUint32(msg, uint32(20+mdlen))              // frame: auth_key_id + msg_id + len + message
	msg = append(msg, make([]byte, 8)...)                                      // auth_key_id = 0, plaintext message
	msg = binary.LittleEndian.AppendUint64(msg, uint64(time.Now().Unix())<<32) // msg_id: unixtime<<32, %4 == 0 as clients must
	msg = binary.LittleEndian.AppendUint32(msg, uint32(mdlen))                 // message_data_length
	msg = binary.LittleEndian.AppendUint32(msg, 0xbe7e8ef1)                    // req_pq_multi
	rand.Read(nonce[:])
	msg = append(msg, nonce[:]...)
	if pad := mdlen - 20; pad > 0 {
		msg = append(msg, make([]byte, pad)...)
		rand.Read(msg[len(msg)-pad:])
	}
	return msg, nonce
}

// readResPQ reads one frame and checks it through the nonce echo. Both probes
// share it: the request size differs, the answer shape does not.
func readResPQ(conn net.Conn, nonce []byte) error {
	var hdr [4]byte
	if _, err := io.ReadFull(conn, hdr[:]); err != nil {
		return err
	}
	// res_pq is ~84 bytes; anything outside a sane frame is not Telegram.
	n := binary.LittleEndian.Uint32(hdr[:])
	if n < resPQMin || n > 1<<16 {
		return fmt.Errorf("mtproto: implausible frame length %d", n)
	}
	// A plausible length alone is four bytes any middlebox can fake: read the
	// body and hold it to res_pq, down to the nonce we just sent.
	body := make([]byte, n)
	if _, err := io.ReadFull(conn, body); err != nil {
		return err
	}
	if id := binary.LittleEndian.Uint64(body[:8]); id != 0 {
		return fmt.Errorf("mtproto: answer carries auth_key_id %#x, want a plaintext one", id)
	}
	if l := binary.LittleEndian.Uint32(body[16:20]); l < 4+16 || 20+int(l) > len(body) {
		return fmt.Errorf("mtproto: message_data_length %d does not fit a %d-byte frame", l, n)
	}
	if c := binary.LittleEndian.Uint32(body[20:24]); c != 0x05162463 {
		return fmt.Errorf("mtproto: answer constructor %#x, want res_pq", c)
	}
	// 128 random bits coming back is what proves something parsed our
	// req_pq_multi, rather than answered with bytes of its own.
	if !bytes.Equal(body[24:40], nonce) {
		return fmt.Errorf("mtproto: answer does not echo our nonce")
	}
	return nil
}

// mtprotoProbe speaks just enough MTProto to make a DC answer: the
// intermediate-transport magic plus an unencrypted req_pq_multi. A bare TCP
// connect proves nothing — DPI boxes complete the handshake toward Telegram
// and silently drop the payload, so connect-only checks pass everywhere.
// Only response bytes framed by the transport mean the DC really talked back.
func mtprotoProbe(ctx context.Context, conn net.Conn) error {
	if d, ok := ctx.Deadline(); ok {
		conn.SetDeadline(d)
		defer conn.SetDeadline(time.Time{})
	}

	msg, nonce := buildReqPQ(20)
	if _, err := conn.Write(msg); err != nil {
		return err
	}
	return readResPQ(conn, nonce[:])
}

// Smallest res_pq worth reading: auth_key_id, msg_id, message_data_length,
// then the constructor and our nonce. server_nonce, pq and the fingerprints
// follow but are never looked at.
const resPQMin = 8 + 8 + 4 + 4 + 16

// Dialled through the tunnel's own stack rather than s.client: that client's
// transport ignores the requested address and always dials metaDialAddr().
// A dial only counts once the DC has answered an MTProto request, so the
// reported RTT is time-to-response, not time-to-SYN-ACK. reached is the mask
// of DCs that answered; the row is Telegram-ok only when it equals allDCs.
func (s *ipStack) telegramRTT(ctx context.Context, timeout time.Duration) (rtt time.Duration, reached uint8) {
	return reachedDCs(ctx, func(ctx context.Context, addr string) (net.Conn, error) {
		conn, err := s.tnet.DialContext(ctx, "tcp", addr)
		if err != nil {
			return nil, err
		}
		if err := mtprotoProbe(ctx, conn); err != nil {
			conn.Close()
			return nil, err
		}
		return conn, nil
	}, telegramDCs, timeout)
}

// mtuProbeLen is the message_data_length of the MTU probe: a req_pq body of
// 20 bytes plus random padding, sized so the frame (~1230 bytes on the wire
// with headers) exercises full-size in-tunnel segments without exceeding the
// 1280 interface MTU.
const mtuProbeLen = 1200

// mtuProbe asks the DC the same req_pq question with a full-size body and
// checks the res_pq answer the same way short probes do: an answer that
// arrived whole proves full-size segments survive the exit, where the 48-byte
// TG dial proves only small ones do. Upload direction only — the answer stays
// ~100 bytes, and bulk download has no unauthenticated probe.
func mtuProbe(ctx context.Context, conn net.Conn) error {
	if d, ok := ctx.Deadline(); ok {
		conn.SetDeadline(d)
		defer conn.SetDeadline(time.Time{})
	}

	msg, nonce := buildReqPQ(mtuProbeLen)
	if _, err := conn.Write(msg); err != nil {
		return err
	}
	return readResPQ(conn, nonce[:])
}

// telegramMTURTT runs one padded req_pq per DC and folds the answers the way
// telegramRTT does. Only the mask matters downstream: a DC whose padded
// answer arrived whole passes full-size segments.
func (s *ipStack) telegramMTURTT(ctx context.Context, timeout time.Duration) uint8 {
	_, reached := reachedDCs(ctx, func(ctx context.Context, addr string) (net.Conn, error) {
		conn, err := s.tnet.DialContext(ctx, "tcp", addr)
		if err != nil {
			return nil, err
		}
		if err := mtuProbe(ctx, conn); err != nil {
			conn.Close()
			return nil, err
		}
		return conn, nil
	}, telegramDCs, timeout)
	return reached
}
