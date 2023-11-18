package uint128

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
)

var (
	Zero = Uint128{0, 0}                           // 0
	Max  = Uint128{math.MaxUint64, math.MaxUint64} // 340282366920938463463374607431768211455
)

// A Uint128 is an unsigned 128-bit number.
type Uint128 struct {
	Lo, Hi uint64
}

// IsZero returns true if u == 0.
func (u Uint128) IsZero() bool {
	return u == Uint128{}
}

// Equals returns true if u == v.
//
// Uint128 values can be compared directly with ==, but use of the Equals method
// is preferred for consistency.
func (u Uint128) Equals(v Uint128) bool {
	return u == v
}

// Equals64 returns true if u == v.
func (u Uint128) Equals64(v uint64) bool {
	return u.Lo == v && u.Hi == 0
}

// LessThan returns true if u < v.
func (u Uint128) LessThan(v Uint128) bool {
	return u.Cmp(v) == -1
}

// LessThan64 returns true if u < v.
func (u Uint128) LessThan64(v uint64) bool {
	return u.Cmp64(v) == -1
}

// GreaterThan returns true if u > v.
func (u Uint128) GreaterThan(v Uint128) bool {
	return u.Cmp(v) == 1
}

// GreaterThan64 returns true if u > v.
func (u Uint128) GreaterThan64(v uint64) bool {
	return u.Cmp64(v) == 1
}

// LessThanOrEqual returns true if u <= v.
func (u Uint128) LessThanOrEqual(v Uint128) bool {
	return u.Cmp(v) != 1
}

// LessThanOrEqual64 returns true if u <= v.
func (u Uint128) LessThanOrEqual64(v uint64) bool {
	return u.Cmp64(v) != 1
}

// GreaterThanOrEqual returns true if u >= v.
func (u Uint128) GreaterThanOrEqual(v Uint128) bool {
	return u.Cmp(v) != -1
}

// GreaterThanOrEqual64 returns true if u >= v.
func (u Uint128) GreaterThanOrEqual64(v uint64) bool {
	return u.Cmp64(v) != -1
}

// Cmp compares u and v and returns:
//
//	-1 if u <  v
//	 0 if u == v
//	+1 if u >  v
func (u Uint128) Cmp(v Uint128) int {
	if u == v {
		return 0
	} else if u.Hi < v.Hi || (u.Hi == v.Hi && u.Lo < v.Lo) {
		return -1
	} else {
		return 1
	}
}

// Cmp64 compares u and v and returns:
//
//	-1 if u <  v
//	 0 if u == v
//	+1 if u >  v
func (u Uint128) Cmp64(v uint64) int {
	if u.Hi == 0 && u.Lo == v {
		return 0
	} else if u.Hi == 0 && u.Lo < v {
		return -1
	} else {
		return 1
	}
}

// And returns u&v.
func (u Uint128) And(v Uint128) Uint128 {
	return Uint128{u.Lo & v.Lo, u.Hi & v.Hi}
}

// And64 returns u&v.
func (u Uint128) And64(v uint64) Uint128 {
	return Uint128{u.Lo & v, u.Hi & 0}
}

// Or returns u|v.
func (u Uint128) Or(v Uint128) Uint128 {
	return Uint128{u.Lo | v.Lo, u.Hi | v.Hi}
}

// Or64 returns u|v.
func (u Uint128) Or64(v uint64) Uint128 {
	return Uint128{u.Lo | v, u.Hi | 0}
}

// Xor returns u^v.
func (u Uint128) Xor(v Uint128) Uint128 {
	return Uint128{u.Lo ^ v.Lo, u.Hi ^ v.Hi}
}

// Xor64 returns u^v.
func (u Uint128) Xor64(v uint64) Uint128 {
	return Uint128{u.Lo ^ v, u.Hi ^ 0}
}

// Add returns u+v.
func (u Uint128) Add(v Uint128) Uint128 {
	lo, carry := bits.Add64(u.Lo, v.Lo, 0)
	hi, carry := bits.Add64(u.Hi, v.Hi, carry)
	if carry != 0 {
		panic("overflow")
	}
	return Uint128{lo, hi}
}

// AddWrap returns u+v with wraparound semantics; for example,
// Max.AddWrap(FromInt(1)) == Zero.
func (u Uint128) AddWrap(v Uint128) Uint128 {
	lo, carry := bits.Add64(u.Lo, v.Lo, 0)
	hi, _ := bits.Add64(u.Hi, v.Hi, carry)
	return Uint128{lo, hi}
}

// Add64 returns u+v.
func (u Uint128) Add64(v uint64) Uint128 {
	lo, carry := bits.Add64(u.Lo, v, 0)
	hi, carry := bits.Add64(u.Hi, 0, carry)
	if carry != 0 {
		panic("overflow")
	}
	return Uint128{lo, hi}
}

// AddWrap64 returns u+v with wraparound semantics; for example,
// Max.AddWrap64(1) == Zero.
func (u Uint128) AddWrap64(v uint64) Uint128 {
	lo, carry := bits.Add64(u.Lo, v, 0)
	hi := u.Hi + carry
	return Uint128{lo, hi}
}

// Sub returns u-v.
func (u Uint128) Sub(v Uint128) Uint128 {
	lo, borrow := bits.Sub64(u.Lo, v.Lo, 0)
	hi, borrow := bits.Sub64(u.Hi, v.Hi, borrow)
	if borrow != 0 {
		panic("overflow")
	}
	return Uint128{lo, hi}
}

// SubWrap returns u-v with wraparound semantics; for example,
// Zero.SubWrap(FromInt(1)) == Max.
func (u Uint128) SubWrap(v Uint128) Uint128 {
	lo, borrow := bits.Sub64(u.Lo, v.Lo, 0)
	hi, _ := bits.Sub64(u.Hi, v.Hi, borrow)
	return Uint128{lo, hi}
}

// Sub64 returns u-v.
func (u Uint128) Sub64(v uint64) Uint128 {
	lo, borrow := bits.Sub64(u.Lo, v, 0)
	hi, borrow := bits.Sub64(u.Hi, 0, borrow)
	if borrow != 0 {
		panic("oveflow")
	}
	return Uint128{lo, hi}
}

// SubWrap64 returns u-v with wraparound semantics; for example,
// Zero.SubWrap64(1) == Max.
func (u Uint128) SubWrap64(v uint64) Uint128 {
	lo, borrow := bits.Sub64(u.Lo, v, 0)
	hi := u.Hi - borrow
	return Uint128{lo, hi}
}

// Mul returns u*v, panicking on overflow.
func (u Uint128) Mul(v Uint128) Uint128 {
	hi, lo := bits.Mul64(u.Lo, v.Lo)
	p0, p1 := bits.Mul64(u.Hi, v.Lo)
	p2, p3 := bits.Mul64(u.Lo, v.Hi)
	hi, c0 := bits.Add64(hi, p1, 0)
	hi, c1 := bits.Add64(hi, p3, c0)
	if (u.Hi != 0 && v.Hi != 0) || p0 != 0 || p2 != 0 || c1 != 0 {
		panic("overflow")
	}
	return Uint128{lo, hi}
}

// MulWrap returns u*v with wraparound semantics; for example,
// Max.MulWrap(Max) == 1.
func (u Uint128) MulWrap(v Uint128) Uint128 {
	hi, lo := bits.Mul64(u.Lo, v.Lo)
	hi += u.Hi*v.Lo + u.Lo*v.Hi
	return Uint128{lo, hi}
}

// Mul64 returns u*v, panicking on overflow.
func (u Uint128) Mul64(v uint64) Uint128 {
	hi, lo := bits.Mul64(u.Lo, v)
	p0, p1 := bits.Mul64(u.Hi, v)
	hi, c0 := bits.Add64(hi, p1, 0)
	if p0 != 0 || c0 != 0 {
		panic("overflow")
	}
	return Uint128{lo, hi}
}

// MulWrap64 returns u*v with wraparound semantics; for example,
// Max.MulWrap64(2) == Max.Sub64(1).
func (u Uint128) MulWrap64(v uint64) Uint128 {
	hi, lo := bits.Mul64(u.Lo, v)
	hi += u.Hi * v
	return Uint128{lo, hi}
}

// DivRound returns u/v, rounded using the remainder.
func (u Uint128) DivRound(v Uint128) Uint128 {
	q, r := u.QuoRem(v)
	if r.Cmp(v.Rsh(1)) >= 1 {
		return q.Add64(1)
	}
	return q
}

// Div returns u/v.
func (u Uint128) Div(v Uint128) Uint128 {
	q, _ := u.QuoRem(v)
	return q
}

// Div64 returns u/v.
func (u Uint128) Div64(v uint64) Uint128 {
	q, _ := u.QuoRem64(v)
	return q
}

// QuoRem returns q = u/v and r = u%v.
func (u Uint128) QuoRem(v Uint128) (q, r Uint128) {
	if v.Hi == 0 {
		var r64 uint64
		q, r64 = u.QuoRem64(v.Lo)
		r = FromInt(r64)
	} else {
		// generate a "trial quotient," guaranteed to be within 1 of the actual
		// quotient, then adjust.
		n := uint(bits.LeadingZeros64(v.Hi))
		v1 := v.Lsh(n)
		u1 := u.Rsh(1)
		tq, _ := bits.Div64(u1.Hi, u1.Lo, v1.Hi)
		tq >>= 63 - n
		if tq != 0 {
			tq--
		}
		q = FromInt(tq)
		// calculate remainder using trial quotient, then adjust if remainder is
		// greater than divisor
		r = u.Sub(v.Mul64(tq))
		if r.Cmp(v) >= 0 {
			q = q.Add64(1)
			r = r.Sub(v)
		}
	}
	return
}

// QuoRem64 returns q = u/v and r = u%v.
func (u Uint128) QuoRem64(v uint64) (q Uint128, r uint64) {
	if u.Hi < v {
		q.Lo, r = bits.Div64(u.Hi, u.Lo, v)
	} else {
		q.Hi, r = bits.Div64(0, u.Hi, v)
		q.Lo, r = bits.Div64(r, u.Lo, v)
	}
	return
}

// Mod returns r = u%v.
func (u Uint128) Mod(v Uint128) (r Uint128) {
	_, r = u.QuoRem(v)
	return
}

// Mod64 returns r = u%v.
func (u Uint128) Mod64(v uint64) (r uint64) {
	_, r = u.QuoRem64(v)
	return
}

// Lsh returns u<<n.
func (u Uint128) Lsh(n uint) (s Uint128) {
	if n > 64 {
		s.Lo = 0
		s.Hi = u.Lo << (n - 64)
	} else {
		s.Lo = u.Lo << n
		s.Hi = u.Hi<<n | u.Lo>>(64-n)
	}
	return
}

// Rsh returns u>>n.
func (u Uint128) Rsh(n uint) (s Uint128) {
	if n > 64 {
		s.Lo = u.Hi >> (n - 64)
		s.Hi = 0
	} else {
		s.Lo = u.Lo>>n | u.Hi<<(64-n)
		s.Hi = u.Hi >> n
	}
	return
}

// LeadingZeros returns the number of leading zero bits in u; the result is 128
// for u == 0.
func (u Uint128) LeadingZeros() int {
	if u.Hi > 0 {
		return bits.LeadingZeros64(u.Hi)
	}
	return 64 + bits.LeadingZeros64(u.Lo)
}

// TrailingZeros returns the number of trailing zero bits in u; the result is
// 128 for u == 0.
func (u Uint128) TrailingZeros() int {
	if u.Lo > 0 {
		return bits.TrailingZeros64(u.Lo)
	}
	return 64 + bits.TrailingZeros64(u.Hi)
}

// OnesCount returns the number of one bits ("population count") in u.
func (u Uint128) OnesCount() int {
	return bits.OnesCount64(u.Hi) + bits.OnesCount64(u.Lo)
}

// RotateLeft returns the value of u rotated left by (k mod 128) bits.
func (u Uint128) RotateLeft(k int) Uint128 {
	const n = 128
	s := uint(k) & (n - 1)
	return u.Lsh(s).Or(u.Rsh(n - s))
}

// RotateRight returns the value of u rotated left by (k mod 128) bits.
func (u Uint128) RotateRight(k int) Uint128 {
	return u.RotateLeft(-k)
}

// Reverse returns the value of u with its bits in reversed order.
func (u Uint128) Reverse() Uint128 {
	return Uint128{bits.Reverse64(u.Hi), bits.Reverse64(u.Lo)}
}

// ReverseBytes returns the value of u with its bytes in reversed order.
func (u Uint128) ReverseBytes() Uint128 {
	return Uint128{bits.ReverseBytes64(u.Hi), bits.ReverseBytes64(u.Lo)}
}

// Len returns the minimum number of bits required to represent u; the result is
// 0 for u == 0.
func (u Uint128) Len() int {
	return 128 - u.LeadingZeros()
}

// String returns the base-10 representation of u as a string.
func (u Uint128) String() string {
	if u.IsZero() {
		return "0"
	}
	buf := []byte("0000000000000000000000000000000000000000") // log10(2^128) < 40
	for i := len(buf); ; i -= 19 {
		q, r := u.QuoRem64(1e19) // largest power of 10 that fits in a uint64
		var n int
		for ; r != 0; r /= 10 {
			n++
			buf[i-n] += byte(r % 10)
		}
		if q.IsZero() {
			return string(buf[i-n:])
		}
		u = q
	}
}

// Bytes returns the bytes encoded in Little Endian.
func (u Uint128) Bytes() []byte {
	b, _ := u.MarshalBinary()
	return b
}

// BytesBE returns the bytes encoded in Big Endian.
func (u Uint128) BytesBE() (b []byte) {
	b = make([]byte, 16)
	binary.BigEndian.PutUint64(b[:8], u.Hi)
	binary.BigEndian.PutUint64(b[8:], u.Lo)
	return
}

// Big returns u as a *big.Int.
func (u Uint128) Big() *big.Int {
	i := new(big.Int).SetUint64(u.Hi)
	i = i.Lsh(i, 64)
	i = i.Xor(i, new(big.Int).SetUint64(u.Lo))
	return i
}

// MarshalText implements encoding.TextMarshaler.
func (u Uint128) MarshalText() ([]byte, error) {
	return []byte(u.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (u *Uint128) UnmarshalText(b []byte) error {
	v, err := FromString(string(b))
	if err != nil {
		return err
	}
	*u = v
	return nil
}

// MarshalBinary implements encoding.BinaryMarshaler
func (u Uint128) MarshalBinary() ([]byte, error) {
	b := make([]byte, 16)
	binary.LittleEndian.PutUint64(b[:8], u.Lo)
	binary.LittleEndian.PutUint64(b[8:], u.Hi)
	return b, nil
}

// UnmarshalBinary implements encoding.BinaryUnmarshaler
func (u *Uint128) UnmarshalBinary(b []byte) error {
	if len(b) != 16 {
		return errors.New("byte slice must be of length 16")
	}
	u.Lo = binary.LittleEndian.Uint64(b[:8])
	u.Hi = binary.LittleEndian.Uint64(b[8:])
	return nil
}

// Scan implements sql.Scanner. It supports reading []byte of length 16 or strings of any length < 40
func (u *Uint128) Scan(src interface{}) error {
	switch src := src.(type) {
	case nil:
		return nil
	case string:
		if src == "" {
			return nil
		}
		v, err := FromString(src)
		if err != nil {
			return err
		}
		*u = v
	case []byte:
		if len(src) == 0 {
			return nil
		}
		*u, _ = FromBytes([]byte(src))
	default:
		return fmt.Errorf("Scan: unable to scan type %T into Uint128: ", src)
	}
	return nil
}

// New returns the Uint128 value (lo,hi).
func New(lo, hi uint64) Uint128 {
	return Uint128{lo, hi}
}

// FromInt converts v to a Uint128 value.
func FromInt(v uint64) Uint128 {
	return Uint128{v, 0}
}

// FromBytes converts b to a Uint128 value.
func FromBytes(b []byte) (u Uint128, err error) {
	err = u.UnmarshalBinary(b)
	return u, err
}

// FromBytesBE converts big-endian b to a Uint128 value.
func FromBytesBE(b []byte) (Uint128, error) {
	if len(b) != 16 {
		return Uint128{}, errors.New("byte slice must be of length 16")
	}
	return Uint128{
		binary.BigEndian.Uint64(b[8:]),
		binary.BigEndian.Uint64(b[:8]),
	}, nil
}

// FromBig converts i to a Uint128 value.
func FromBig(i *big.Int) (Uint128, error) {
	if i.Sign() < 0 {
		return Uint128{}, errors.New("value can not be negative")
	} else if i.BitLen() > 128 {
		return Uint128{}, errors.New("value overflows Uint128")
	}
	return Uint128{i.Uint64(), i.Rsh(i, 64).Uint64()}, nil
}

// FromString converts string s into a Uint128 value
func FromString(s string) (u Uint128, err error) {
	i := new(big.Int)
	// Parse the string as a big.Int.
	if _, ok := i.SetString(s, 10); !ok {
		return u, errors.New("invalid number format")
	}
	// Check if the number is negative.
	if i.Sign() < 0 {
		return u, errors.New("value cannot be negative")
	}
	// Check if the number overflows 128 bits.
	if i.BitLen() > 128 {
		return u, errors.New("value overflows Uint128")
	}
	// Extract the lower 64 bits.
	u.Lo = i.Uint64()
	// Right shift by 64 bits and extract the higher 64 bits.
	u.Hi = i.Rsh(i, 64).Uint64()
	return u, nil
}
