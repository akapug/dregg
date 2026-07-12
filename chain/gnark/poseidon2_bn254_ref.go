// Native-Go reference twin for the width-3 BN254 Poseidon2 permutation.
//
// It runs the identical schedule as the circuit gadget (poseidon2_bn254.go)
// but in plain fr.Element arithmetic (the BN254 scalar field), so the two are
// independent implementations that must agree, and it is checked against the
// HorizenLabs zkhash gold vector in the tests.
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

func frFromHex(s string) fr.Element {
	n, ok := new(big.Int).SetString(s, 0)
	if !ok {
		panic("poseidon2 bn254 ref: bad constant " + s)
	}
	var e fr.Element
	e.SetBigInt(n)
	return e
}

// bn254RefSbox: x^5.
func bn254RefSbox(x fr.Element) fr.Element {
	var x2, x4, x5 fr.Element
	x2.Mul(&x, &x)
	x4.Mul(&x2, &x2)
	x5.Mul(&x4, &x)
	return x5
}

func bn254RefExtLinear(s *[bn254P3Width]fr.Element) {
	var sum fr.Element
	sum.Add(&s[0], &s[1])
	sum.Add(&sum, &s[2])
	s[0].Add(&s[0], &sum)
	s[1].Add(&s[1], &sum)
	s[2].Add(&s[2], &sum)
}

func bn254RefIntLinear(s *[bn254P3Width]fr.Element) {
	var sum fr.Element
	sum.Add(&s[0], &s[1])
	sum.Add(&sum, &s[2])
	s[0].Add(&s[0], &sum)
	s[1].Add(&s[1], &sum)
	// s2 = 2*s2 + sum
	s[2].Double(&s[2])
	s[2].Add(&s[2], &sum)
}

// poseidon2Bn254Ref applies the permutation in place over fr.Element.
func poseidon2Bn254Ref(state *[bn254P3Width]fr.Element) {
	// Parse constants into fr.Element (cheap; done per call for clarity).
	var extInit, extTerm [bn254P3HalfFull][bn254P3Width]fr.Element
	var intC [bn254P3Partial]fr.Element
	for r := 0; r < bn254P3HalfFull; r++ {
		for i := 0; i < bn254P3Width; i++ {
			extInit[r][i] = frFromHex(rc3ExtInitial[r][i])
			extTerm[r][i] = frFromHex(rc3ExtTerminal[r][i])
		}
	}
	for r := 0; r < bn254P3Partial; r++ {
		intC[r] = frFromHex(rc3Internal[r])
	}

	bn254RefExtLinear(state)

	for r := 0; r < bn254P3HalfFull; r++ {
		for i := 0; i < bn254P3Width; i++ {
			state[i].Add(&state[i], &extInit[r][i])
		}
		for i := 0; i < bn254P3Width; i++ {
			state[i] = bn254RefSbox(state[i])
		}
		bn254RefExtLinear(state)
	}

	for r := 0; r < bn254P3Partial; r++ {
		state[0].Add(&state[0], &intC[r])
		state[0] = bn254RefSbox(state[0])
		bn254RefIntLinear(state)
	}

	for r := 0; r < bn254P3HalfFull; r++ {
		for i := 0; i < bn254P3Width; i++ {
			state[i].Add(&state[i], &extTerm[r][i])
		}
		for i := 0; i < bn254P3Width; i++ {
			state[i] = bn254RefSbox(state[i])
		}
		bn254RefExtLinear(state)
	}
}

// poseidon2Bn254RefCompress mirrors Poseidon2Bn254Compress in the reference.
func poseidon2Bn254RefCompress(left, right fr.Element) fr.Element {
	var zero fr.Element
	state := [bn254P3Width]fr.Element{left, right, zero}
	poseidon2Bn254Ref(&state)
	return state[0]
}
