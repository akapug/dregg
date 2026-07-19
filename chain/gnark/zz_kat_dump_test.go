package friverifier

import (
	"fmt"
	"testing"
)

func TestDumpRound1KAT(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	rounds := []OpenInputRoundShape{}
	for _, r := range fx.InputRounds {
		var ms []OpenInputMatrixShape
		for _, m := range r.Matrices {
			ms = append(ms, OpenInputMatrixShape{m.LogHeight, m.Width, m.NumPoints, m.NextPointBits})
		}
		rounds = append(rounds, OpenInputRoundShape{ms})
	}
	ri := 1
	round := rounds[ri]
	groups := openInputHeightGroupsOf(round)
	fmt.Printf("ROUND %d maxLh=%d index=%d logMax=%d\n", ri, groups[0].logHeight, fx.Queries[0].ExpectedIndex, fx.Fri.LogGlobalMaxHeight)
	for gi, g := range groups {
		fmt.Printf("  group %d height=%d mats=%v\n", gi, g.logHeight, g.mats)
	}
	op := shrinkInputOpeningsRef(t, fx, 0)[ri]
	// group concatenations
	for gi, g := range groups {
		var limbs []uint32
		for _, mi := range g.mats {
			limbs = append(limbs, op.rows[mi]...)
		}
		fmt.Printf("  G%d limbs (%d): %v\n", gi, len(limbs), limbs)
	}
	fmt.Printf("  path (%d):\n", len(op.path))
	for _, p := range op.path {
		fmt.Printf("    0x%s\n", p.Text(16))
	}
	root, err := openInputBatchRootRef(round, op, fx.Queries[0].ExpectedIndex, fx.Fri.LogGlobalMaxHeight)
	if err != nil { t.Fatal(err) }
	fmt.Printf("  COMPUTED ROOT: 0x%s\n", root.Text(16))
}
