import Dregg2.Games.Automatafl

namespace Dregg2.Games.Automatafl.Audit
open Dregg2.Games.Automatafl

/-! ### D1. Destination held by a NON-MOVING piece: the piece is DESTROYED.
Rules step 3: "only if no other piece (which is not in the process of being moved) is on the
straight-line path between the source and the destination (otherwise, the piece is replaced at
its original position)"; author: "designating a move to an occupied square ... just fails to
execute".  ONE move, deployed arity. -/
def d1Board : Board := mkBoard 3 [(⟨0,0⟩, .attractor), (⟨0,2⟩, .repulsor)] ⟨2,2⟩
def d1Move : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨0,2⟩ }

#guard moveValidB d1Board d1Move = true
#guard occluded d1Board [d1Move.frm] d1Move = false          -- interior is EXCLUSIVE of the dest
#guard d1Board.cellAt ⟨0,2⟩ = Particle.repulsor
-- the mover lands on the occupied square; the repulsor is gone from the whole board
#guard (applyMoves d1Board [d1Move]).cellAt ⟨0,2⟩ = Particle.attractor
#guard (applyMoves d1Board [d1Move]).cellAt ⟨0,0⟩ = Particle.vacuum
#guard ((List.range 3).all (fun x => (List.range 3).all (fun y =>
          (applyMoves d1Board [d1Move]).cellAt ⟨x,y⟩ != Particle.repulsor))) = true

/-! ### D2. 2-CYCLE with pieces on BOTH squares: our spec SWAPS them.
PHILOSOPHY.md / MERGE_RESOLUTION_DESIGN.md: "2-cycles (A→B, B→A) ALWAYS stay in place".
logic/src/game.rs Phase 3: `is_two_cycle` ⇒ `dest_coord = start_coord`. -/
def d2Board : Board := mkBoard 3 [(⟨0,0⟩, .attractor), (⟨0,2⟩, .repulsor)] ⟨2,2⟩
def d2A : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨0,2⟩ }
def d2B : Move := { who := 1, frm := ⟨0,2⟩, to := ⟨0,0⟩ }

#guard conflictResolve d2Board [d2A, d2B] = [d2A, d2B]   -- not a conflict
#guard (applyMoves d2Board [d2A, d2B]).cellAt ⟨0,2⟩ = Particle.attractor  -- SWAPPED
#guard (applyMoves d2Board [d2A, d2B]).cellAt ⟨0,0⟩ = Particle.repulsor   -- SWAPPED

/-! ### D3. 2-cycle whose far square is EMPTY: README erratum says the piece does NOT move.
"Cycles are permissible, including a move from an empty square directly back to some source
square--the piece simply doesn't move in this case."  Rust: 2-cycle ⇒ stay. -/
def d3Board : Board := mkBoard 3 [(⟨0,0⟩, .attractor)] ⟨2,2⟩
def d3A : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨0,2⟩ }
def d3B : Move := { who := 1, frm := ⟨0,2⟩, to := ⟨0,0⟩ }   -- source is VACUUM

#guard conflictResolve d3Board [d3A, d3B] = [d3A, d3B]
#guard (applyMoves d3Board [d3A, d3B]).cellAt ⟨0,2⟩ = Particle.attractor  -- it DID move
#guard (applyMoves d3Board [d3A, d3B]).cellAt ⟨0,0⟩ = Particle.vacuum

/-! ### D4. A conflicted coordinate is NOT made illegal for the other players' moves.
Rules: "It is illegal to specify as a source or destination the *exact* coordinate which was
conflicted upon (that is, in a source conflict, that source piece becomes immovable by all; in a
destination conflict, that destination square can no longer be moved to by anyone)". -/
-- (a) destination conflict at (2,0); a third move USES (2,0) as its source.
def d4Board : Board :=
  mkBoard 5 [(⟨0,0⟩, .attractor), (⟨4,0⟩, .attractor), (⟨2,0⟩, .repulsor)] ⟨4,4⟩
def d4A : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨2,0⟩ }
def d4B : Move := { who := 1, frm := ⟨4,0⟩, to := ⟨2,0⟩ }
def d4C : Move := { who := 2, frm := ⟨2,0⟩, to := ⟨2,4⟩ }

#guard conflictResolve d4Board [d4A, d4B, d4C] = [d4C]     -- C SURVIVES; Rust invalidates it
#guard (applyMoves d4Board (conflictResolve d4Board [d4A, d4B, d4C])).cellAt ⟨2,4⟩
        = Particle.repulsor                                 -- and it EXECUTES

-- (b) source (fork) conflict at (0,0); a third move TARGETS (0,0).
def d5Board : Board :=
  mkBoard 5 [(⟨0,0⟩, .attractor), (⟨0,4⟩, .repulsor)] ⟨4,4⟩
def d5A : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨0,2⟩ }
def d5B : Move := { who := 1, frm := ⟨0,0⟩, to := ⟨2,0⟩ }
def d5C : Move := { who := 2, frm := ⟨0,4⟩, to := ⟨0,0⟩ }

#guard conflictResolve d5Board [d5A, d5B, d5C] = [d5C]     -- C SURVIVES; Rust invalidates it

/-! ### D5. FAIRNESS IS FALSE, and a piece is destroyed at a vacuum merge.
Two chains converge on (2,0) through vacuum waypoints; neither destination-conflict fires
(both waypoint sources are vacuum).  `journeys.find?` awards (2,0) to whichever journey is
FIRST IN MOVE-LIST ORDER — so permuting the move list changes the board.  This REFUTES
`FairnessObligation` (PHILOSOPHY.md "Principle of Fairness"). -/
def d6Board : Board := mkBoard 5 [(⟨0,0⟩, .attractor), (⟨4,0⟩, .repulsor)] ⟨4,4⟩
def m1 : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨1,0⟩ }
def m2 : Move := { who := 1, frm := ⟨1,0⟩, to := ⟨2,0⟩ }   -- vacuum source
def m3 : Move := { who := 2, frm := ⟨4,0⟩, to := ⟨3,0⟩ }
def m4 : Move := { who := 3, frm := ⟨3,0⟩, to := ⟨2,0⟩ }   -- vacuum source

#guard conflictResolve d6Board [m1,m2,m3,m4] = [m1,m2,m3,m4]      -- NO conflict fires
#guard (applyMoves d6Board [m1,m2,m3,m4]).cellAt ⟨2,0⟩ = Particle.attractor
#guard (applyMoves d6Board [m3,m4,m1,m2]).cellAt ⟨2,0⟩ = Particle.repulsor
-- permutation changes the board ⇒ FairnessObligation is FALSE
#guard ((List.range 5).all (fun x => (List.range 5).all (fun y =>
          (applyMoves d6Board [m1,m2,m3,m4]).cellAt ⟨x,y⟩ != Particle.repulsor))) = true

/-! ### D6. 3-CYCLE through a vacuum square: our chain lands the piece INSIDE the cycle.
MOVE_EXPLAIN.md: "A piece moved into a cycle of squares that were all empty at the start of the
turn will not enter the cycle. The move is nullified". -/
def d7Board : Board := mkBoard 5 [(⟨0,0⟩, .attractor)] ⟨4,4⟩
def e1 : Move := { who := 0, frm := ⟨0,0⟩, to := ⟨0,1⟩ }   -- piece into the empty cycle
def e2 : Move := { who := 1, frm := ⟨0,1⟩, to := ⟨0,2⟩ }   -- empty
def e3 : Move := { who := 2, frm := ⟨0,2⟩, to := ⟨0,1⟩ }   -- empty, back: empty 2-cycle

#guard conflictResolve d7Board [e1,e2,e3] = [e1,e2,e3]
#guard (applyMoves d7Board [e1,e2,e3]).cellAt ⟨0,0⟩ = Particle.vacuum   -- it LEFT
#guard (applyMoves d7Board [e1,e2,e3]).cellAt ⟨0,2⟩ = Particle.attractor -- entered the empty cycle

end Dregg2.Games.Automatafl.Audit
