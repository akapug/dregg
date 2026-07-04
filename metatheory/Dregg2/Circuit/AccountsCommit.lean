/-
# Dregg2.Circuit.AccountsCommit — the `accounts` growth carrier (sorted-`Finset` list digest).

`createCellA` / `spawnA` grow `accounts : Finset CellId`. The honest commitment is the Poseidon
list-sponge over the canonical sorted account index (`k.accounts.sort (· ≤ ·)`), reusing
`ListCommit.listDigest` + `ListDigestBindsList`. The `accountsComponent` smart constructor is the
`ActiveComponent` shape for account-growth effects paired with other touched fields.

ADDITIVE: imports `EffectCommit2` (reuses `ActiveComponent`); edits none of the keystones.
-/
import Dregg2.Circuit.EffectCommit2

namespace Dregg2.Circuit.AccountsCommit

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Exec

set_option linter.dupNamespace false

/-- Canonical sorted account index (the list the digest sponges). -/
def accountsSorted (k : RecordKernelState) : List CellId :=
  k.accounts.sort (· ≤ ·)

/-- Equal sorted account lists force equal `accounts` Finsets. -/
theorem accounts_eq_of_sorted_eq (s t : Finset CellId)
    (h : s.sort (· ≤ ·) = t.sort (· ≤ ·)) : s = t := by
  have h' := congr_arg List.toFinset h
  rwa [Finset.sort_toFinset, Finset.sort_toFinset] at h'

theorem accountsSorted_eq_of_eq (s t : Finset CellId) (h : s = t) :
    s.sort (· ≤ ·) = t.sort (· ≤ ·) := by rw [h]

/-- **`accountsComponent`** — an `ActiveComponent` for `accounts` growth: digest is the sorted-list
sponge; `postClause` is FULL `Finset` equality (a drop/reorder of an existing id is REJECTED). -/
def accountsComponent {St Args : Type} (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (expectedAccounts : St → Args → Finset CellId) : ActiveComponent St Args where
  digest    := fun k => listDigest LE cN (accountsSorted k)
  expected  := fun pre args => listDigest LE cN ((expectedAccounts pre args).sort (· ≤ ·))
  postClause := fun pre args post => post.accounts = expectedAccounts pre args
  binds     := fun pre args post h =>
    accounts_eq_of_sorted_eq _ _ (ListDigestBindsList LE cN hN hLE _ _ h)
  encodes   := fun pre args post h =>
    listDigest_congr LE cN (accountsSorted_eq_of_eq _ _ h)

#assert_axioms accounts_eq_of_sorted_eq

end Dregg2.Circuit.AccountsCommit