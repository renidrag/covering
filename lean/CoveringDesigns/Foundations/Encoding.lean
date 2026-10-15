import CoveringDesigns.Foundations.Relabelling
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Init.Data.BitVec.Lemmas

/-! The bridge between finite subsets and bit vectors is proved explicitly. -/

namespace CoveringDesigns

open Finset

def bitsOfFunction {n : ℕ} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

@[simp] theorem bitsOfFunction_get {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (bitsOfFunction f).getLsbD i.val = f i := by
  rw [bitsOfFunction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, i.isLt]

def decode {n : ℕ} (x : BitVec n) : Finset (Fin n) :=
  univ.filter (fun i => x.getLsbD i.val)

def encode {n : ℕ} (S : Finset (Fin n)) : BitVec n :=
  bitsOfFunction (fun i => decide (i ∈ S))

@[simp] theorem mem_decode {n : ℕ} (x : BitVec n) (i : Fin n) :
    i ∈ decode x ↔ x.getLsbD i.val = true := by
  simp [decode]

@[simp] theorem decode_encode {n : ℕ} (S : Finset (Fin n)) : decode (encode S) = S := by
  ext i
  simp only [mem_decode, encode, bitsOfFunction_get, decide_eq_true_eq]

@[simp] theorem encode_decode {n : ℕ} (x : BitVec n) : encode (decode x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (bitsOfFunction (fun i : Fin n => decide (i ∈ decode x))).getLsbD
    (⟨i, hi⟩ : Fin n).val = x.getLsbD i
  rw [bitsOfFunction_get]
  simp [mem_decode]

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro S T h
  simpa using congrArg decode h

theorem decode_injective {n : ℕ} : Function.Injective (@decode n) := by
  intro x y h
  simpa using congrArg encode h

def subsetBitsEquiv (n : ℕ) : Finset (Fin n) ≃ BitVec n where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

def countBits4 : List Bool → BitVec 4
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countBits4 bs

theorem countBits4_toNat (bs : List Bool) (h : bs.length < 16) :
    (countBits4 bs).toNat = bs.count true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hbs : bs.length < 16 := by simpa using Nat.lt_of_succ_lt h
    have hc := List.count_le_length (a := true) (l := bs)
    specialize ih hbs
    have hcount : 1 + bs.count true < 16 := by simp only [List.length_cons] at h; omega
    cases b
    · simpa [countBits4] using ih
    · simp [countBits4, BitVec.toNat_add, ih, Nat.add_comm]
      omega

theorem count_ofFn_eq_sum {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true = ∑ i, if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.sum_univ_succ]
    cases f 0 <;> simp [Nat.add_comm]

theorem countBits4_card {n : ℕ} (f : Fin n → Bool) (hn : n < 16) :
    (countBits4 (List.ofFn f)).toNat = (univ.filter (fun i => f i)).card := by
  rw [countBits4_toNat _ (by simpa), count_ofFn_eq_sum]
  simp only [card_eq_sum_ones, sum_filter]

theorem countBits4_decode {n : ℕ} (x : BitVec n) (hn : n < 16) :
    (countBits4 (List.ofFn (fun i : Fin n => x.getLsbD i.val))).toNat = (decode x).card :=
  countBits4_card _ hn

theorem decode_and {n : ℕ} (x y : BitVec n) : decode (x &&& y) = decode x ∩ decode y := by
  ext q
  simp only [mem_decode, BitVec.getLsbD_and, Bool.and_eq_true, mem_inter]

theorem encode_and_eq_right_iff {n : ℕ} (S T : Finset (Fin n)) :
    encode S &&& encode T = encode T ↔ T ⊆ S := by
  constructor
  · intro h
    have hh := congrArg decode h
    rw [decode_and, decode_encode, decode_encode] at hh
    exact inter_eq_right.mp hh
  · intro h
    apply decode_injective
    rw [decode_and, decode_encode, decode_encode, inter_eq_right.mpr h]

end CoveringDesigns
