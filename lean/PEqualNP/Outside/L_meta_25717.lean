import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25716

namespace PEqualNP.Outside.L_meta_25717

private theorem pnp25717Row (k : ℕ) (p : ZMod k) (z : ZMod k → ZMod 2)
    (h : ∀ t : ℕ, t < 3 →
      PEqualNP.Outside.L_meta_25716_aux.mix k 1 (PEqualNP.Outside.L_meta_25716_aux.rot k 1 z) (p + t) =
        PEqualNP.Outside.L_meta_25716_aux.rot k 0 z (p + t) ∧
      PEqualNP.Outside.L_meta_25716_aux.mix k 1 (PEqualNP.Outside.L_meta_25716_aux.rot k 1 z) (p + t + 1) = 0 ∧
      PEqualNP.Outside.L_meta_25716_aux.mix k 1 (PEqualNP.Outside.L_meta_25716_aux.rot k 1 z) (p + t + 2) = 0) :
    ∀ t : ℕ, t < 7 → z (p - 2 + t) = 0 := by
  have h0 := h 0 (by decide)
  have e0 : z (p - 2 + 0) + z (p - 2 + 1) + z (p - 2 + 2) = z (p - 2 + 2) := by
    have e := h0.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have h1 := h 1 (by decide)
  have e1 : z (p - 2 + 1) + z (p - 2 + 2) + z (p - 2 + 3) = z (p - 2 + 3) := by
    have e := h1.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have h2 := h 2 (by decide)
  have e2 : z (p - 2 + 2) + z (p - 2 + 3) + z (p - 2 + 4) = z (p - 2 + 4) := by
    have e := h2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f1 : z (p - 2 + 1) + z (p - 2 + 2) + z (p - 2 + 3) = 0 := by
    have e := h0.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f2 : z (p - 2 + 2) + z (p - 2 + 3) + z (p - 2 + 4) = 0 := by
    have e := h1.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f3 : z (p - 2 + 3) + z (p - 2 + 4) + z (p - 2 + 5) = 0 := by
    have e := h2.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f4 : z (p - 2 + 4) + z (p - 2 + 5) + z (p - 2 + 6) = 0 := by
    have e := h2.2.2
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  intro t ht
  interval_cases t
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e0 + e2 + f1
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e2 + f1
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + e2 + f1
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + f1
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e2 + f2
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + e2 + f1 + f2 + f3
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + f1 + f3 + f4

private theorem pnp25717Col (k : ℕ) (p : ZMod k) (z : ZMod k → ZMod 2)
    (h : ∀ t : ℕ, t < 5 →
      PEqualNP.Outside.L_meta_25716_aux.mix k 2 (PEqualNP.Outside.L_meta_25716_aux.rot k 3 z) (p + t) =
        PEqualNP.Outside.L_meta_25716_aux.rot k 4 z (p + t) ∧
      PEqualNP.Outside.L_meta_25716_aux.mix k 2 (PEqualNP.Outside.L_meta_25716_aux.rot k 3 z) (p + t + 1) = 0 ∧
      PEqualNP.Outside.L_meta_25716_aux.mix k 2 (PEqualNP.Outside.L_meta_25716_aux.rot k 3 z) (p + t + 2) = 0) :
    ∀ t : ℕ, t < 11 → z (p - 5 + t) = 0 := by
  have h0 := h 0 (by decide)
  have e0 : z (p - 5 + 0) + z (p - 5 + 2) + z (p - 5 + 4) = z (p - 5 + 1) := by
    have e := h0.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have h1 := h 1 (by decide)
  have e1 : z (p - 5 + 1) + z (p - 5 + 3) + z (p - 5 + 5) = z (p - 5 + 2) := by
    have e := h1.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have h2 := h 2 (by decide)
  have e2 : z (p - 5 + 2) + z (p - 5 + 4) + z (p - 5 + 6) = z (p - 5 + 3) := by
    have e := h2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have h3 := h 3 (by decide)
  have e3 : z (p - 5 + 3) + z (p - 5 + 5) + z (p - 5 + 7) = z (p - 5 + 4) := by
    have e := h3.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have h4 := h 4 (by decide)
  have e4 : z (p - 5 + 4) + z (p - 5 + 6) + z (p - 5 + 8) = z (p - 5 + 5) := by
    have e := h4.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f1 : z (p - 5 + 1) + z (p - 5 + 3) + z (p - 5 + 5) = 0 := by
    have e := h0.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f2 : z (p - 5 + 2) + z (p - 5 + 4) + z (p - 5 + 6) = 0 := by
    have e := h1.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f3 : z (p - 5 + 3) + z (p - 5 + 5) + z (p - 5 + 7) = 0 := by
    have e := h2.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f4 : z (p - 5 + 4) + z (p - 5 + 6) + z (p - 5 + 8) = 0 := by
    have e := h3.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f5 : z (p - 5 + 5) + z (p - 5 + 7) + z (p - 5 + 9) = 0 := by
    have e := h4.2.1
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  have f6 : z (p - 5 + 6) + z (p - 5 + 8) + z (p - 5 + 10) = 0 := by
    have e := h4.2.2
    unfold PEqualNP.Outside.L_meta_25716_aux.mix PEqualNP.Outside.L_meta_25716_aux.rot at e
    norm_num at e
    ring_nf at e ⊢
    simpa using e
  intro t ht
  interval_cases t
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e0 + e1 + e2 + e3 + e4 + f2 + f3 + f4
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e2 + e4 + f1 + f2 + f4
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + f1
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e2 + f2
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e3 + f3
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e4 + f4
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + e3 + f1 + f2 + f3
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e2 + e4 + f2 + f3 + f4
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e1 + f1 + f2 + f4
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e2 + f2 + f3 + f5
  · norm_num
    linear_combination (norm := (ring_nf; norm_num [Int.rawCast, Nat.rawCast] <;> simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide])) e3 + f3 + f4 + f6

private theorem pnp25717Queries {I : Type} [Fintype I] {O : Type} [Nonempty O]
    {m : ℕ} (obs : Fin m → I → ZMod 2) (out : (I → ZMod 2) → O)
    (surj : Function.Surjective fun x => fun t => dotProduct (obs t) x)
    (period : ∀ z, (∀ x, out (x + z) = out x) ↔ ∀ t, dotProduct (obs t) z = 0)
    (q : ℕ) :
    (∃ (f : Fin q → I → ZMod 2) (g : (Fin q → ZMod 2) → O),
      ∀ x, g (fun t => dotProduct (f t) x) = out x) ↔ m ≤ q := by
  classical
  constructor
  · rintro ⟨f, g, hg⟩
    let chooseKey : (Fin m → ZMod 2) → (I → ZMod 2) := fun a => Classical.choose (surj a)
    have hc (a : Fin m → ZMod 2) : (fun t => dotProduct (obs t) (chooseKey a)) = a :=
      Classical.choose_spec (surj a)
    let code : (Fin m → ZMod 2) → (Fin q → ZMod 2) :=
      fun a t => dotProduct (f t) (chooseKey a)
    have hinj : Function.Injective code := by
      intro a b hab
      let z := chooseKey a - chooseKey b
      have hz (t : Fin q) : dotProduct (f t) z = 0 := by
        rw [show z = chooseKey a - chooseKey b from rfl, dotProduct_sub]
        exact sub_eq_zero.mpr (congrFun hab t)
      have hobs := (period z).mp (fun x => by
        rw [← hg (x + z), ← hg x]
        congr 1
        funext t
        rw [dotProduct_add, hz, add_zero])
      funext t
      rw [← congrFun (hc a) t, ← congrFun (hc b) t]
      apply sub_eq_zero.mp
      rw [← dotProduct_sub]
      exact hobs t
    have hcard := Fintype.card_le_of_injective code hinj
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  · intro hm
    let f : Fin q → I → ZMod 2 := fun t =>
      if ht : t.val < m then obs ⟨t.val, ht⟩ else 0
    let g : (Fin q → ZMod 2) → O := fun a =>
      out (Classical.choose (surj (fun t => a (Fin.castLE hm t))))
    refine ⟨f, g, ?_⟩
    intro x
    let a : Fin m → ZMod 2 := fun t => dotProduct (f (Fin.castLE hm t)) x
    let y : I → ZMod 2 := Classical.choose (surj a)
    have hy : (fun t => dotProduct (obs t) y) = a := Classical.choose_spec (surj a)
    have hz (t : Fin m) : dotProduct (obs t) (y - x) = 0 := by
      rw [dotProduct_sub, sub_eq_zero]
      simpa [a, f, t.isLt] using congrFun hy t
    change out y = out x
    have h := (period (y - x)).mpr hz x
    rwa [add_comm x (y - x), sub_add_cancel] at h

private def pnp25717Patch {k : ℕ} (starts : Finset (ZMod k)) (left len : ℕ) :
    Finset (ZMod k) :=
  starts.biUnion (fun p => (Finset.range len).image (fun t : ℕ => p - (left : ZMod k) + t))

private theorem pnp25717Mem {k : ℕ} {starts : Finset (ZMod k)} {left len : ℕ}
    {p : ZMod k} (hp : p ∈ starts) {t : ℕ} (ht : t < len) :
    p - (left : ZMod k) + t ∈ pnp25717Patch starts left len :=
  Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩⟩

set_option maxHeartbeats 1000000 in
private theorem pnp25717Normal (k : ℕ) [NeZero k] (hk : ¬ (k = 1 ∨ k = 3))
    (row col cr cc z : ZMod k → ZMod 2) (R C : Finset (ZMod k)) :
    ((∀ j ∈ pnp25717Patch R 0 3, ∀ x,
       PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr (x + z) j =
       PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr x j) ∧
     (∀ j ∈ pnp25717Patch C 0 5, ∀ x,
       PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc (x + z) j =
       PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc x j)) ↔
    ∀ i ∈ pnp25717Patch R 2 7 ∪ pnp25717Patch C 5 11, z i = 0 := by
  classical
  constructor
  · rintro ⟨hr, hc⟩ i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p, hp, ht⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨t, htRange, rfl⟩ := Finset.mem_image.mp ht
      apply pnp25717Row k p z _ t (Finset.mem_range.mp htRange)
      intro j hj
      have hm : p + (j : ZMod k) ∈ pnp25717Patch R 0 3 := by
        simpa using pnp25717Mem (left := 0) hp hj
      obtain ⟨e, h | h⟩ := (PEqualNP.Outside.L_meta_25716_aux.key k 1 1 0
        (Or.inl rfl) row cr z _).mp (hr _ hm)
      · exact (hk h).elim
      · exact ⟨e, h⟩
    · obtain ⟨p, hp, ht⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨t, htRange, rfl⟩ := Finset.mem_image.mp ht
      apply pnp25717Col k p z _ t (Finset.mem_range.mp htRange)
      intro j hj
      have hm : p + (j : ZMod k) ∈ pnp25717Patch C 0 5 := by
        simpa using pnp25717Mem (left := 0) hp hj
      obtain ⟨e, h | h⟩ := (PEqualNP.Outside.L_meta_25716_aux.key k 2 3 4
        (Or.inr rfl) col cc z _).mp (hc _ hm)
      · exact (hk h).elim
      · exact ⟨e, h⟩
  · intro hz
    constructor
    · intro j hj
      obtain ⟨p, hp, ht⟩ := Finset.mem_biUnion.mp hj
      obtain ⟨t, htRange, rfl⟩ := Finset.mem_image.mp ht
      have ht' := Finset.mem_range.mp htRange
      have h (a : ℕ) (ha : a < 7) : z (p - 2 + a) = 0 := by
        apply hz _ (Finset.mem_union_left _ _)
        simpa using pnp25717Mem (left := 2) hp ha
      apply (PEqualNP.Outside.L_meta_25716_aux.key k 1 1 0 (Or.inl rfl) row cr z _).mpr
      refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp only [PEqualNP.Outside.L_meta_25716_aux.mix, PEqualNP.Outside.L_meta_25716_aux.rot] <;>
        push_cast <;> norm_num
      · have h0 := h (t + 0) (by omega)
        push_cast at h0
        have h1 := h (t + 1) (by omega)
        push_cast at h1
        have h2 := h (t + 2) (by omega)
        push_cast at h2
        have h3 := h (t + 2) (by omega)
        push_cast at h3
        ring_nf at h0 h1 h2 h3 ⊢
        simp [h0, h1, h2, h3]
      · have h0 := h (t + 1) (by omega)
        push_cast at h0
        have h1 := h (t + 2) (by omega)
        push_cast at h1
        have h2 := h (t + 3) (by omega)
        push_cast at h2
        ring_nf at h0 h1 h2 ⊢
        simp [h0, h1, h2]
      · have h0 := h (t + 2) (by omega)
        push_cast at h0
        have h1 := h (t + 3) (by omega)
        push_cast at h1
        have h2 := h (t + 4) (by omega)
        push_cast at h2
        ring_nf at h0 h1 h2 ⊢
        simp [h0, h1, h2]
    · intro j hj
      obtain ⟨p, hp, ht⟩ := Finset.mem_biUnion.mp hj
      obtain ⟨t, htRange, rfl⟩ := Finset.mem_image.mp ht
      have ht' := Finset.mem_range.mp htRange
      have h (a : ℕ) (ha : a < 11) : z (p - 5 + a) = 0 := by
        apply hz _ (Finset.mem_union_right _ _)
        simpa using pnp25717Mem (left := 5) hp ha
      apply (PEqualNP.Outside.L_meta_25716_aux.key k 2 3 4 (Or.inr rfl) col cc z _).mpr
      refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp only [PEqualNP.Outside.L_meta_25716_aux.mix, PEqualNP.Outside.L_meta_25716_aux.rot] <;>
        push_cast <;> norm_num
      · have h0 := h (t + 0) (by omega)
        push_cast at h0
        have h1 := h (t + 2) (by omega)
        push_cast at h1
        have h2 := h (t + 4) (by omega)
        push_cast at h2
        have h3 := h (t + 1) (by omega)
        push_cast at h3
        ring_nf at h0 h1 h2 h3 ⊢
        simp [h0, h1, h2, h3]
      · have h0 := h (t + 1) (by omega)
        push_cast at h0
        have h1 := h (t + 3) (by omega)
        push_cast at h1
        have h2 := h (t + 5) (by omega)
        push_cast at h2
        ring_nf at h0 h1 h2 ⊢
        simp [h0, h1, h2]
      · have h0 := h (t + 2) (by omega)
        push_cast at h0
        have h1 := h (t + 4) (by omega)
        push_cast at h1
        have h2 := h (t + 6) (by omega)
        push_cast at h2
        ring_nf at h0 h1 h2 ⊢
        simp [h0, h1, h2]

end PEqualNP.Outside.L_meta_25717

open PEqualNP.Outside.L_meta_25717

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25717 : (∀ (k : ℕ) [NeZero k],
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let rot := fun (s : ℕ) (w : V) (i : I) => w (i-(s : I))
  let mix := fun (d : ℕ) (w : V) (i : I) => w (i-(d : I))+w i+w (i+(d : I))
  let out := fun (d u v : ℕ) (name c x : V) (j : I) =>
    let y := mix d (rot u x + name)
    y j + (1+y (j+1))*y (j+2) + rot v x j + c j
  let patch := fun (starts : Finset I) (left len : ℕ) =>
    starts.biUnion (fun p => (Finset.range len).image (fun t : ℕ => p-(left : I)+(t : I)))
  ∀ (row col cr cc : V) (R C : Finset I),
    let S := patch R 0 3
    let T := patch C 0 5
    let sites := patch R 2 7 ∪ patch C 5 11
    let need := if sites = ∅ ∨ k = 1 then 0 else if k = 3 then 2 else sites.card
    ∀ q : ℕ,
      (∃ (forms : Fin q → V) (decode : (Fin q → B) → V × V),
        ∀ key : V,
          let ans := decode (fun t => dotProduct (forms t) key)
          (∀ j ∈ S, ans.1 j = out 1 1 0 row cr key j) ∧
          (∀ i ∈ T, ans.2 i = out 2 3 4 col cc key i)) ↔ need ≤ q) := by
  classical
  intro k hk
  dsimp only
  intro row col cr cc R C q
  let S := pnp25717Patch R 0 3
  let T := pnp25717Patch C 0 5
  let sites := pnp25717Patch R 2 7 ∪ pnp25717Patch C 5 11
  let O := ((ZMod k → ZMod 2) × (ZMod k → ZMod 2))
  let mask (a : Finset (ZMod k)) (v : ZMod k → ZMod 2) (i : ZMod k) :=
    if i ∈ a then v i else 0
  let F (x : ZMod k → ZMod 2) : O :=
    (mask S (PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr x),
     mask T (PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc x))
  change (∃ f : Fin q → ZMod k → ZMod 2, ∃ g : (Fin q → ZMod 2) → O,
    ∀ x, (∀ j ∈ S, (g (fun t => dotProduct (f t) x)).1 j =
       PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr x j) ∧
      (∀ j ∈ T, (g (fun t => dotProduct (f t) x)).2 j =
       PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc x j)) ↔
    (if sites = ∅ ∨ k = 1 then 0 else if k = 3 then 2 else sites.card) ≤ q
  have eqmask (a : Finset (ZMod k)) (v w : ZMod k → ZMod 2) :
      mask a v = mask a w ↔ ∀ j ∈ a, v j = w j := by
    constructor
    · intro h j hj
      simpa [mask, hj] using congrFun h j
    · intro h
      funext j
      by_cases hj : j ∈ a
      · simp [mask, hj, h j hj]
      · simp [mask, hj]
  have equiv :
      (∃ f : Fin q → ZMod k → ZMod 2, ∃ g : (Fin q → ZMod 2) → O,
        ∀ x, (∀ j ∈ S, (g (fun t => dotProduct (f t) x)).1 j =
          PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr x j) ∧
          (∀ j ∈ T, (g (fun t => dotProduct (f t) x)).2 j =
          PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc x j)) ↔
      ∃ f : Fin q → ZMod k → ZMod 2, ∃ g : (Fin q → ZMod 2) → O,
        ∀ x, g (fun t => dotProduct (f t) x) = F x := by
    constructor
    · rintro ⟨f, g, h⟩
      refine ⟨f, fun a => (mask S (g a).1, mask T (g a).2), fun x => ?_⟩
      exact Prod.ext ((eqmask _ _ _).2 (h x).1) ((eqmask _ _ _).2 (h x).2)
    · rintro ⟨f, g, h⟩
      refine ⟨f, g, fun x => ⟨fun j hj => ?_, fun j hj => ?_⟩⟩
      · simpa [F, mask, hj] using congrArg (fun r : O => r.1 j) (h x)
      · simpa [F, mask, hj] using congrArg (fun r : O => r.2 j) (h x)
  rw [equiv]
  have period (z : ZMod k → ZMod 2) :
      (∀ x, F (x + z) = F x) ↔
      ((∀ j ∈ S, ∀ x, PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr (x + z) j =
        PEqualNP.Outside.L_meta_25716_aux.out k 1 1 0 row cr x j) ∧
       (∀ j ∈ T, ∀ x, PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc (x + z) j =
        PEqualNP.Outside.L_meta_25716_aux.out k 2 3 4 col cc x j)) := by
    constructor
    · intro h
      exact ⟨fun j hj x => (eqmask _ _ _).mp (congrArg Prod.fst (h x)) j hj,
        fun j hj x => (eqmask _ _ _).mp (congrArg Prod.snd (h x)) j hj⟩
    · rintro ⟨hr, hc⟩ x
      exact Prod.ext ((eqmask _ _ _).mpr (fun j hj => hr j hj x))
        ((eqmask _ _ _).mpr (fun j hj => hc j hj x))
  have emptyCases : sites = ∅ → R = ∅ ∧ C = ∅ := by
    intro he
    constructor
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hh := Finset.mem_union_left (pnp25717Patch C 5 11)
        (pnp25717Mem (left := 2) hp (show 0 < 7 by decide))
      change _ ∈ sites at hh
      rw [he] at hh
      exact Finset.notMem_empty _ hh
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hh := Finset.mem_union_right (pnp25717Patch R 2 7)
        (pnp25717Mem (left := 5) hp (show 0 < 11 by decide))
      change _ ∈ sites at hh
      rw [he] at hh
      exact Finset.notMem_empty _ hh
  have constantCase (h : sites = ∅ ∨ k = 1) : ∀ z x, F (x + z) = F x := by
    intro z
    apply (period z).mpr
    rcases h with hempty | hk1
    · obtain ⟨hr, hc⟩ := emptyCases hempty
      simp [S, T, hr, hc, pnp25717Patch]
    · subst k
      have trip : ∀ a : ZMod 2, a + a + a = a := by decide
      have hmix (d u v : ℕ) (i : ZMod 1) :
          PEqualNP.Outside.L_meta_25716_aux.mix 1 d
            (PEqualNP.Outside.L_meta_25716_aux.rot 1 u z) i =
          PEqualNP.Outside.L_meta_25716_aux.rot 1 v z i := by
        simp only [PEqualNP.Outside.L_meta_25716_aux.mix, PEqualNP.Outside.L_meta_25716_aux.rot]
        have all (i : ZMod 1) : i = 0 := Subsingleton.elim _ _
        simp only [all, trip]
      exact ⟨fun i _ => (PEqualNP.Outside.L_meta_25716_aux.key 1 1 1 0
        (Or.inl rfl) row cr z i).mpr ⟨hmix _ _ _ _, Or.inl (Or.inl rfl)⟩,
        fun i _ => (PEqualNP.Outside.L_meta_25716_aux.key 1 2 3 4
        (Or.inr rfl) col cc z i).mpr ⟨hmix _ _ _ _, Or.inl (Or.inl rfl)⟩⟩
  by_cases hzero : sites = ∅ ∨ k = 1
  · simp only [if_pos hzero, Nat.zero_le, iff_true]
    refine ⟨fun _ => 0, fun _ => F 0, fun x => ?_⟩
    simpa using (constantCase hzero x 0).symm
  rw [if_neg hzero]
  by_cases hk3 : k = 3
  · rw [if_pos hk3]
    subst k
    have hnonempty : R.Nonempty ∨ C.Nonempty := by
      by_contra hn
      have hr := Finset.not_nonempty_iff_eq_empty.mp (fun h => hn (Or.inl h))
      have hc := Finset.not_nonempty_iff_eq_empty.mp (fun h => hn (Or.inr h))
      apply hzero
      left
      simp [sites, hr, hc, pnp25717Patch]
    have hfull (p i : ZMod 3) : ∃ t : Fin 3, p + (t.val : ZMod 3) = i := by
      revert p i
      decide
    let e (t : Fin 2) : ZMod 3 := if t = 0 then 1 else 2
    let obs (t : Fin 2) : ZMod 3 → ZMod 2 := Pi.single (e t) 1 - Pi.single 0 1
    have obs_eq (z : ZMod 3 → ZMod 2) (t : Fin 2) :
        dotProduct (obs t) z = z (e t) - z 0 := by
      simp [obs, sub_dotProduct, single_dotProduct]
    refine pnp25717Queries obs F ?_ ?_ q
    · intro a
      refine ⟨fun j => if j = 1 then a 0 else if j = 2 then a 1 else 0, ?_⟩
      funext t
      change dotProduct (obs t) _ = a t
      rw [obs_eq]
      have ht : t = 0 ∨ t = 1 := (by decide : ∀ t : Fin 2, t = 0 ∨ t = 1) t
      rcases ht with rfl | rfl <;>
        simp [e, show (0 : ZMod 3) ≠ 1 by decide, show (0 : ZMod 3) ≠ 2 by decide,
          show (2 : ZMod 3) ≠ 1 by decide]
    · intro z
      rw [period z]
      have hmix (d u : ℕ) (hd : d = 1 ∨ d = 2) (i : ZMod 3) :
          PEqualNP.Outside.L_meta_25716_aux.mix 3 d
            (PEqualNP.Outside.L_meta_25716_aux.rot 3 u z) i =
          PEqualNP.Outside.L_meta_25716_aux.mix 3 d
            (PEqualNP.Outside.L_meta_25716_aux.rot 3 u z) 0 :=
        PEqualNP.Outside.L_meta_25716_aux.hconst 3 (Or.inr rfl) d hd _ _ _
      constructor
      · rintro ⟨hr, hc⟩
        have hconst : ∀ i : ZMod 3, z i = z 0 := by
          intro i
          rcases hnonempty with ⟨p, hp⟩ | ⟨p, hp⟩
          · have hkey (a : ZMod 3) : z a =
                PEqualNP.Outside.L_meta_25716_aux.mix 3 1
                  (PEqualNP.Outside.L_meta_25716_aux.rot 3 1 z) 0 := by
              obtain ⟨t, ht⟩ := hfull p a
              have ha : a ∈ S := by
                rw [← ht]
                simpa [S] using pnp25717Mem (left := 0) hp t.isLt
              have hh := ((PEqualNP.Outside.L_meta_25716_aux.key 3 1 1 0
                (Or.inl rfl) row cr z a).mp (hr a ha)).1
              simpa [PEqualNP.Outside.L_meta_25716_aux.rot, hmix 1 1 (Or.inl rfl) a] using hh.symm
            exact (hkey i).trans (hkey 0).symm
          · have hkey (a : ZMod 3) : z a =
                PEqualNP.Outside.L_meta_25716_aux.mix 3 2
                  (PEqualNP.Outside.L_meta_25716_aux.rot 3 3 z) 0 := by
              obtain ⟨t, ht⟩ := hfull p (a + 4)
              have ha : a + 4 ∈ T := by
                rw [← ht]
                simpa [T] using pnp25717Mem (left := 0) hp (show t.val < 5 by omega)
              have hh := ((PEqualNP.Outside.L_meta_25716_aux.key 3 2 3 4
                (Or.inr rfl) col cc z (a + 4)).mp (hc _ ha)).1
              simpa [PEqualNP.Outside.L_meta_25716_aux.rot, hmix 2 3 (Or.inr rfl) (a + 4)] using hh.symm
            exact (hkey i).trans (hkey 0).symm
        intro t
        rw [obs_eq, hconst, sub_self]
      · intro h
        have h0 := sub_eq_zero.mp ((obs_eq z 0) ▸ h 0)
        have h1 := sub_eq_zero.mp ((obs_eq z 1) ▸ h 1)
        have hz (i : ZMod 3) : z i = z 0 := by
          have hi : i = 0 ∨ i = 1 ∨ i = 2 :=
            (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i
          rcases hi with rfl | rfl | rfl
          · rfl
          · simpa [e] using h0
          · simpa [e] using h1
        have trip : ∀ a : ZMod 2, a + a + a = a := by decide
        have hh (d u v : ℕ) (i : ZMod 3) :
            PEqualNP.Outside.L_meta_25716_aux.mix 3 d
              (PEqualNP.Outside.L_meta_25716_aux.rot 3 u z) i =
            PEqualNP.Outside.L_meta_25716_aux.rot 3 v z i := by
          simp only [PEqualNP.Outside.L_meta_25716_aux.mix, PEqualNP.Outside.L_meta_25716_aux.rot, hz, trip]
        exact ⟨fun i _ => (PEqualNP.Outside.L_meta_25716_aux.key 3 1 1 0
          (Or.inl rfl) row cr z i).mpr ⟨hh _ _ _ _, Or.inl (Or.inr rfl)⟩,
          fun i _ => (PEqualNP.Outside.L_meta_25716_aux.key 3 2 3 4
          (Or.inr rfl) col cc z i).mpr ⟨hh _ _ _ _, Or.inl (Or.inr rfl)⟩⟩
  · rw [if_neg hk3]
    have hk' : ¬ (k = 1 ∨ k = 3) := fun h => h.elim (fun h => hzero (Or.inr h)) hk3
    let e : {i // i ∈ sites} ≃ Fin sites.card :=
      (Fintype.equivFin _).trans (finCongr (Fintype.card_coe sites))
    let obs (t : Fin sites.card) : ZMod k → ZMod 2 := Pi.single (e.symm t).val 1
    have hobs (z : ZMod k → ZMod 2) (t : Fin sites.card) :
        dotProduct (obs t) z = z (e.symm t).val := by
      simp [obs, single_dotProduct]
    refine pnp25717Queries obs F ?_ ?_ q
    · intro a
      refine ⟨fun i => if hi : i ∈ sites then a (e ⟨i, hi⟩) else 0, ?_⟩
      funext t
      simp [hobs, (e.symm t).property]
    · intro z
      rw [period z, pnp25717Normal k hk' row col cr cc z R C]
      constructor
      · intro h t
        rw [hobs]
        exact h _ (e.symm t).property
      · intro h i hi
        simpa [hobs] using h (e ⟨i, hi⟩)
