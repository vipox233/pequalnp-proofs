import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25016_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isN : GateOp → Bool
  | GateOp.not => true
  | _ => false

def rd (g : Gate) : List ℕ := if isN g.op then g.inputs.take 1 else g.inputs

theorem ev (g : Gate) (f : ℕ → Bool) : g.op.eval (g.inputs.map f) = g.op.eval ((rd g).map f) := by
  unfold rd
  split_ifs with h
  · cases e : g.op <;> simp_all [isN]; cases g.inputs <;> simp [GateOp.eval]
  · rfl

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card + gs.countP (fun g => isN g.op) ≤ R.card + gs.length ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ (rd g).toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have hr : (rd g).length + (if isN g.op then 1 else 0) ≤ 2 := by
        unfold rd; split_ifs <;> simp <;> omega
      have : R0.card + (if isN g.op then 1 else 0) ≤ R.card + 1 := by
        have hk : (if isN g.op then 1 else 0) ≤ 1 := by split_ifs <;> omega
        by_cases ht : t ∈ R
        · have e : R0 = R.erase t ∪ (rd g).toFinset := if_pos ht
          rw [e]
          have := Finset.card_union_le (R.erase t) (rd g).toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le (rd g)
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · have e : R0 = R := if_neg ht
          rw [e]; omega
      rw [List.countP_append]
      simp only [List.countP_singleton, List.length_append, List.length_singleton]
      split_ifs at this ⊢ <;> omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        rw [ev, ev]
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

end PEqualNP.Outside.L_meta_25016_aux

open PEqualNP.Outside.L_meta_25016_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25016 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u') → (∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v') → ¬ PEqualNP.Represents.RepSizeAtMost A (n + m - 3) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → n + m - 2 ≤ C.size := by
  intro n m A hn hm hrow hcol hno C hF hR
  by_contra hlt
  obtain ⟨R', hc, hR'⟩ := cone (n + m) C.gates (fun g hg => (hF g hg).2) {C.output}
  rw [Finset.card_singleton] at hc
  have key : ∀ (u u' : Fin n) (v v' : Fin m), (∀ i ∈ R', ((oneEach u v).getD i false = true ↔
      (oneEach u' v').getD i false = true)) → A u v = A u' v' := by
    intro u u' v v' h
    have e1 := hR u v
    have e2 := hR u' v'
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [← e1, ← e2]
    exact hR' _ _ (by simp [oneEach]) (by simp [oneEach])
      (fun i hi => Bool.eq_iff_iff.2 (h i hi)) _ (Finset.mem_singleton_self _)
  let Fr := Finset.univ.filter (fun u : Fin n => ¬ u.val ∈ R')
  let Fc := Finset.univ.filter (fun v : Fin m => ¬ n + v.val ∈ R')
  have hr : Fr.card ≤ 1 := by
    refine Finset.card_le_one.2 fun u hu u0 hu0 => hrow u u0 fun v => key _ _ v v fun i hi => ?_
    simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu0
    have : i ≠ u.val := fun e => hu (e ▸ hi)
    have : i ≠ u0.val := fun e => hu0 (e ▸ hi)
    simp only [oe]
    constructor <;> intro h <;> omega
  have hl : Fc.card ≤ 1 := by
    refine Finset.card_le_one.2 fun v hv v0 hv0 => hcol v v0 fun u => key u u _ _ fun i hi => ?_
    simp only [Fc, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv0
    have : i ≠ n + v.val := fun e => hv (e ▸ hi)
    have : i ≠ n + v0.val := fun e => hv0 (e ▸ hi)
    simp only [oe]
    constructor <;> intro h <;> omega
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => u.val ∈ R')
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun v : Fin m => n + v.val ∈ R')
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  change _ + Fr.card = n at h1
  change _ + Fc.card = m at h2
  have h3 : (Finset.univ.filter (fun u : Fin n => u.val ∈ R')).card ≤ (R'.filter (· < n)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, a.2⟩
  have h4 : (Finset.univ.filter (fun v : Fin m => n + v.val ∈ R')).card ≤
      (R'.filter (¬ · < n)).card := by
    rw [← Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h) :
      Function.Injective (fun v : Fin m => n + v.val))]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, by omega⟩
  have h5 := Finset.card_filter_add_card_filter_not (s := R') (· < n)
  simp only [Circuit.size] at hlt
  have h0 : C.gates.countP (fun g => isN g.op) = 0 := by omega
  refine hno ⟨C, fun g hg => ⟨?_, (hF g hg).2⟩, by simp only [Circuit.size]; omega, hR⟩
  have hn' : isN g.op = false := by
    by_contra hc'
    exact absurd h0 (List.countP_pos_iff.2 ⟨g, hg, by simpa using hc'⟩).ne'
  have := (hF g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
  rcases this with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h] at hn'; simp [isN] at hn'
