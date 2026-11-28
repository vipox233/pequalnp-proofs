import Mathlib
import PEqualNP.Defs

-- L-lib-1458. Probes come from the given linear code applied to labels (x, x^3) of the active
-- vertices over GaloisField 2 h; the circuit budget is matched by an explicit spanning build
-- (one OR gate per vertex outside S, three AND gates per edge) and by a column-counting bound.
-- The forbidden-pair / monotone-pair idea follows L_meta_53188 on upstream main (Apache-2.0).

namespace PEqualNP.Outside.L_lib_1458

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem pairAlg {K : Type} [Field K] (h2 : (2 : K) = 0) (x y x' y' : K) (hxy : x ≠ y)
    (hs : x + y = x' + y') (hc : x^3 + y^3 = x'^3 + y'^3) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have hs0 : x + y ≠ 0 := by
    intro h0
    apply hxy
    linear_combination h0 - y * h2
  have hp : x * y = x' * y' := by
    have h3 : (x + y) * (x * y - x' * y') = 0 := by
      linear_combination (-1 : K) * hc + ((x+y)^2 - (x+y)*(x'+y') + (x'+y')^2 - 3*x'*y') * hs
        + (2*x*y*x' + 2*x*y*y' - x*y^2 - x*x'*y' - x*x'^2 - x*y'^2 - x^2*y + x^2*x' + x^2*y' - y*x'*y' - y*x'^2 - y*y'^2 + y^2*x' + y^2*y') * h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hs0
    · exact sub_eq_zero.mp h
  have hr : (x - x') * (x - y') = 0 := by linear_combination x * hs - hp
  rcases mul_eq_zero.mp hr with h | h
  · left; refine ⟨sub_eq_zero.mp h, ?_⟩; linear_combination hs - h
  · right; refine ⟨sub_eq_zero.mp h, ?_⟩; linear_combination hs - h

theorem zmodBit (a b : ZMod 2) : decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

theorem zmodEq : ∀ a b : ZMod 2, decide (a = 1) = decide (b = 1) → a = b := by decide

theorem labels (n h : Nat) (active : Finset (Fin n)) (hact : active.card ≤ 2^h) :
    ∃ lab : Fin n → Fin (2*h) → Bool,
      (∀ u ∈ active, ∀ v ∈ active, u ≠ v → ∃ t, xor (lab u t) (lab v t) = true) ∧
      (∀ a ∈ active, ∀ b ∈ active, ∀ a' ∈ active, ∀ b' ∈ active, a ≠ b →
        (∀ t, xor (lab a t) (lab b t) = xor (lab a' t) (lab b' t)) →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · refine ⟨fun _ _ => false, ?_, ?_⟩
    · intro u hu v hv huv
      exact absurd (Finset.card_le_one.mp (by simpa using hact) u hu v hv) huv
    · intro a ha b hb _ _ _ _ hab
      exact absurd (Finset.card_le_one.mp (by simpa using hact) a ha b hb) hab
  have hh : h ≠ 0 := by omega
  let K := GaloisField 2 h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let B := Module.finBasisOfFinrankEq (ZMod 2) K (GaloisField.finrank 2 hh)
  let bits := fun (y : K) (i : Fin h) => decide (B.repr y i = 1)
  have bitsAdd : ∀ y z i, bits (y + z) i = xor (bits y i) (bits z i) := by
    intro y z i
    simp only [bits, map_add, Finsupp.add_apply, zmodBit]
  have bitsInj : ∀ y z, (∀ i, bits y i = bits z i) → y = z := by
    intro y z hyz
    apply B.repr.injective
    ext i
    exact zmodEq _ _ (hyz i)
  have hc : Nat.card K = 2^h := GaloisField.card 2 h hh
  let eK : K ≃ Fin (Nat.card K) := Finite.equivFin K
  let x : Fin n → K := fun v => if hv : v ∈ active then
    eK.symm (Fin.cast hc.symm (Fin.castLE hact (active.equivFin ⟨v, hv⟩))) else 0
  have xInj : ∀ u ∈ active, ∀ v ∈ active, x u = x v → u = v := by
    intro u hu v hv huv
    simp only [x, dif_pos hu, dif_pos hv, EmbeddingLike.apply_eq_iff_eq, Fin.cast_inj] at huv
    have := active.equivFin.injective (Fin.castLE_injective hact huv)
    simpa using this
  let lab : Fin n → Fin (2*h) → Bool := fun v t =>
    if ht : t.val < h then bits (x v) ⟨t, ht⟩ else bits (x v ^ 3) ⟨t.val - h, by omega⟩
  have low : ∀ v (i : Fin h), lab v ⟨i, by omega⟩ = bits (x v) i := by
    intro v i; simp [lab, i.isLt]
  have high : ∀ v (i : Fin h), lab v ⟨h + i, by omega⟩ = bits (x v ^ 3) i := by
    intro v i; simp [lab]
  refine ⟨lab, ?_, ?_⟩
  · intro u hu v hv huv
    by_contra hne
    apply huv
    apply xInj u hu v hv
    apply bitsInj
    intro i
    have := hne
    simp only [not_exists, Bool.not_eq_true] at this
    have hi := this ⟨i, by omega⟩
    rw [low, low] at hi
    revert hi; cases bits (x u) i <;> cases bits (x v) i <;> decide
  · intro a ha b hb a' ha' b' hb' hab heq
    have hs : x a + x b = x a' + x b' := by
      apply bitsInj; intro i
      have := heq ⟨i, by omega⟩
      rw [low, low, low, low] at this
      rw [bitsAdd, bitsAdd, this]
    have hcub : x a ^ 3 + x b ^ 3 = x a' ^ 3 + x b' ^ 3 := by
      apply bitsInj; intro i
      have := heq ⟨h + i, by omega⟩
      rw [high, high, high, high] at this
      rw [bitsAdd, bitsAdd, this]
    have hxab : x a ≠ x b := fun e => hab (xInj a ha b hb e)
    rcases pairAlg h2 _ _ _ _ hxab hs hcub with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨xInj _ ha _ ha' e1, xInj _ hb _ hb' e2⟩
    · exact Or.inr ⟨xInj _ ha _ hb' e1, xInj _ hb _ ha' e2⟩




theorem wiresSnoc (G : List Gate) (g : Gate) (o o' : Nat) (x : List Bool) :
    Circuit.wires ⟨G ++ [g], o⟩ x = Circuit.wires ⟨G, o'⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o'⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wiresNil (o : Nat) (x : List Bool) : Circuit.wires ⟨[], o⟩ x = x := by
  simp [Circuit.wires]

theorem wiresLen (G : List Gate) (o : Nat) (x : List Bool) :
    (Circuit.wires ⟨G, o⟩ x).length = x.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [wiresNil]
  | append_singleton G g ih => rw [wiresSnoc G g o o, List.length_append, ih]; simp; omega

theorem wiresPre (G G' : List Gate) (o : Nat) (x : List Bool) :
    ∃ t, Circuit.wires ⟨G ++ G', o⟩ x = Circuit.wires ⟨G, o⟩ x ++ t := by
  induction G' using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton G' g ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G ++ G', o⟩ x).getD i false)], ?_⟩
    rw [← List.append_assoc, wiresSnoc _ g o o, ht, List.append_assoc]

theorem getDPre {l t : List Bool} {j : Nat} (h : j < l.length) : (l ++ t).getD j false = l.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wiresInput (C : Circuit) (x : List Bool) (j : Nat) (hj : j < x.length) :
    (C.wires x).getD j false = x.getD j false := by
  obtain ⟨G, o⟩ := C
  obtain ⟨t, ht⟩ := wiresPre [] G o x
  simp only [List.nil_append] at ht
  rw [ht, wiresNil, getDPre hj]

theorem mapGetD {X : Type} (L : List (X → Bool)) (x : X) (j : Nat) (hj : j < L.length) :
    (L.map (fun g => g x)).getD j false = L[j] x := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- monotonicity of AND/OR circuits -/
theorem wiresMono (G : List Gate) (o : Nat) (hG : Monotone2 ⟨G, o⟩) (x y : List Bool)
    (hl : x.length = y.length) (hxy : ∀ j, x.getD j false = true → y.getD j false = true) :
    ∀ j, (Circuit.wires ⟨G, o⟩ x).getD j false = true → (Circuit.wires ⟨G, o⟩ y).getD j false = true := by
  induction G using List.reverseRecOn with
  | nil => simpa [wiresNil] using hxy
  | append_singleton G g ih =>
    have hG' : Monotone2 ⟨G, o⟩ := fun g' hg' => hG g' (List.mem_append_left _ hg')
    have ih' := ih hG'
    have hg := (hG g (by simp)).1
    intro j hj
    rw [wiresSnoc G g o o] at hj ⊢
    have lx := wiresLen G o x
    have ly := wiresLen G o y
    by_cases hlt : j < x.length + G.length
    · rw [getDPre (by omega)] at hj ⊢
      exact ih' j hj
    · by_cases heq : j = x.length + G.length
      · subst heq
        have ex : (Circuit.wires ⟨G, o⟩ x ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o⟩ x).getD i false)]).getD
            (x.length + G.length) false = g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o⟩ x).getD i false) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, lx]
        have ey : (Circuit.wires ⟨G, o⟩ y ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o⟩ y).getD i false)]).getD
            (x.length + G.length) false = g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o⟩ y).getD i false) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, ly, hl]
        rw [ex] at hj; rw [ey]
        rcases hg with hop | hop <;> rw [hop] at hj ⊢ <;> simp [GateOp.eval] at hj ⊢
        · intro i hi; exact ih' i (hj i hi)
        · obtain ⟨i, hi, hv⟩ := hj; exact ⟨i, hi, ih' i hv⟩
      · exfalso
        have : (Circuit.wires ⟨G, o⟩ x ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o⟩ x).getD i false)]).length ≤ j := by
          simp [lx]; omega
        rw [List.getD_eq_default _ _ this] at hj
        exact Bool.false_ne_true hj

/-- counting lower bound -/
theorem countLB {X ι : Type} (A : Finset X) (L : List (X → Bool)) (C : Circuit) (T : Finset ι)
    (fam : ι → X → Bool)
    (hcomp : ∀ t ∈ T, ∃ j < L.length + C.size, ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = fam t x)
    (hin : ∀ t ∈ T, ∀ g ∈ L, ∃ x ∈ A, fam t x ≠ g x)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ∃ x ∈ A, fam t x ≠ fam t' x) : T.card ≤ C.size := by
  classical
  choose! w hw hwv using hcomp
  have big : ∀ t ∈ T, L.length ≤ w t := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, hx, hne⟩ := hin t ht (L[w t]) (List.getElem_mem hlt)
    apply hne
    rw [← hwv t ht x hx, wiresInput _ _ _ (by simpa using hlt), mapGetD _ _ _ hlt]
  have hmaps : ∀ t ∈ T, w t ∈ Finset.Ico L.length (L.length + C.size) := by
    intro t ht; simp [big t ht, hw t ht]
  have hinj : Set.InjOn w T := by
    intro t ht t' ht' he
    by_contra hne
    obtain ⟨x, hx, hd⟩ := hsep t ht t' ht' hne
    apply hd
    rw [← hwv t ht x hx, ← hwv t' ht' x hx, he]
  have := Finset.card_le_card_of_injOn w hmaps hinj
  simpa using this

def val {X : Type} (L : List (X → Bool)) (G : List Gate) (j : Nat) (x : X) : Bool :=
  (Circuit.wires ⟨G, 0⟩ (L.map (fun g => g x))).getD j false

def Has {X : Type} (L : List (X → Bool)) (G : List Gate) (f : X → Bool) : Prop :=
  ∃ j < L.length + G.length, ∀ x, val L G j x = f x

def Good {X : Type} (L : List (X → Bool)) (G : List Gate) : Prop :=
  Monotone2 ⟨G, 0⟩ ∧ NestedCover.ReadsBack L.length ⟨G, 0⟩

theorem hasInput {X : Type} {L : List (X → Bool)} {f : X → Bool} (G : List Gate) (hf : f ∈ L) : Has L G f := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  refine ⟨j, by omega, fun x => ?_⟩
  simp only [val]
  rw [wiresInput _ _ _ (by simpa using hj), mapGetD _ _ _ hj]

theorem hasMono {X : Type} {L : List (X → Bool)} {G : List Gate} {f : X → Bool} (h : Has L G f) (G' : List Gate) :
    Has L (G ++ G') f := by
  obtain ⟨j, hj, hv⟩ := h
  refine ⟨j, by simp; omega, fun x => ?_⟩
  obtain ⟨t, ht⟩ := wiresPre G G' 0 (L.map (fun g => g x))
  simp only [val] at hv ⊢
  rw [ht, getDPre (by rw [wiresLen]; simpa using hj)]
  exact hv x

theorem hasEq {X : Type} {L : List (X → Bool)} {G : List Gate} {f f' : X → Bool} (h : Has L G f)
    (he : ∀ x, f x = f' x) : Has L G f' := by
  obtain ⟨j, hj, hv⟩ := h
  exact ⟨j, hj, fun x => (hv x).trans (he x)⟩

theorem valNew {X : Type} (L : List (X → Bool)) (G : List Gate) (g : Gate) (x : X) :
    val L (G ++ [g]) (L.length + G.length) x = g.op.eval (g.inputs.map fun i => val L G i x) := by
  simp only [val]
  rw [wiresSnoc G g 0 0]
  have lx := wiresLen G 0 (L.map (fun g => g x))
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [lx])]
  simp [lx]

theorem gateStep {X : Type} {L : List (X → Bool)} {G : List Gate} {f f' : X → Bool} (op : GateOp)
    (hop : op = .and ∨ op = .or) (hG : Good L G) (h1 : Has L G f) (h2 : Has L G f') :
    ∃ g, Good L (G ++ [g]) ∧ Has L (G ++ [g]) (fun x => op.eval [f x, f' x]) := by
  obtain ⟨a, ha, hav⟩ := h1
  obtain ⟨b, hb, hbv⟩ := h2
  refine ⟨⟨op, [a, b]⟩, ⟨?_, ?_⟩, ⟨L.length + G.length, by simp, fun x => ?_⟩⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hG.1 g' h
    · simp only [List.mem_singleton] at h
      subst h
      refine ⟨?_, by simp⟩
      rcases hop with rfl | rfl <;> simp
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < G.length
    · have : NestedCover.gateAt ⟨G ++ [⟨op, [a, b]⟩], 0⟩ j = NestedCover.gateAt ⟨G, 0⟩ j := by
        simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this] at hi
      exact hG.2 j hlt i hi
    · have hj' : j = G.length := by omega
      subst hj'
      have : NestedCover.gateAt ⟨G ++ [⟨op, [a, b]⟩], 0⟩ G.length = ⟨op, [a, b]⟩ := by
        simp [NestedCover.gateAt, List.getD_eq_getElem?_getD]
      rw [this] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [valNew]
    simp [hav, hbv]

theorem andStep {X : Type} {L : List (X → Bool)} {G : List Gate} {f f' : X → Bool}
    (hG : Good L G) (h1 : Has L G f) (h2 : Has L G f') :
    ∃ g, Good L (G ++ [g]) ∧ Has L (G ++ [g]) (fun x => f x && f' x) := by
  obtain ⟨g, hg, hh⟩ := gateStep .and (Or.inl rfl) hG h1 h2
  exact ⟨g, hg, hasEq hh (fun x => by simp [GateOp.eval])⟩

theorem orStep {X : Type} {L : List (X → Bool)} {G : List Gate} {f f' : X → Bool}
    (hG : Good L G) (h1 : Has L G f) (h2 : Has L G f') :
    ∃ g, Good L (G ++ [g]) ∧ Has L (G ++ [g]) (fun x => f x || f' x) := by
  obtain ⟨g, hg, hh⟩ := gateStep .or (Or.inr rfl) hG h1 h2
  exact ⟨g, hg, hasEq hh (fun x => by simp [GateOp.eval])⟩

theorem edgeStep {X : Type} {L : List (X → Bool)} {G : List Gate} {p s q r : X → Bool}
    (hG : Good L G) (hp : Has L G p) (hs : Has L G s) (hq : Has L G q) (hr : Has L G r) :
    ∃ G', Good L (G ++ G') ∧ G'.length = 3 ∧ Has L (G ++ G') (fun x => p x && s x) ∧
      Has L (G ++ G') (fun x => p x && q x) ∧ Has L (G ++ G') (fun x => r x && q x) ∧
      ∃ g, Good L (G ++ G' ++ [g]) ∧ Has L (G ++ G' ++ [g]) (fun x => (p x && s x) || (r x && q x)) := by
  obtain ⟨g1, hg1, a1⟩ := andStep hG hp hs
  obtain ⟨g2, hg2, a2⟩ := andStep hg1 (hasMono hp _) (hasMono hq _)
  obtain ⟨g3, hg3, a3⟩ := andStep hg2 (hasMono (hasMono hr _) _) (hasMono (hasMono hq _) _)
  have e : G ++ [g1] ++ [g2] ++ [g3] = G ++ [g1, g2, g3] := by simp
  obtain ⟨g4, hg4, a4⟩ := orStep hg3 (hasMono (hasMono a1 _) _) a3
  refine ⟨[g1, g2, g3], e ▸ hg3, rfl, e ▸ hasMono (hasMono a1 _) _, e ▸ hasMono a2 _, e ▸ a3, g4, e ▸ hg4, e ▸ a4⟩

theorem build {X : Type} {n : Nat} (L : List (X → Bool)) (bit : Fin n → X → Bool)
    (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (hb : ∀ i, bit i ∈ L) (hs : ∀ e ∈ E, (fun x => bit e.1 x == bit e.2 x) ∈ L)
    (hd : ∀ e ∈ E, (fun x => !(bit e.1 x == bit e.2 x)) ∈ L)
    (hS : ∀ i ∈ S, (fun x => !bit i x) ∈ L)
    (hclosed : ∀ K : Finset (Fin n), S ⊆ K → (∀ e ∈ E, e.1 ∈ K ↔ e.2 ∈ K) → K = Finset.univ) :
    ∃ G, Good L G ∧ G.length = (Finset.univ \ S).card + 3 * E.card ∧
      (∀ i, Has L G (fun x => !bit i x)) ∧
      ∀ e ∈ E, Has L G (fun x => !bit e.1 x && !bit e.2 x) ∧ Has L G (fun x => bit e.1 x && !bit e.2 x) ∧
        Has L G (fun x => !bit e.1 x && bit e.2 x) := by
  classical
  let Inv := fun m : Nat => ∃ (K : Finset (Fin n)) (D : Finset (Fin n × Fin n)) (G : List Gate),
    S ⊆ K ∧ D ⊆ E ∧ D.card = m ∧ Good L G ∧ G.length = (K \ S).card + 3 * D.card ∧
    (∀ i ∈ K, Has L G (fun x => !bit i x)) ∧
    ∀ e ∈ D, e.1 ∈ K ∧ e.2 ∈ K ∧ Has L G (fun x => !bit e.1 x && !bit e.2 x) ∧
      Has L G (fun x => bit e.1 x && !bit e.2 x) ∧ Has L G (fun x => !bit e.1 x && bit e.2 x)
  have base : Inv 0 := by
    refine ⟨S, ∅, [], le_rfl, Finset.empty_subset _, rfl, ⟨fun g hg => by simp at hg, fun j hj => by simp at hj⟩,
      by simp, fun i hi => hasInput _ (hS i hi), fun e he => by simp at he⟩
  have step : ∀ m < E.card, Inv m → Inv (m + 1) := by
    intro m hm ⟨K, D, G, hSK, hDE, hDc, hG, hlen, hneg, hedge⟩
    have hex : ∃ e ∈ E, e ∉ D ∧ (e.1 ∈ K ∨ e.2 ∈ K) := by
      by_contra hno
      simp only [not_exists, not_and, not_or] at hno
      have hK := hclosed K hSK (by
        intro e he
        by_cases hD : e ∈ D
        · exact ⟨fun _ => (hedge e hD).2.1, fun _ => (hedge e hD).1⟩
        · exact ⟨fun h => absurd h (hno e he hD).1, fun h => absurd h (hno e he hD).2⟩)
      obtain ⟨e, heE, heD⟩ : ∃ e ∈ E, e ∉ D := by
        by_contra hall
        simp only [not_exists, not_and, not_not] at hall
        have := Finset.card_le_card (show E ⊆ D from hall)
        omega
      exact (hno e heE heD).1 (hK ▸ Finset.mem_univ _)
    obtain ⟨e, heE, heD, hend⟩ := hex
    have hDc' : (insert e D).card = m + 1 := by rw [Finset.card_insert_of_notMem heD, hDc]
    have hsub : insert e D ⊆ E := Finset.insert_subset heE hDE
    have hs' := hasInput (L := L) G (hs e heE)
    have hd' := hasInput (L := L) G (hd e heE)
    -- the known endpoint w and the other endpoint o
    have key : ∀ w o : Fin n, w ∈ K → (w = e.1 ∧ o = e.2 ∨ w = e.2 ∧ o = e.1) →
        (∀ x, (bit w x == bit o x) = (bit e.1 x == bit e.2 x)) → Inv (m + 1) := by
      intro w o hw hwo hsym
      have hsw : Has L G (fun x => bit w x == bit o x) := hasEq hs' (fun x => (hsym x).symm)
      have hdw : Has L G (fun x => !(bit w x == bit o x)) := hasEq hd' (fun x => by rw [hsym])
      obtain ⟨G', hG', hl3, a1, a2, a3, g, hg, a4⟩ :=
        edgeStep hG (hneg w hw) hsw hdw (hasInput G (hb w))
      have lowE : ∀ G'' : List Gate, Has L G'' (fun x => !bit w x && (bit w x == bit o x)) →
          Has L G'' (fun x => !bit e.1 x && !bit e.2 x) := by
        intro G'' h
        refine hasEq h (fun x => ?_)
        rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases bit e.1 x <;> cases bit e.2 x <;> rfl
      have fwdE : ∀ G'' : List Gate, Has L G'' (fun x => !bit w x && !(bit w x == bit o x)) →
          Has L G'' (fun x => bit w x && !(bit w x == bit o x)) →
          Has L G'' (fun x => bit e.1 x && !bit e.2 x) := by
        intro G'' h1 h2
        rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hasEq h2 (fun x => by cases bit e.1 x <;> cases bit e.2 x <;> rfl)
        · exact hasEq h1 (fun x => by cases bit e.1 x <;> cases bit e.2 x <;> rfl)
      have bwdE : ∀ G'' : List Gate, Has L G'' (fun x => !bit w x && !(bit w x == bit o x)) →
          Has L G'' (fun x => bit w x && !(bit w x == bit o x)) →
          Has L G'' (fun x => !bit e.1 x && bit e.2 x) := by
        intro G'' h1 h2
        rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hasEq h1 (fun x => by cases bit e.1 x <;> cases bit e.2 x <;> rfl)
        · exact hasEq h2 (fun x => by cases bit e.1 x <;> cases bit e.2 x <;> rfl)
      have oK : ∀ v, v = w ∨ v = o → (v = e.1 ∨ v = e.2) := by
        intro v hv; rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
      by_cases ho : o ∈ K
      · refine ⟨K, insert e D, G ++ G', hSK, hsub, hDc', hG', ?_, fun i hi => hasMono (hneg i hi) _, ?_⟩
        · rw [List.length_append, hl3, hlen, Finset.card_insert_of_notMem heD]; ring
        · intro e' he'
          rcases Finset.mem_insert.1 he' with rfl | he'
          · refine ⟨?_, ?_, lowE _ a1, fwdE _ a2 a3, bwdE _ a2 a3⟩ <;>
              rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
          · obtain ⟨h1, h2, b1, b2, b3⟩ := hedge e' he'
            exact ⟨h1, h2, hasMono b1 _, hasMono b2 _, hasMono b3 _⟩
      · have hoS : o ∉ S := fun h => ho (hSK h)
        refine ⟨insert o K, insert e D, G ++ G' ++ [g], hSK.trans (Finset.subset_insert _ _), hsub, hDc', hg, ?_, ?_, ?_⟩
        · rw [List.length_append, List.length_append, hl3, hlen, Finset.card_insert_of_notMem heD,
            Finset.insert_sdiff_of_notMem _ hoS, Finset.card_insert_of_notMem (fun h => ho (Finset.mem_sdiff.1 h).1)]
          simp; ring
        · intro i hi
          rcases Finset.mem_insert.1 hi with hio | hi
          · subst hio
            exact hasEq a4 (fun x => by cases bit w x <;> cases bit i x <;> rfl)
          · exact hasMono (hasMono (hneg i hi) _) _
        · intro e' he'
          rcases Finset.mem_insert.1 he' with rfl | he'
          · refine ⟨?_, ?_, hasMono (lowE _ a1) _, hasMono (fwdE _ a2 a3) _, hasMono (bwdE _ a2 a3) _⟩ <;>
              rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hw]
          · obtain ⟨h1, h2, b1, b2, b3⟩ := hedge e' he'
            exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2,
              hasMono (hasMono b1 _) _, hasMono (hasMono b2 _) _, hasMono (hasMono b3 _) _⟩
    rcases hend with h1 | h2
    · exact key e.1 e.2 h1 (Or.inl ⟨rfl, rfl⟩) (fun x => rfl)
    · exact key e.2 e.1 h2 (Or.inr ⟨rfl, rfl⟩) (fun x => by cases bit e.1 x <;> cases bit e.2 x <;> rfl)
  have all : ∀ m ≤ E.card, Inv m := by
    intro m
    induction m with
    | zero => exact fun _ => base
    | succ m ih => exact fun hm => step m (by omega) (ih (by omega))
  obtain ⟨K, D, G, hSK, hDE, hDc, hG, hlen, hneg, hedge⟩ := all E.card le_rfl
  have hDE' : D = E := Finset.eq_of_subset_of_card_le hDE (by omega)
  subst hDE'
  have hK := hclosed K hSK (fun e he => ⟨fun _ => (hedge e he).2.1, fun _ => (hedge e he).1⟩)
  subst hK
  exact ⟨G, hG, hlen, fun i => hneg i (Finset.mem_univ _), fun e he => (hedge e he).2.2⟩



inductive Tag (n : Nat) where
  | zero | one
  | bit (i : Fin n)
  | same (e : Fin n × Fin n)
  | diff (e : Fin n × Fin n)
  | neg (i : Fin n)
  | low (e : Fin n × Fin n)
  | fwd (e : Fin n × Fin n)
  | bwd (e : Fin n × Fin n)

def colB {n : Nat} (m : Fin n → Bool) : Tag n → Bool
  | .zero => false
  | .one => true
  | .bit i => m i
  | .same e => m e.1 == m e.2
  | .diff e => !(m e.1 == m e.2)
  | .neg i => !m i
  | .low e => !m e.1 && !m e.2
  | .fwd e => m e.1 && !m e.2
  | .bwd e => !m e.1 && m e.2

def col {n : Nat} {W : Type} (bit : Fin n → W → Bool) (t : Tag n) (x : W) : Bool :=
  colB (fun w => bit w x) t

def Valid {n : Nat} (E : Finset (Fin n × Fin n)) : Tag n → Prop
  | .same e => e ∈ E
  | .diff e => e ∈ E
  | .low e => e ∈ E
  | .fwd e => e ∈ E
  | .bwd e => e ∈ E
  | _ => True

def IsNeed {n : Nat} (E : Finset (Fin n × Fin n)) : Tag n → Prop
  | .neg _ => True
  | .low e => e ∈ E
  | .fwd e => e ∈ E
  | .bwd e => e ∈ E
  | _ => False

theorem pickB {n : Nat} (bit : Fin n → Finset (Fin n) → Bool) (hbit : ∀ i x, bit i x = true ↔ i ∈ x)
    (β : Fin n → Bool) (t t' : Tag n)
    (H : ∃ b : Bool, colB (fun w => decide (β w = b)) t ≠ colB (fun w => decide (β w = b)) t') :
    ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ β w = b) → col bit t x ≠ col bit t' x := by
  obtain ⟨b, hb⟩ := H
  refine ⟨b, fun x hx => ?_⟩
  have : (fun w => bit w x) = (fun w => decide (β w = b)) :=
    funext fun w => by rw [Bool.eq_iff_iff, hbit, hx]; simp
  simp only [col]
  rw [this]
  exact hb

theorem atZero {n : Nat} (bit : Fin n → Finset (Fin n) → Bool) (hbit : ∀ i x, bit i x = true ↔ i ∈ x)
    (x : Finset (Fin n)) (hx : ∀ v, v ∉ x) (t : Tag n) : col bit t x = colB (fun _ => false) t := by
  have : (fun w => bit w x) = (fun _ => false) :=
    funext fun w => by rw [Bool.eq_false_iff, ne_eq, hbit]; exact hx w
  simp only [col]; rw [this]

theorem atClass {n c : Nat} (bit : Fin n → Finset (Fin n) → Bool) (hbit : ∀ i x, bit i x = true ↔ i ∈ x)
    (color : Fin n → Fin c) (j : Fin c)
    (x : Finset (Fin n)) (hx : ∀ v, v ∈ x ↔ color v = j) (t : Tag n) :
    col bit t x = colB (fun w => decide (color w = j)) t := by
  have : (fun w => bit w x) = (fun w => decide (color w = j)) :=
    funext fun w => by rw [Bool.eq_iff_iff, hbit, hx]; simp
  simp only [col]; rw [this]

section
variable {n c h r : Nat} (bit : Fin n → Finset (Fin n) → Bool) (hbit : ∀ i x, bit i x = true ↔ i ∈ x)
  (A : Finset (Finset (Fin n))) (color : Fin n → Fin c) (E : Finset (Fin n × Fin n))
  (active : Finset (Fin n)) (enc : (Fin (2*h) → Bool) → Fin r → Bool) (lab : Fin n → Fin (2*h) → Bool)
  (hzero : ∃ x ∈ A, ∀ v, v ∉ x)
  (hclass : ∀ j, ∃ x ∈ A, ∀ v, v ∈ x ↔ color v = j)
  (hprobe : ∀ z : Fin (2*h) → Bool, (∃ t, z t = true) → ∀ P : Finset (Fin n) → Prop,
    (∀ k, enc z k = true → ∃ b : Bool, ∀ x, (∀ v, v ∈ x ↔ enc (lab v) k = b) → P x) → ∃ x ∈ A, P x)
  (hlin : ∀ x y j, enc (fun k => xor (x k) (y k)) j = xor (enc x j) (enc y j))
  (hlab1 : ∀ u ∈ active, ∀ v ∈ active, u ≠ v → ∃ t, xor (lab u t) (lab v t) = true)
  (hlab2 : ∀ a ∈ active, ∀ b ∈ active, ∀ a' ∈ active, ∀ b' ∈ active, a ≠ b →
        (∀ t, xor (lab a t) (lab b t) = xor (lab a' t) (lab b' t)) →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
  (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.1 ∈ active ∧ e.2 ∈ active)
  (hcol : ∀ e ∈ E, color e.1 = color e.2)
  (hlone : ∀ i i', i ≠ i' → color i = color i' → i ∈ active ∧ i' ∈ active)
include hprobe hlin hlab1 in
theorem probe2 (u v : Fin n) (hu : u ∈ active) (hv : v ∈ active) (huv : u ≠ v) (P : Finset (Fin n) → Prop)
    (H : ∀ k, enc (lab u) k ≠ enc (lab v) k → ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ enc (lab w) k = b) → P x) :
    ∃ x ∈ A, P x := by
  refine hprobe (fun t => xor (lab u t) (lab v t)) (hlab1 u hu v hv huv) P (fun k hk => H k ?_)
  rw [hlin] at hk
  intro heq; rw [heq] at hk; simp at hk

include hprobe hlin hlab2 hE in
theorem probe4 (e e' : Fin n × Fin n) (he : e ∈ E) (he' : e' ∈ E) (hne : e ≠ e') (P : Finset (Fin n) → Prop)
    (H : ∀ k, xor (enc (lab e.1) k) (enc (lab e.2) k) ≠ xor (enc (lab e'.1) k) (enc (lab e'.2) k) →
      ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ enc (lab w) k = b) → P x) :
    ∃ x ∈ A, P x := by
  obtain ⟨h1, a1, b1⟩ := hE e he
  obtain ⟨h2, a2, b2⟩ := hE e' he'
  have nz : ∃ t, (fun t => xor (xor (lab e.1 t) (lab e.2 t)) (xor (lab e'.1 t) (lab e'.2 t))) t = true := by
    by_contra hno
    simp only [not_exists, Bool.not_eq_true] at hno
    have hs : ∀ t, xor (lab e.1 t) (lab e.2 t) = xor (lab e'.1 t) (lab e'.2 t) := by
      intro t; have := hno t; revert this
      cases xor (lab e.1 t) (lab e.2 t) <;> cases xor (lab e'.1 t) (lab e'.2 t) <;> simp
    rcases hlab2 _ a1 _ b1 _ a2 _ b2 (ne_of_lt h1) hs with ⟨q1, q2⟩ | ⟨q1, q2⟩
    · exact hne (Prod.ext q1 q2)
    · rw [q1, q2] at h1; exact absurd (h1.trans h2) (lt_irrefl _)
  refine hprobe _ nz P (fun k hk => H k ?_)
  have : enc (fun t => xor (xor (lab e.1 t) (lab e.2 t)) (xor (lab e'.1 t) (lab e'.2 t))) k =
      xor (xor (enc (lab e.1) k) (enc (lab e.2) k)) (xor (enc (lab e'.1) k) (enc (lab e'.2) k)) := by
    rw [hlin (fun t => xor (lab e.1 t) (lab e.2 t)) (fun t => xor (lab e'.1 t) (lab e'.2 t)), hlin, hlin]
  rw [this] at hk
  intro heq; rw [heq] at hk; simp at hk

end

section
variable {n c r : Nat} (bit : Fin n → Finset (Fin n) → Bool) (hbit : ∀ i x, bit i x = true ↔ i ∈ x)
  (A : Finset (Finset (Fin n))) (color : Fin n → Fin c) (E : Finset (Fin n × Fin n))
  (active : Finset (Fin n)) (β : Fin n → Fin r → Bool)
  (hzero : ∃ x ∈ A, ∀ v, v ∉ x)
  (hclass : ∀ j, ∃ x ∈ A, ∀ v, v ∈ x ↔ color v = j)
  (hP2 : ∀ u ∈ active, ∀ v ∈ active, u ≠ v → ∀ P : Finset (Fin n) → Prop,
    (∀ k, β u k ≠ β v k → ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ β w k = b) → P x) → ∃ x ∈ A, P x)
  (hP4 : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → ∀ P : Finset (Fin n) → Prop,
    (∀ k, xor (β e.1 k) (β e.2 k) ≠ xor (β e'.1 k) (β e'.2 k) →
      ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ β w k = b) → P x) → ∃ x ∈ A, P x)
  (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.1 ∈ active ∧ e.2 ∈ active)
  (hcol : ∀ e ∈ E, color e.1 = color e.2)
  (hlone : ∀ i i', i ≠ i' → color i = color i' → i ∈ active ∧ i' ∈ active)
include hbit hzero hclass hP2 hP4 hE hcol hlone

theorem sepNeg (i : Fin n) (t' : Tag n) (hv : Valid E t') (hne : Tag.neg i ≠ t') :
    ∃ x ∈ A, col bit (.neg i) x ≠ col bit t' x := by
  obtain ⟨x0, hx0A, hx0⟩ := hzero
  have z0 := atZero bit hbit x0 hx0
  obtain ⟨xi, hxiA, hxi⟩ := hclass (color i)
  have zi := atClass bit hbit color _ xi hxi
  cases t' with
  | zero => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | one => exact ⟨xi, hxiA, by simp [zi, colB]⟩
  | bit j => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | same e => exact ⟨xi, hxiA, by simp [zi, colB, hcol e hv]⟩
  | diff e => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | fwd e => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | bwd e => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | neg i' =>
    have hii : i ≠ i' := fun h => hne (h ▸ rfl)
    by_cases hc : color i = color i'
    · obtain ⟨ha, ha'⟩ := hlone i i' hii hc
      exact hP2 i ha i' ha' hii _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β i k = p; generalize β i' k = q; revert p q; decide))
    · exact ⟨xi, hxiA, by simp [zi, colB, Ne.symm hc]⟩
  | low e =>
    obtain ⟨hlt, ha, hb⟩ := hE e hv
    by_cases hc : color i = color e.1
    · exact hP2 e.1 ha e.2 hb (ne_of_lt hlt) _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β i k = p; generalize β e.1 k = q; generalize β e.2 k = q'; revert p q q'; decide))
    · exact ⟨xi, hxiA, by simp [zi, colB, ← hcol e hv, Ne.symm hc]⟩

theorem sepLow (e : Fin n × Fin n) (he : e ∈ E) (t' : Tag n) (hv : Valid E t') (hne : Tag.low e ≠ t') :
    ∃ x ∈ A, col bit (.low e) x ≠ col bit t' x := by
  obtain ⟨x0, hx0A, hx0⟩ := hzero
  have z0 := atZero bit hbit x0 hx0
  obtain ⟨xi, hxiA, hxi⟩ := hclass (color e.1)
  have zi := atClass bit hbit color _ xi hxi
  have hce := hcol e he
  obtain ⟨hlt, ha, hb⟩ := hE e he
  cases t' with
  | zero => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | one => exact ⟨xi, hxiA, by simp [zi, colB]⟩
  | bit j => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | same e' => exact ⟨xi, hxiA, by simp [zi, colB, hcol e' hv]⟩
  | diff e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | fwd e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | bwd e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | neg i =>
    by_cases hc : color i = color e.1
    · exact hP2 e.1 ha e.2 hb (ne_of_lt hlt) _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β i k = p; generalize β e.1 k = q; generalize β e.2 k = q'; revert p q q'; decide))
    · exact ⟨xi, hxiA, by simp [zi, colB, hc]⟩
  | low e' =>
    have hee : e ≠ e' := fun h => hne (h ▸ rfl)
    by_cases hc : color e.1 = color e'.1
    · exact hP4 e he e' hv hee _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))
    · exact ⟨xi, hxiA, by simp [zi, colB, ← hcol e' hv, Ne.symm hc]⟩

theorem sepFwd (e : Fin n × Fin n) (he : e ∈ E) (t' : Tag n) (hv : Valid E t') (hne : Tag.fwd e ≠ t') :
    ∃ x ∈ A, col bit (.fwd e) x ≠ col bit t' x := by
  obtain ⟨x0, hx0A, hx0⟩ := hzero
  have z0 := atZero bit hbit x0 hx0
  have hce := hcol e he
  obtain ⟨hlt, ha, hb⟩ := hE e he
  cases t' with
  | zero => exact hP2 e.1 ha e.2 hb (ne_of_lt hlt) _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = q; generalize β e.2 k = q'; revert q q'; decide))
  | one => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | bit j =>
    obtain ⟨xj, hxjA, hxj⟩ := hclass (color j)
    exact ⟨xj, hxjA, by simp [atClass bit hbit color _ xj hxj, colB, hce]⟩
  | same e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | neg i => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | low e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | diff e' =>
    obtain ⟨hlt', ha', hb'⟩ := hE e' hv
    exact hP2 e'.1 ha' e'.2 hb' (ne_of_lt hlt') _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))
  | fwd e' =>
    have hee : e ≠ e' := fun h => hne (h ▸ rfl)
    exact hP4 e he e' hv hee _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))
  | bwd e' =>
    by_cases hee : e = e'
    · subst hee
      exact hP2 e.1 ha e.2 hb (ne_of_lt hlt) _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = q; generalize β e.2 k = q'; revert q q'; decide))
    · exact hP4 e he e' hv hee _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))

theorem sepBwd (e : Fin n × Fin n) (he : e ∈ E) (t' : Tag n) (hv : Valid E t') (hne : Tag.bwd e ≠ t') :
    ∃ x ∈ A, col bit (.bwd e) x ≠ col bit t' x := by
  obtain ⟨x0, hx0A, hx0⟩ := hzero
  have z0 := atZero bit hbit x0 hx0
  have hce := hcol e he
  obtain ⟨hlt, ha, hb⟩ := hE e he
  cases t' with
  | zero => exact hP2 e.1 ha e.2 hb (ne_of_lt hlt) _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = q; generalize β e.2 k = q'; revert q q'; decide))
  | one => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | bit j =>
    obtain ⟨xj, hxjA, hxj⟩ := hclass (color j)
    exact ⟨xj, hxjA, by simp [atClass bit hbit color _ xj hxj, colB, hce]⟩
  | same e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | neg i => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | low e' => exact ⟨x0, hx0A, by simp [z0, colB]⟩
  | diff e' =>
    obtain ⟨hlt', ha', hb'⟩ := hE e' hv
    exact hP2 e'.1 ha' e'.2 hb' (ne_of_lt hlt') _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))
  | bwd e' =>
    have hee : e ≠ e' := fun h => hne (h ▸ rfl)
    exact hP4 e he e' hv hee _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))
  | fwd e' =>
    by_cases hee : e = e'
    · subst hee
      exact hP2 e.1 ha e.2 hb (ne_of_lt hlt) _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = q; generalize β e.2 k = q'; revert q q'; decide))
    · exact hP4 e he e' hv hee _ (fun k hk => pickB bit hbit (fun w => β w k) _ _ (by
        simp only [colB]; revert hk
        generalize β e.1 k = p; generalize β e.2 k = q; generalize β e'.1 k = p'; generalize β e'.2 k = q'
        revert p q p' q'; decide))


theorem sepAny (t t' : Tag n) (ht : IsNeed E t) (hv : Valid E t') (hne : t ≠ t') :
    ∃ x ∈ A, col bit t x ≠ col bit t' x := by
  cases t with
  | neg i => exact sepNeg bit hbit A color E active β hzero hclass hP2 hP4 hE hcol hlone i t' hv hne
  | low e => exact sepLow bit hbit A color E active β hzero hclass hP2 hP4 hE hcol hlone e ht t' hv hne
  | fwd e => exact sepFwd bit hbit A color E active β hzero hclass hP2 hP4 hE hcol hlone e ht t' hv hne
  | bwd e => exact sepBwd bit hbit A color E active β hzero hclass hP2 hP4 hE hcol hlone e ht t' hv hne
  | _ => exact ht.elim

end

theorem survive {β γ : Type} (lost : Finset β) (d : Nat) (hl : lost.card ≤ d) (K : Finset γ)
    (hK : d < K.card) (f : γ → β) (hf : Function.Injective f) : ∃ k ∈ K, f k ∉ lost := by
  classical
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have := Finset.card_le_card_of_injOn f (fun k hk => hno k hk) hf.injOn
  omega

def tagOf {n : Nat} : Fin n ⊕ ((Fin n × Fin n) ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n))) → Tag n
  | .inl i => .neg i
  | .inr (.inl e) => .low e
  | .inr (.inr (.inl e)) => .fwd e
  | .inr (.inr (.inr e)) => .bwd e

def InputOK {n : Nat} (S : Finset (Fin n)) : Tag n → Prop
  | .neg i => i ∈ S
  | .low _ => False
  | .fwd _ => False
  | .bwd _ => False
  | _ => True

theorem tagInj {n : Nat} (t t' : Fin n ⊕ ((Fin n × Fin n) ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n))))
    (h : tagOf t = tagOf t') : t = t' := by
  rcases t with i | e | e | e <;> rcases t' with i' | e' | e' | e' <;> simp [tagOf] at h ⊢ <;> exact h

end PEqualNP.Outside.L_lib_1458

open PEqualNP.Outside.L_lib_1458 in
theorem PEqualNP.Outside.L_lib_1458 :
∀ (n h r d : Nat) (active : Finset (Fin n)), active.card ≤ 2^h →
  ∀ enc : (Fin (2*h) → Bool) → Fin r → Bool,
    (∀ x y j, enc (fun k => xor (x k) (y k)) j = xor (enc x j) (enc y j)) →
    (∀ x, (∃ k, x k = true) → d < (Finset.univ.filter (fun j => enc x j = true)).card) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  ∃ probe : Fin r → W,
    ∀ (c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
      (∀ e ∈ E, e.1 < e.2 ∧ e.1 ∈ active ∧ e.2 ∈ active) →
      Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let I := (Fin r × Bool) ⊕ (Option (Fin c) × Fin (d+1))
  let row : I → W := Sum.elim
    (fun a => if a.2 then probe a.1 else Finset.univ \ probe a.1)
    (fun a => a.1.elim ∅ (fun j => Finset.univ.filter (fun v => color v = j)))
  Fintype.card I = 2*r+(c+1)*(d+1) ∧
    ∀ lost : Finset I, lost.card ≤ d → keeps ((Finset.univ \ lost).image row) := by
  intro n h r d active hact enc hlin hdist
  obtain ⟨lab, hl1, hl2⟩ := labels n h active hact
  show ∃ probe : Fin r → Finset (Fin n), _
  refine ⟨fun k => Finset.univ.filter (fun v => enc (lab v) k = true), ?_⟩
  intro c E color hEp hsurj hconn bit neg same raw need keeps I row
  refine ⟨by simp [I, Fintype.card_sum, Fintype.card_prod, Fintype.card_option]; ring, ?_⟩
  intro lost hlost
  suffices H : ∀ A : Finset (Finset (Fin n)), (∀ i, i ∉ lost → row i ∈ A) → keeps A by
    refine H _ (fun i hi => ?_)
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨i, hi, rfl⟩
  intro A hA
  have hbit : ∀ i x, bit i x = true ↔ i ∈ x := fun i x => by simp [bit]
  have comp : ∀ o : Option (Fin c), ∃ k : Fin (d+1), (Sum.inr (o, k) : I) ∉ lost := by
    intro o
    obtain ⟨k, -, hk⟩ := survive lost d hlost Finset.univ (by simp)
      (fun k : Fin (d+1) => (Sum.inr (o, k) : I)) (by intro a b hab; exact (Prod.mk.inj (Sum.inr.inj hab)).2)
    exact ⟨k, hk⟩
  have hzero : ∃ x ∈ A, ∀ v, v ∉ x := by
    obtain ⟨k, hk⟩ := comp none
    exact ⟨_, hA _ hk, by simp [row]⟩
  have hclass : ∀ j, ∃ x ∈ A, ∀ v, v ∈ x ↔ color v = j := by
    intro j
    obtain ⟨k, hk⟩ := comp (some j)
    exact ⟨_, hA _ hk, fun v => by simp [row]⟩
  have hprobe : ∀ z : Fin (2*h) → Bool, (∃ t, z t = true) → ∀ P : Finset (Fin n) → Prop,
      (∀ k, enc z k = true → ∃ b : Bool, ∀ x, (∀ v, v ∈ x ↔ enc (lab v) k = b) → P x) →
      ∃ x ∈ A, P x := by
    intro z hz P HP
    have hK := hdist z hz
    choose! b hb using HP
    obtain ⟨k, hkK, hk⟩ := survive lost d hlost (Finset.univ.filter (fun j => enc z j = true)) hK
      (fun k => (Sum.inl (k, b k) : I)) (by intro a a' haa; exact (Prod.mk.inj (Sum.inl.inj haa)).1)
    refine ⟨_, hA _ hk, hb k (by simpa using hkK) _ ?_⟩
    intro v
    cases hbk : b k <;> simp [row, hbk]
  have hcol : ∀ e ∈ E, color e.1 = color e.2 := by
    intro e he
    have := ((hconn (Finset.univ.filter (fun i => color i = color e.1))).mpr
      (by intro i j hij; simp [hij])) e he
    simpa [eq_comm] using this.mp (by simp)
  have one : ∀ i i', i ≠ i' → color i = color i' → i ∈ active := by
    intro i i' hne hc
    by_contra hi
    have hZ := (hconn {i}).mp (by
      intro e he
      have := hEp e he
      have h1 : e.1 ≠ i := fun q => hi (q ▸ this.2.1)
      have h2 : e.2 ≠ i := fun q => hi (q ▸ this.2.2)
      simp [h1, h2])
    have := (hZ i i' hc).mp (by simp)
    simp at this
    exact hne this.symm
  have hlone : ∀ i i', i ≠ i' → color i = color i' → i ∈ active ∧ i' ∈ active :=
    fun i i' hne hc => ⟨one i i' hne hc, one i' i (Ne.symm hne) hc.symm⟩
  have hP2 : ∀ u ∈ active, ∀ v ∈ active, u ≠ v → ∀ P : Finset (Fin n) → Prop,
      (∀ k, enc (lab u) k ≠ enc (lab v) k → ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ enc (lab w) k = b) → P x) →
      ∃ x ∈ A, P x :=
    fun u hu v hv huv P H => probe2 (A := A) (active := active) (enc := enc)
      (lab := lab) hprobe hlin hl1 u v hu hv huv P H
  have hP4 : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → ∀ P : Finset (Fin n) → Prop,
      (∀ k, xor (enc (lab e.1) k) (enc (lab e.2) k) ≠ xor (enc (lab e'.1) k) (enc (lab e'.2) k) →
        ∃ b : Bool, ∀ x, (∀ w, w ∈ x ↔ enc (lab w) k = b) → P x) →
      ∃ x ∈ A, P x :=
    fun e he e' he' hne P H => probe4 (A := A) (E := E) (active := active)
      (enc := enc) (lab := lab) hprobe hlin hl2 hEp e e' he he' hne P H
  have sep : ∀ t t' : Tag n, IsNeed E t → Valid E t' → t ≠ t' →
      ∃ x ∈ A, col bit t x ≠ col bit t' x :=
    fun t t' ht hv hne => sepAny bit hbit _ color E active (fun w k => enc (lab w) k) hzero hclass hP2 hP4
      hEp hcol hlone t t' ht hv hne
  have hsameStd : ∀ e, same e = (fun x => bit e.1 x == bit e.2 x) := by
    intro e; funext x
    simp only [same]
    cases bit e.1 x <;> cases bit e.2 x <;> simp
  have hdiffStd : ∀ e, (fun x => !same e x) = (fun x => !(bit e.1 x == bit e.2 x)) := by
    intro e; rw [hsameStd e]
  have negNeed : ∀ i, neg i ∈ need := by
    intro i
    simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))
  have lowNeed : ∀ e ∈ E, (fun x => neg e.1 x && neg e.2 x) ∈ need := by
    intro e he
    simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))
  have fwdNeed : ∀ e ∈ E, (fun x => bit e.1 x && neg e.2 x) ∈ need := by
    intro e he
    simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨e, he, rfl⟩)
  have bwdNeed : ∀ e ∈ E, (fun x => neg e.1 x && bit e.2 x) ∈ need := by
    intro e he
    simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨e, he, rfl⟩
  intro S p L
  have memL : ∀ g, ((((g = (fun _ => false) ∨ g = (fun _ => true)) ∨ ∃ i, bit i = g) ∨ ∃ e ∈ E, same e = g) ∨
      ∃ e ∈ E, (fun x => !same e x) = g) ∨ (∃ i ∈ S, neg i = g) → g ∈ L := by
    intro g hg
    simp only [L, raw, Finset.mem_toList, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and]
    exact hg
  have inputTag : ∀ g ∈ L, ∃ t', Valid E t' ∧ g = col bit t' ∧ InputOK S t' := by
    intro g hg
    simp only [L, raw, Finset.mem_toList, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and] at hg
    rcases hg with ((((rfl | rfl) | ⟨i, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨i, hi, rfl⟩
    · exact ⟨.zero, trivial, rfl, trivial⟩
    · exact ⟨.one, trivial, rfl, trivial⟩
    · exact ⟨.bit i, trivial, rfl, trivial⟩
    · exact ⟨.same e, he, hsameStd e, trivial⟩
    · exact ⟨.diff e, he, hdiffStd e, trivial⟩
    · exact ⟨.neg i, trivial, rfl, hi⟩
  have hclosed : ∀ K : Finset (Fin n), S ⊆ K → (∀ e ∈ E, e.1 ∈ K ↔ e.2 ∈ K) → (∀ j, ∃ i ∈ S, color i = j) →
      K = Finset.univ := by
    intro K hSK hK hcov
    have hc := (hconn K).mp hK
    ext v
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨s, hs, hsv⟩ := hcov (color v)
    exact (hc s v hsv).mp (hSK hs)
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hcard : (Finset.univ \ S).card = n - S.card := by simp [Finset.card_univ_diff]
  constructor
  · rintro ⟨⟨G, o⟩, hmono, hrb, hout, hsize, hall⟩
    have cov : ∀ j, ∃ i ∈ S, color i = j := by
      by_contra hno
      simp only [not_forall, not_exists, not_and] at hno
      obtain ⟨j, hj⟩ := hno
      obtain ⟨x0, hx0A, hx0⟩ := hzero
      obtain ⟨xj, hxjA, hxj⟩ := hclass j
      obtain ⟨i, hi⟩ := hsurj j
      obtain ⟨w, -, hw⟩ := hall (neg i) (negNeed i)
      have z0 := atZero bit hbit x0 hx0
      have zj := atClass bit hbit color j xj hxj
      have m := wiresMono G o hmono (L.map (fun g => g x0))
        (L.map (fun g => g xj)) (by simp) (by
          intro m hm
          by_cases hlt : m < L.length
          · rw [mapGetD _ _ _ hlt] at hm ⊢
            obtain ⟨t', hv, heq, hok⟩ := inputTag _ (List.getElem_mem hlt)
            rw [heq] at hm ⊢
            rw [z0] at hm
            rw [zj]
            cases t' with
            | zero => exact absurd hm (by simp [colB])
            | one => rfl
            | bit v => exact absurd hm (by simp [colB])
            | same e => simp [colB, hcol e hv]
            | diff e => exact absurd hm (by simp [colB])
            | neg s => simp [colB, hj s hok]
            | low e => exact absurd hok id
            | fwd e => exact absurd hok id
            | bwd e => exact absurd hok id
          · rw [List.getD_eq_default _ _ (by simpa using hlt)] at hm
            exact absurd hm (by simp)) w
      have a := hw x0 hx0A
      have b := hw xj hxjA
      have b' : neg i xj = false := by simp [neg, bit, hxj, hi]
      have a' : neg i x0 = true := by simp [neg, bit, hx0]
      rw [b'] at b
      rw [a'] at a
      have := m a
      rw [b] at this
      exact Bool.false_ne_true this
    refine ⟨cov, ?_⟩
    let T := (Finset.univ \ S).disjSum (E.disjSum (E.disjSum E))
    have hT : T.card = (Finset.univ \ S).card + (E.card + (E.card + E.card)) := by
      simp [T, Finset.card_disjSum]
    have hneed : ∀ t ∈ T, IsNeed E (tagOf t) ∧ col bit (tagOf t) ∈ need := by
      intro t ht
      rcases t with i | e | e | e <;> simp only [T, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at ht
      · exact ⟨trivial, negNeed i⟩
      · exact ⟨ht, lowNeed e ht⟩
      · exact ⟨ht, fwdNeed e ht⟩
      · exact ⟨ht, bwdNeed e ht⟩
    have hle := countLB (A) L ⟨G, o⟩ T
      (fun t => col bit (tagOf t))
      (fun t ht => hall _ (hneed t ht).2)
      (by
        intro t ht g hg
        obtain ⟨t', hv, heq, hok⟩ := inputTag g hg
        have hne : tagOf t ≠ t' := by
          intro q
          subst q
          rcases t with i | e | e | e <;> simp only [T, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at ht
          · simp only [tagOf, InputOK] at hok
            simp at ht
            exact ht hok
          all_goals exact hok
        rw [heq]
        exact sep _ _ (hneed t ht).1 hv hne)
      (by
        intro t ht t' ht' hne
        have hv : Valid E (tagOf t') := by
          have := (hneed t' ht').1
          rcases t' with i | e | e | e <;> simpa [tagOf, IsNeed, Valid] using this
        exact sep _ _ (hneed t ht).1 hv (fun q => hne (tagInj _ _ q)))
    have : (⟨G, o⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = G.length := rfl
    omega
  · rintro ⟨hcov, hp⟩
    obtain ⟨G, hG, hlen, hneg, hedge⟩ := build L bit E S
      (fun i => memL _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))))
      (fun e he => by
        rw [← hsameStd e]
        exact memL _ (Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))))
      (fun e he => by
        rw [← hdiffStd e]
        exact memL _ (Or.inl (Or.inr ⟨e, he, rfl⟩)))
      (fun i hi => memL _ (Or.inr ⟨i, hi, rfl⟩))
      (fun K hSK hK => hclosed K hSK hK hcov)
    have hpos : 0 < L.length :=
      List.length_pos_of_mem (memL _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))))
    refine ⟨⟨G, 0⟩, hG.1, hG.2, by simp [PEqualNP.CircuitLowerBounds.Circuit.size]; omega, ?_, ?_⟩
    · show G.length ≤ p
      omega
    · intro f hf
      simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf
      rcases hf with ((⟨i, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
      · obtain ⟨j, hj, hv⟩ := hneg i
        exact ⟨j, hj, fun x _ => hv x⟩
      · obtain ⟨j, hj, hv⟩ := (hedge e he).1
        exact ⟨j, hj, fun x _ => hv x⟩
      · obtain ⟨j, hj, hv⟩ := (hedge e he).2.1
        exact ⟨j, hj, fun x _ => hv x⟩
      · obtain ⟨j, hj, hv⟩ := (hedge e he).2.2
        exact ⟨j, hj, fun x _ => hv x⟩
