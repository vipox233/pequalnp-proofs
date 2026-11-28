import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33611

lemma selectorRepairExists {k : ℕ} (E : Finset (Fin k → ZMod 2))
    (h : (Fin k → ZMod 2) → ZMod 2) :
    ∃ T : Finset (Fin k → ZMod 2), T ⊆ E ∧
      ∃ f : (Fin k → ZMod 2) → ZMod 2,
        (∃ (b : ZMod 2) (l : Fin k → ZMod 2) (M : Fin k → Fin k → ZMod 2),
          ∀ u, f u = b + dotProduct l u + ∑ i, ∑ v, M i v * u i * u v) ∧
        ∀ s ∈ E, h s = f s + (if s ∈ T then 1 else 0) := by
  classical
  let T := E.filter (fun s => h s = 1)
  refine ⟨T, Finset.filter_subset _ _, fun _ => 0, ?_, ?_⟩
  · exact ⟨0, 0, 0, by simp [dotProduct]⟩
  · intro s hs
    have bits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases bits (h s) with hv | hv <;> simp [T, hs, hv]

theorem existsMinimalRepair {S : Type*} (repairs : Finset S → Prop)
    (someRepair : ∃ T, repairs T) :
    ∃ T, repairs T ∧ ∀ U : Finset S, U ⊂ T → ¬repairs U := by
  classical
  have sizes : ∃ k : ℕ, ∃ T : Finset S, repairs T ∧ T.card = k := by
    obtain ⟨T, hT⟩ := someRepair
    exact ⟨T.card, T, hT, rfl⟩
  obtain ⟨T, hT, cardT⟩ := Nat.find_spec sizes
  refine ⟨T, hT, ?_⟩
  intro U strict hU
  have least : Nat.find sizes ≤ U.card := Nat.find_min' sizes ⟨U, hU, rfl⟩
  exact (Nat.not_lt_of_ge (cardT.le.trans least)) (Finset.card_lt_card strict)

theorem positiveRepairCost {S : Type*} (E : Finset S) (repairs : Finset S → Prop)
    (someRepair : ∃ T, repairs T) (inside : ∀ T, repairs T → T ⊆ E)
    (w z : S → ℝ) (weight : ∀ s ∈ E, 0 < w s) (nonneg : ∀ s ∈ E, 0 ≤ z s)
    (hit : ∀ T : Finset S, repairs T → (∀ U : Finset S, U ⊂ T → ¬repairs U) →
      1 ≤ 2 * ∑ s ∈ T, z s) : 0 < ∑ s ∈ E, w s * z s := by
  obtain ⟨T, hT, minimal⟩ := existsMinimalRepair repairs someRepair
  have score := hit T hT minimal
  have positive : ∃ s ∈ T, 0 < z s := by
    by_contra! nonpos
    have hsum : (∑ s ∈ T, z s) ≤ 0 := Finset.sum_nonpos nonpos
    linarith
  obtain ⟨s, hs, hz⟩ := positive
  have he : s ∈ E := inside T hT hs
  exact Finset.sum_pos' (fun a ha => mul_nonneg (weight a ha).le (nonneg a ha))
    ⟨s, he, mul_pos (weight s he) hz⟩

theorem signSum_eq_card_iff {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (∑ i, if P i then (1 : ℝ) else -1) = Fintype.card ι ↔ ∀ i, P i := by
  constructor
  · intro h
    by_contra! hbad
    obtain ⟨j, hj⟩ := hbad
    have bound (i : ι) : (if P i then (1 : ℝ) else -1) ≤ 1 := by
      split <;> norm_num
    have strict : (∑ i, if P i then (1 : ℝ) else -1) < ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_lt_sum (fun i _ => bound i)
      exact ⟨j, Finset.mem_univ j, by simp [hj]⟩
    simp [h] at strict
  · intro h
    simp [h]

theorem doubleSignSum_eq_card_iff {X B : Type*} [Fintype X] [Fintype B]
    (P : X → B → Prop) [∀ x, DecidablePred (P x)] :
    (∑ x, ∑ b, if P x b then (1 : ℝ) else -1) = (Fintype.card X : ℝ) * Fintype.card B
      ↔ ∀ x b, P x b := by
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, Prod.forall] using
    signSum_eq_card_iff (fun z : X × B => P z.1 z.2)

theorem normalizedScore_eq_one_iff (n t : ℕ)
    (P : (Fin n → ZMod 2) → (Fin t → ZMod 2) → Prop) [∀ x, DecidablePred (P x)] :
    ((∑ x, ∑ b, if P x b then (1 : ℝ) else -1) / 2 ^ (n+t) = 1) ↔ ∀ x b, P x b := by
  rw [div_eq_iff (by positivity : (2 : ℝ) ^ (n+t) ≠ 0), one_mul]
  simpa [Fintype.card_fun, ZMod.card, pow_add] using doubleSignSum_eq_card_iff P

lemma selectorCoverCostPositive {k : ℕ} (E : Finset (Fin k → ZMod 2))
    (h : (Fin k → ZMod 2) → ZMod 2) (w z : (Fin k → ZMod 2) → ℝ)
    (weight : ∀ s ∈ E, 0 < w s) (nonneg : ∀ s ∈ E, 0 ≤ z s) :
    let repairs := fun (T : Finset (Fin k → ZMod 2)) => T ⊆ E ∧
      ∃ f : (Fin k → ZMod 2) → ZMod 2,
        (∃ (b : ZMod 2) (l : Fin k → ZMod 2) (M : Fin k → Fin k → ZMod 2),
          ∀ u, f u = b + dotProduct l u + ∑ i, ∑ v, M i v * u i * u v) ∧
        ∀ s ∈ E, h s = f s + (if s ∈ T then 1 else 0)
    (∀ T : Finset (Fin k → ZMod 2), repairs T → (∀ U, U ⊂ T → ¬repairs U) →
      1 ≤ 2 * ∑ s ∈ T, z s) → 0 < ∑ s ∈ E, w s * z s := by
  intro repairs hit
  exact positiveRepairCost E repairs (selectorRepairExists E h) (fun _ hT => hT.1)
    w z weight nonneg hit

end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611

namespace HullFourier

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F
abbrev Form (n : ℕ) := Vec n →ₗ[F] F

def bit (b : Bool) : F := if b then 1 else 0

def IsAffine {Z : Type*} {m : ℕ} (f : Z → Vec m → Bool) : Prop :=
  ∃ (l : Form m) (a : Z → F), ∀ z x, bit (f z x) = l x + a z

def goodGate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

noncomputable def charged (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def gateValue (g : Gate) (W : Z → Vec m → List Bool) (z : Z) (x : Vec m) : Bool :=
  g.op.eval (g.inputs.map fun i => (W z x).getD i false)

theorem charged_eq_true (g : Gate) :
    charged g = true ↔ (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  unfold charged
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

private theorem gateAffine_const {Z : Type*} {m : ℕ} (f : Z → Bool) :
    IsAffine (fun z (_ : Vec m) => f z) := by
  exact ⟨0, fun z => bit (f z), by simp⟩

private theorem gateBit_not (a : Bool) :
    bit (GateOp.not.eval [a]) = 1 + bit a := by
  cases a <;> decide

private theorem gateBit_mod1 (a : Bool) :
    bit ((GateOp.mod 2).eval [a]) = 1 + bit a := by
  cases a <;> decide

private theorem gateBit_mod2 (a b : Bool) :
    bit ((GateOp.mod 2).eval [a, b]) = 1 + bit a + bit b := by
  cases a <;> cases b <;> decide

private theorem gateBit_and1 (a : Bool) : GateOp.and.eval [a] = a := by
  cases a <;> rfl

private theorem gateBit_or1 (a : Bool) : GateOp.or.eval [a] = a := by
  cases a <;> rfl

theorem gate_affine {Z : Type*} {m : ℕ} {g : Gate} {W : Z → Vec m → List Bool}
    (hg : goodGate g) (hc : charged g = false)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    IsAffine (gateValue g W) := by
  rcases g with ⟨op, inputs⟩
  rcases hg with ⟨hlen, hop⟩
  change inputs.length ≤ 2 at hlen
  have hnot : ¬ ((op = .and ∨ op = .or) ∧ inputs.length = 2) := by
    intro h
    have ht := (charged_eq_true ⟨op, inputs⟩).2 h
    rw [hc] at ht
    contradiction
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ inputs.length = 1) at hop
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · exact gateAffine_const (fun _ => op.eval [])
  · rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩
    · change IsAffine (fun z x => GateOp.and.eval [(W z x).getD i false])
      simpa only [gateBit_and1] using hW i
    · change IsAffine (fun z x => GateOp.or.eval [(W z x).getD i false])
      simpa only [gateBit_or1] using hW i
    · obtain ⟨l, a, ha⟩ := hW i
      refine ⟨l, fun z => 1 + a z, fun z x => ?_⟩
      change bit ((GateOp.mod 2).eval [(W z x).getD i false]) = _
      rw [gateBit_mod1, ha]
      ring
    · obtain ⟨l, a, ha⟩ := hW i
      refine ⟨l, fun z => 1 + a z, fun z x => ?_⟩
      change bit (GateOp.not.eval [(W z x).getD i false]) = _
      rw [gateBit_not, ha]
      ring
  · have hi : (op = .and ∨ op = .or) → False := fun h => hnot ⟨h, rfl⟩
    rcases hop with h | h | rfl | ⟨_, hn⟩
    · exact (hi (Or.inl h)).elim
    · exact (hi (Or.inr h)).elim
    · obtain ⟨l, a, ha⟩ := hW i
      obtain ⟨r, c, hc⟩ := hW j
      refine ⟨l + r, fun z => 1 + a z + c z, fun z x => ?_⟩
      change bit ((GateOp.mod 2).eval [(W z x).getD i false, (W z x).getD j false]) = _
      rw [gateBit_mod2, ha, hc, LinearMap.add_apply]
      ring
    · simp at hn
  · simp only [List.length_cons] at hlen
    omega

private theorem gateBit_and2 (a b : Bool) :
    bit (GateOp.and.eval [a, b]) = bit a * bit b + 0 * (bit a + bit b) := by
  cases a <;> cases b <;> decide

private theorem gateBit_or2 (a b : Bool) :
    bit (GateOp.or.eval [a, b]) = bit a * bit b + 1 * (bit a + bit b) := by
  cases a <;> cases b <;> decide

private theorem gateBinary_cut {Z : Type*} {n : ℕ} {f g : Z → Vec (n + 1) → Bool}
    {v : Z → Vec (n + 1) → Bool} {ε : F}
    (hv : ∀ z x, bit (v z x) = bit (f z x) * bit (g z x) + ε * (bit (f z x) + bit (g z x)))
    (hf : IsAffine f) (hg : IsAffine g) :
    ∃ ℓ : Form (n + 1), ∃ c : Z → F, ℓ ≠ 0 ∧
      ∀ b : F, ∃ l : Form (n + 1), ∃ a : Z → F,
        ∀ z x, ℓ x + c z = b → bit (v z x) = l x + a z := by
  obtain ⟨l, a, ha⟩ := hf
  obtain ⟨r, c, hc⟩ := hg
  by_cases hl : l = 0
  · by_cases hr : r = 0
    · let p : Form (n + 1) := LinearMap.proj (0 : Fin (n + 1))
      have hp : p ≠ 0 := by
        intro h
        have he := DFunLike.congr_fun h (fun _ => (1 : F))
        have hf : (1 : F) = 0 := he
        exact one_ne_zero hf
      refine ⟨p, fun _ => 0, hp, fun _ => ⟨0, fun z => a z * c z + ε * (a z + c z), ?_⟩⟩
      intro z x _
      simp [hv, ha, hc, hl, hr]
    · refine ⟨r, c, hr, fun b => ⟨(b + ε) • l, fun z => a z * b + ε * (a z + b), ?_⟩⟩
      intro z x h
      rw [hv, ha, hc, h, LinearMap.smul_apply, smul_eq_mul]
      ring
  · refine ⟨l, a, hl, fun b => ⟨(b + ε) • r, fun z => b * c z + ε * (b + c z), ?_⟩⟩
    intro z x h
    rw [hv, ha, hc, h, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem gate_affine_on_cut {Z : Type*} {m : ℕ} {g : Gate} {W : Z → Vec (m + 1) → List Bool}
    (hc : charged g = true)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    ∃ ℓ : Form (m + 1), ∃ c : Z → F, ℓ ≠ 0 ∧
      ∀ b : F, ∃ l : Form (m + 1), ∃ a : Z → F,
        ∀ z x, ℓ x + c z = b → bit (gateValue g W z x) = l x + a z := by
  obtain ⟨hop, hlen⟩ := (charged_eq_true g).1 hc
  rcases g with ⟨op, inputs⟩
  change op = .and ∨ op = .or at hop
  change inputs.length = 2 at hlen
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · rcases hop with rfl | rfl
    · exact gateBinary_cut (fun z x => gateBit_and2 _ _) (hW i) (hW j)
    · exact gateBinary_cut (fun z x => gateBit_or2 _ _) (hW i) (hW j)
  · simp only [List.length_cons] at hlen
    omega

theorem wires_extend {Z : Type*} {m n : ℕ} {W : Z → Vec m → List Bool}
    {v : Z → Vec m → Bool} (hlen : ∀ z x, (W z x).length = n)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false))
    (hv : IsAffine v) (i : ℕ) :
    IsAffine (fun z x => (W z x ++ [v z x]).getD i false) := by
  by_cases hi : i < n
  · have h : (fun z x => (W z x ++ [v z x]).getD i false) =
        (fun z x => (W z x).getD i false) := by
      funext z x
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa [hlen] using hi)]
    simpa only [h] using hW i
  · by_cases he : i = n
    · subst i
      have h : (fun z x => (W z x ++ [v z x]).getD n false) = v := by
        funext z x
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen])]
        simp [hlen]
      simpa only [h] using hv
    · have h : (fun z x => (W z x ++ [v z x]).getD i false) = (fun _ _ => false) := by
        funext z x
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hlen]; omega)]
        rfl
      rw [h]
      exact gateAffine_const (fun _ => false)

private theorem cut_pivot {m : ℕ} (ℓ : Form (m + 1)) (hℓ : ℓ ≠ 0) :
    ∃ j : Fin (m + 1), ℓ (Pi.single j 1) = 1 := by
  by_contra! h
  apply hℓ
  apply LinearMap.pi_ext
  intro j a
  have hj : ℓ (Pi.single j 1) = 0 := by
    exact (show ∀ t : F, t ≠ 1 → t = 0 by decide) _ (h j)
  have ha : (Pi.single j a : Vec (m + 1)) = a • Pi.single j 1 := by
    ext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Pi.single_eq_of_ne hi]
  rw [ha, map_smul, hj, smul_zero, LinearMap.zero_apply]

theorem cut_exists_split {m : ℕ} (ℓ : Form (m + 1)) (hℓ : ℓ ≠ 0) :
    ∃ E : (F × Vec m) ≃ₗ[F] Vec (m + 1), ∀ e x, ℓ (E (e, x)) = e := by
  classical
  obtain ⟨j, hj⟩ := cut_pivot ℓ hℓ
  let w : Vec (m + 1) := Pi.single j 1
  change ℓ w = 1 at hj
  let u := finSuccAboveEquiv j
  let drop : Vec (m + 1) →ₗ[F] Vec m :=
    { toFun := fun v i => v (u i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p := ℓ.prod drop
  have hdw : drop w = 0 := by
    ext i
    exact Pi.single_eq_of_ne (u i).2 _
  have hinj : Function.Injective p := by
    intro x y hxy
    have hl : ℓ x = ℓ y := congrArg Prod.fst hxy
    have hd : drop x = drop y := congrArg Prod.snd hxy
    have hxy' : x - y = (x j - y j) • w := by
      ext i
      by_cases hi : i = j
      · subst i
        simp [w]
      · have he : x i = y i := by
          have h := congrFun hd (u.symm ⟨i, hi⟩)
          change x (u (u.symm ⟨i, hi⟩)).1 = y (u (u.symm ⟨i, hi⟩)).1 at h
          simpa only [Equiv.apply_symm_apply] using h
        simp [w, Pi.single_eq_of_ne hi, he]
    have hs := congrArg ℓ hxy'
    simp [map_sub, hl, hj] at hs
    apply sub_eq_zero.mp
    rw [hxy', ← hs, zero_smul]
  have hsurj : Function.Surjective p := by
    rintro ⟨e, x⟩
    let base : Vec (m + 1) := fun i => if hi : i = j then 0 else x (u.symm ⟨i, hi⟩)
    have hbase : drop base = x := by
      ext i
      change base (u i).1 = x i
      simp [base, dite_eq_right (u i).2]
    refine ⟨base + (e - ℓ base) • w, Prod.ext ?_ ?_⟩
    · change ℓ (base + (e - ℓ base) • w) = e
      simp [hj]
    · change drop (base + (e - ℓ base) • w) = x
      simp [hdw, hbase]
  let E := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩
  refine ⟨E.symm, fun e x => ?_⟩
  exact congrArg Prod.fst (E.apply_symm_apply (e, x))

private def walshSign (x : F) : ℤ := if x = 0 then 1 else -1

private theorem walshSign_add_one (x : F) : walshSign (x + 1) = -walshSign x := by
  fin_cases x <;> decide

private theorem walshSign_agreement (q : Bool) (x : F) :
    walshSign (bit q - x) = (if q = decide (x = 1) then 2 else 0) - 1 := by
  cases q <;> fin_cases x <;> decide

private theorem walshSign_natAbs (x : F) : (walshSign x).natAbs = 1 := by
  fin_cases x <;> decide

private theorem walsh_eq_agreement {k : ℕ} (f : Vec k → Bool) (v : Vec k) :
    (∑ x : Vec k, walshSign (bit (f x) - dotProduct v x)) =
    2 * ((((Finset.univ : Finset (Vec k)).filter
      (fun x => f x = decide (dotProduct v x = 1))).card : ℕ) : ℤ) - (2:ℤ)^k := by
  simp_rw [walshSign_agreement]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp [ZMod.card, mul_comm]

open Classical in
private theorem walshSign_sum {m : ℕ} (g : Form m) (c : F) :
    (∑ y : Vec m, walshSign (c + g y)).natAbs = if g = 0 then 2^m else 0 := by
  classical
  by_cases hg : g = 0
  · simp [hg, ZMod.card, Int.natAbs_mul, walshSign_natAbs]
  · rw [ite_eq_right hg]
    have hex : ∃ w : Vec m, g w ≠ 0 := by
      by_contra! h
      exact hg (LinearMap.ext fun x => h x)
    obtain ⟨w, hw⟩ := hex
    have hw' : g w = 1 := by
      have h01 (x : F) : x = 0 ∨ x = 1 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h01 (g w) with h | h
      · exact (hw h).elim
      · exact h
    have h := Equiv.sum_comp (Equiv.addRight w) fun y : Vec m => walshSign (c + g y)
    change (∑ y : Vec m, walshSign (c + g (y + w))) =
      ∑ y : Vec m, walshSign (c + g y) at h
    simp_rw [map_add, hw', ← add_assoc, walshSign_add_one, Finset.sum_neg_distrib] at h
    have hz : (∑ y : Vec m, walshSign (c + g y)) = 0 := by omega
    simp [hz]

private def walshRestriction {k m : ℕ} (L : Vec m →ₗ[F] Vec k) : Vec k →ₗ[F] Form m :=
  (Module.Dual.transpose L).comp (dotProductEquiv F (Fin k)).toLinearMap

private theorem walshRestriction_apply {k m : ℕ} (L : Vec m →ₗ[F] Vec k)
    (v : Vec k) (y : Vec m) : walshRestriction L v y = dotProduct v (L y) := rfl

private theorem walshRestriction_surjective {k m : ℕ} (L : Vec m →ₗ[F] Vec k)
    (R : Vec k →ₗ[F] Vec m) (hRL : Function.LeftInverse R L) :
    Function.Surjective (walshRestriction L) := by
  intro ℓ
  refine ⟨(dotProductEquiv F (Fin k)).symm (ℓ.comp R), ?_⟩
  apply LinearMap.ext
  intro y
  rw [walshRestriction_apply]
  change dotProductEquiv F (Fin k) ((dotProductEquiv F (Fin k)).symm (ℓ.comp R)) (L y) = ℓ y
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, hRL y]

private theorem walshRestriction_ker_finrank {k b : ℕ} (hb : b ≤ k)
    (L : Vec (k-b) →ₗ[F] Vec k) (R : Vec k →ₗ[F] Vec (k-b))
    (hRL : Function.LeftInverse R L) : Module.finrank F (LinearMap.ker (walshRestriction L)) = b := by
  have hdim (n : ℕ) : Module.finrank F (Vec n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h := (walshRestriction L).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (walshRestriction_surjective L R hRL), finrank_top,
    ← (dotProductEquiv F (Fin (k-b))).finrank_eq, hdim, hdim] at h
  omega

theorem walshCover {k b : ℕ} {Z : Type*} (hb : b ≤ k) (f : Z → Vec k → Bool)
    (L : Fin (2^b) → Vec (k-b) →ₗ[F] Vec k)
    (R : Fin (2^b) → Vec k →ₗ[F] Vec (k-b))
    (hRL : ∀ i, Function.LeftInverse (R i) (L i))
    (p : Fin (2^b) → Z → Vec k) (ℓ : Fin (2^b) → Form (k-b))
    (a : Fin (2^b) → Z → F)
    (hf : ∀ i z y, bit (f z (p i z + L i y)) = ℓ i y + a i z)
    (hsum : ∀ z (h : Vec k → ℤ), ∑ x, h x = ∑ i, ∑ y, h (p i z + L i y)) :
    ∃ (D : Fin (2^b) → Submodule F (Vec k)) (aa : Fin (2^b) → Vec k),
      (∀ i, Module.finrank F (D i) = b) ∧
      ∀ z v,
        let H := ((Finset.univ : Finset (Vec k)).filter
          (fun x => f z x = decide (dotProduct v x = 1))).card
        2^b * (2 * (H : ℤ) - (2:ℤ)^k).natAbs ≤
          2^k * ((Finset.univ : Finset (Fin (2^b))).filter
            (fun i => @decide (v-aa i ∈ D i) (Classical.propDecidable _))).card := by
  classical
  choose aa haa using fun i => walshRestriction_surjective (L i) (R i) (hRL i) (ℓ i)
  refine ⟨fun i => LinearMap.ker (walshRestriction (L i)), aa,
    fun i => walshRestriction_ker_finrank hb (L i) (R i) (hRL i), ?_⟩
  intro z v
  dsimp only
  rw [← walsh_eq_agreement (f z) v, hsum z]
  let W (i : Fin (2^b)) : ℤ :=
    ∑ y, walshSign (bit (f z (p i z + L i y)) - dotProduct v (p i z + L i y))
  change 2^b * (∑ i, W i).natAbs ≤ _
  have hW (i : Fin (2^b)) : (W i).natAbs =
      if v - aa i ∈ LinearMap.ker (walshRestriction (L i)) then 2^(k-b) else 0 := by
    have hterm (y : Vec (k-b)) :
        bit (f z (p i z + L i y)) - dotProduct v (p i z + L i y) =
          (a i z - dotProduct v (p i z)) + (ℓ i - walshRestriction (L i) v) y := by
      rw [hf, dotProduct_add, LinearMap.sub_apply, walshRestriction_apply]
      abel
    simp_rw [W, hterm, walshSign_sum]
    have hc : ℓ i - walshRestriction (L i) v = 0 ↔
        v - aa i ∈ LinearMap.ker (walshRestriction (L i)) := by
      rw [LinearMap.mem_ker, map_sub, haa, sub_eq_zero, sub_eq_zero]
      exact eq_comm
    simp only [hc]
  have hbound : (∑ i, W i).natAbs ≤ ∑ i, (W i).natAbs := by
    exact Int.natAbs_sum_le _ _
  refine (Nat.mul_le_mul_left _ hbound).trans_eq ?_
  simp_rw [hW, decide_eq_true_eq]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm _ (2^(k-b)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le hb]
  rfl

private structure Frame (k : ℕ) (Z : Type) (m : ℕ) where
  linear : Vec m →ₗ[F] Vec k
  retract : Vec k →ₗ[F] Vec m
  left_inv : Function.LeftInverse retract linear
  offset : Z → Vec k

private def Frame.point (T : Frame k Z m) (z : Z) (x : Vec m) : Vec k :=
  T.offset z + T.linear x

private def cutLinear (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) : Vec m →ₗ[F] Vec (m+1) :=
  E.toLinearMap.comp (LinearMap.inr F F (Vec m))

private theorem split_add (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (a : F) (x : Vec m) :
    E (a,x) = E (a,0) + E (0,x) := by
  rw [← map_add]
  simp

private def Frame.cut (T : Frame k Z (m+1)) (E : (F × Vec m) ≃ₗ[F] Vec (m+1))
    (c : Z → F) (e : F) : Frame k Z m where
  linear := T.linear.comp (cutLinear E)
  retract := (LinearMap.snd F F (Vec m)).comp (E.symm.toLinearMap.comp T.retract)
  left_inv := by
    intro x
    change (E.symm (T.retract (T.linear (E (0,x))))).2 = x
    rw [T.left_inv,E.symm_apply_apply]
  offset z := T.offset z + T.linear (E (e+c z,0))

private theorem Frame.cut_point (T : Frame k Z (m+1)) (E : (F × Vec m) ≃ₗ[F] Vec (m+1))
    (c : Z → F) (e : F) (z : Z) (x : Vec m) :
    (T.cut E c e).point z x = T.point z (E (e+c z,x)) := by
  change T.offset z + T.linear (E (e+c z,0)) + T.linear (E (0,x)) = _
  simp only [Frame.point, split_add E (e+c z) x, map_add, add_assoc]

private theorem sum_cut (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (a : F)
    (f : Vec (m+1) → ℤ) :
    (∑ q, f q) = ∑ e : F, ∑ x : Vec m, f (E (e+a,x)) := by
  let Q := (Equiv.prodCongr (Equiv.addRight a) (Equiv.refl (Vec m))).trans E.toEquiv
  rw [← Equiv.sum_comp Q f]
  rw [Fintype.sum_prod_type]
  rfl

private def consEquiv (m : ℕ) : F × Vec m ≃ Vec (m+1) where
  toFun p := Fin.cons p.1 p.2
  invFun q := (q 0, Fin.tail q)
  left_inv p := by simp
  right_inv q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem sum_cons (f : Vec (m+1) → ℤ) :
    (∑ q, f q) = ∑ e : F, ∑ x : Vec m, f (Fin.cons e x) := by
  rw [← Equiv.sum_comp (consEquiv m) f, Fintype.sum_prod_type]
  rfl

private theorem affine_reparam (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (c : Z → F)
    (e : F) (l : Form (m+1)) (a : Z → F)
    (f : Z → Vec (m+1) → Bool)
    (h : ∀ z y, bit (f z (E (e+c z,y))) = l (E (e+c z,y)) + a z) :
    IsAffine (fun z y => f z (E (e+c z,y))) := by
  refine ⟨l.comp (cutLinear E),fun z => l (E (e+c z,0)) + a z, ?_⟩
  intro z y
  rw [h,split_add E (e+c z) y,map_add]
  change l (E (e+c z,0)) + l (E (0,y)) + a z = l (E (0,y)) + (l (E (e+c z,0)) + a z)
  ac_rfl

private def step (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def finalValue (gs : List Gate) (W : Z → Vec k → List Bool)
    (out : ℕ) (z : Z) (x : Vec k) : Bool :=
  (gs.foldl (fun w g => step g w) (W z x)).getD out false

private structure Cell (k : ℕ) (Z : Type) (m : ℕ) extends Frame k Z m where
  slope : Form m
  phase : Z → F

private theorem partition (gs : List Gate) (hg : ∀ g ∈ gs, goodGate g)
    (s : ℕ) (hs : gs.countP charged = s) (T : Frame k Z (m+s))
    (W : Z → Vec k → List Bool) (out n : ℕ) (hwlength : ∀ z x, (W z x).length = n)
    (hwaffine : ∀ i : ℕ, IsAffine (fun z x => (W z (T.point z x)).getD i false)) :
    ∃ cells : Vec s → Cell k Z m,
      (∀ i z x, bit (finalValue gs W out z ((cells i).toFrame.point z x)) =
        (cells i).slope x + (cells i).phase z) ∧
      ∀ z (f : Vec k → ℤ),
        (∑ x, f (T.point z x)) = ∑ i, ∑ x, f ((cells i).toFrame.point z x) := by
  induction gs generalizing s n W out with
  | nil =>
      have hzero : s = 0 := by simpa using hs.symm
      clear hs
      subst s
      obtain ⟨l,a,ha⟩ := hwaffine out
      refine ⟨fun _ => ⟨T,l,a⟩, ?_, ?_⟩
      · intro i z x
        exact ha z x
      · intro z f
        have hcard : Fintype.card (Vec 0) = 1 := by simp [Vec,F]
        change (∑ x, f (T.point z x)) = ∑ _ : Vec 0, ∑ x, f (T.point z x)
        simp only [Finset.sum_const,Finset.card_univ,hcard,one_nsmul]
  | cons g gs ih =>
      have hgate := hg g (by simp)
      have hgs (a : Gate) (ha : a ∈ gs) := hg a (by simp [ha])
      let W' z x := step g (W z x)
      have hW' (z : Z) (x : Vec k) : (W' z x).length = n+1 := by
        simp [W',step,hwlength]
      cases hch : charged g
      · have hs' : gs.countP charged = s := by simpa [List.countP_cons,hch] using hs
        let localW := fun z x => W z (T.point z x)
        have ha := gate_affine (g := g) (W := localW) hgate hch hwaffine
        have hall : ∀ i, IsAffine (fun z x => (W' z (T.point z x)).getD i false) :=
          fun i => wires_extend (W := localW) (fun z x => hwlength z _) hwaffine ha i
        obtain ⟨cells,hcells,hsum⟩ := ih hgs s hs' T W' out (n+1) hW' hall
        exact ⟨cells,hcells,hsum⟩
      · have hs' : gs.countP charged + 1 = s := by simpa [List.countP_cons,hch] using hs
        cases s with
        | zero => omega
        | succ s =>
          have htail : gs.countP charged = s := by omega
          let localW := fun z x => W z (T.point z x)
          obtain ⟨l,c,hl,hcut⟩ := gate_affine_on_cut (g := g) (W := localW) hch hwaffine
          obtain ⟨E,hE⟩ := cut_exists_split l hl
          let C (e : F) := T.cut E c e
          have hchild (e : F) :
              ∀ i, IsAffine (fun z x => (W' z ((C e).point z x)).getD i false) := by
            let childW := fun z x => W z ((C e).point z x)
            have ha (i : ℕ) : IsAffine (fun z x => (childW z x).getD i false) := by
              obtain ⟨l,a,ha⟩ := hwaffine i
              have hv := affine_reparam E c e l a
                (fun z x => (W z (T.point z x)).getD i false) (fun z y => ha z _)
              simpa only [childW,C,Frame.cut_point] using hv
            obtain ⟨l',a',hcut'⟩ := hcut e
            have hv := affine_reparam E c e l' a' (gateValue g localW) (by
              intro z y
              apply hcut'
              rw [hE]
              exact (by decide : ∀ x y : F, x+y+y=x) _ _)
            have hb : IsAffine (gateValue g childW) := by
              change IsAffine (fun z y => gateValue g childW z y)
              simpa only [gateValue,childW,C,Frame.cut_point,localW] using hv
            exact wires_extend (W := childW) (fun z x => hwlength z _) ha hb
          have hbranch (e : F) := ih hgs s htail (C e) W' out (n+1) hW' (hchild e)
          choose cells he hsum using hbranch
          refine ⟨(fun i : Vec (s+1) => cells (i 0) (Fin.tail i)),?_,?_⟩
          · intro i z x
            exact he _ _ z x
          · intro z f
            calc
              (∑ x, f (T.point z x)) =
                  ∑ e : F, ∑ x, f ((C e).point z x) := by
                erw [sum_cut E (c z) (fun x => f (T.point z x))]
                apply Finset.sum_congr rfl
                intro e _
                apply Finset.sum_congr rfl
                intro x _
                rw [show (C e).point z x = T.point z (E (e+c z,x)) from T.cut_point E c e z x]
              _ = ∑ e : F, ∑ i : Vec s, ∑ x, f ((cells e i).toFrame.point z x) := by
                exact Finset.sum_congr rfl fun e _ => hsum e z f
              _ = ∑ i : Vec (s+1), ∑ x, f ((cells (i 0) (Fin.tail i)).toFrame.point z x) := by
                rw [sum_cons]
                simp

private def inputs (z : Fin t → Bool) (x : Vec k) : List Bool :=
  List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z

private theorem bit_decide (x : F) : bit (decide (x = 1)) = x :=
  (by decide : ∀ y : F, bit (decide (y = 1)) = y) x

private theorem inputs_affine {k t : ℕ} (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) (x : Vec k) => (inputs z x).getD i false) := by
  by_cases hi : i < k
  · refine ⟨LinearMap.proj ⟨i,hi⟩,fun _ => 0,?_⟩
    intro z x
    change bit ((inputs z x).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_ofFn, dite_eq_left hi, Option.getD_some, bit_decide,
      LinearMap.proj_apply, add_zero]
  · refine ⟨0,fun z => bit ((List.ofFn z).getD (i-k) false),?_⟩
    intro z x
    change bit ((inputs z x).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]

private def standard (h : m = k) : Frame k Z m := by
  subst m
  exact ⟨LinearMap.id,LinearMap.id,fun _ => rfl,fun _ => 0⟩

private theorem standard_affine {m k t : ℕ} (h : m = k) (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) x => (inputs z ((standard h).point z x)).getD i false) := by
  subst m
  simpa [standard,Frame.point] using inputs_affine (k := k) (t := t) i

private theorem standard_sum {m k : ℕ} {Z : Type} (h : m = k) (z : Z) (f : Vec k → ℤ) :
    (∑ x, f ((standard h).point z x)) = ∑ x, f x := by
  subst m
  simp [standard,Frame.point]

private def boundAt (b : ℕ) (f : Z → Vec k → Bool) : Prop :=
  ∃ (D : Fin (2^b) → Submodule F (Vec k)) (a : Fin (2^b) → Vec k),
    (∀ i, Module.finrank F (D i) = b) ∧
    ∀ z v,
      let H := ((Finset.univ : Finset (Vec k)).filter (fun x =>
        f z x = decide (dotProduct v x = 1))).card
      2^b * (2*(H : ℤ)-(2:ℤ)^k).natAbs ≤
        2^k * ((Finset.univ : Finset (Fin (2^b))).filter (fun l =>
          @decide (v-a l ∈ D l) (Classical.propDecidable _))).card

private theorem fullCover (f : Z → Vec k → Bool) : boundAt k f := by
  classical
  refine ⟨fun _ => ⊤,fun _ => 0,fun i => ?_,?_⟩
  · rw [finrank_top, Module.finrank_fin_fun]
  · intro z v
    dsimp only
    rw [← walsh_eq_agreement (f z) v]
    have h : (∑ x : Vec k, walshSign (bit (f z x) - dotProduct v x)).natAbs ≤ 2^k := by
      calc
        _ ≤ ∑ x : Vec k, (walshSign (bit (f z x) - dotProduct v x)).natAbs :=
          Int.natAbs_sum_le _ _
        _ = _ := by simp [walshSign_natAbs,ZMod.card]
    simpa [Submodule.mem_top, Fintype.card_fin] using Nat.mul_le_mul_left (2^k) h

private theorem circuit_cover {k t s : ℕ} (C : Circuit) (hs : C.gates.countP charged = s)
    (hle : s ≤ k) (hgood : ∀ g ∈ C.gates, goodGate g) :
    boundAt s (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x)) := by
  classical
  let m := k-s
  have hm : m+s=k := Nat.sub_add_cancel hle
  let T : Frame k (Fin t → Bool) (m+s) := standard hm
  obtain ⟨C₀,hC,hsum⟩ := partition C.gates hgood s hs T inputs C.output (k+t)
    (by intro z x; simp [inputs]) (fun i => standard_affine hm i)
  let ind : Vec s ≃ Fin (2^s) := Fintype.equivFinOfCardEq (by simp [Vec,F,ZMod.card])
  let C₁ (j : Fin (2^s)) := C₀ (ind.symm j)
  apply walshCover hle (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x))
    (fun i => (C₁ i).linear) (fun i => (C₁ i).retract) (fun i => (C₁ i).left_inv)
    (fun i => (C₁ i).offset) (fun i => (C₁ i).slope) (fun i => (C₁ i).phase)
  · intro i z y
    exact hC (ind.symm i) z y
  · intro z f
    calc
      (∑ x, f x) = ∑ x, f (T.point z x) := (standard_sum hm z f).symm
      _ = ∑ i, ∑ x, f ((C₀ i).toFrame.point z x) := hsum z f
      _ = ∑ i : Fin (2^s), ∑ x, f ((C₁ i).toFrame.point z x) :=
        (Equiv.sum_comp ind.symm _).symm

end HullFourier

open HullFourier PEqualNP.CircuitLowerBounds in
theorem hullFourierEstimate : (∀ (k t : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  let Z := Fin t → Bool
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) →
    let s := C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let b := min s k
    let I := Fin (2^b)
    ∃ (D : I → Submodule F V) (a : I → V), (∀ i, Module.finrank F (D i) = b) ∧
      ∀ (z : Z) (v : V),
        let H := ((Finset.univ : Finset V).filter (fun x =>
          C.eval (List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z) =
            decide (dotProduct v x = 1))).card
        2^b * (2*(H : ℤ)-(2:ℤ)^k).natAbs ≤
          2^k * ((Finset.univ : Finset I).filter (fun l =>
            @decide (v-a l ∈ D l) (Classical.propDecidable _))).card) := by

  classical
  intro k t
  dsimp only
  intro C _hread hgood
  change boundAt (min (C.gates.countP charged) k)
    (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x))
  by_cases h : C.gates.countP charged ≤ k
  · rw [Nat.min_eq_left h]
    exact circuit_cover C rfl h hgood
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact fullCover _

theorem promiseHullDimension {k t n : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) × (Fin t → ZMod 2))
    (E : Finset (Fin k → ZMod 2)) (o : Fin k → ZMod 2) (ho : o ∈ E)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (contain : ∀ s ∈ E, ∀ z, e.symm (s,z) - a ∈ U) :
    t + Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ((fun s => s-o) '' (↑E : Set (Fin k → ZMod 2)))) ≤
      Module.finrank (ZMod 2) U := by
  let S := Fin k → ZMod 2
  let D := Fin t → ZMod 2
  let W := Submodule.span (ZMod 2) ((fun s => s-o) '' (↑E : Set S))
  let f : S →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    e.symm.toLinearMap.comp (LinearMap.inl (ZMod 2) S D)
  have diff (s : S) (hs : s ∈ E) (z : D) : e.symm (s-o,z) ∈ U := by
    have hh := U.sub_mem (contain s hs z) (contain o ho 0)
    rw [sub_sub_sub_cancel_right] at hh
    have pair : ((s,z) - (o,0) : S × D) = (s-o,z) := Prod.ext rfl (sub_zero z)
    have linear : e.symm ((s,z) - (o,0)) = e.symm (s,z) - e.symm (o,0) :=
      map_sub e.symm (s,z) (o,0)
    rwa [← linear, pair] at hh
  have incl : W ≤ U.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    exact diff s hs 0
  let A : (W × D) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    e.symm.toLinearMap.comp (W.subtype.prodMap LinearMap.id)
  have hA (x : W × D) : A x ∈ U := by
    have hu : e.symm (x.1.val,0) ∈ U := incl x.1.property
    have hv : e.symm (0,x.2) ∈ U := by simpa using diff o ho x.2
    have hadd := U.add_mem hu hv
    rw [← e.symm.map_add] at hadd
    simpa [A] using hadd
  let B := A.codRestrict U hA
  have hi : Function.Injective B := by
    intro x y h
    have h' : ((x.1 : S),x.2) = ((y.1 : S),y.2) :=
      e.symm.injective (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (congrArg (fun p : S × D => p.1) h'))
      (congrArg (fun p : S × D => p.2) h')
  have result := LinearMap.finrank_le_finrank_of_injective hi
  rw [Module.finrank_prod, show Module.finrank (ZMod 2) D = t from Module.finrank_fin_fun _] at result
  exact (Nat.add_comm ..) ▸ result

theorem perfectPointwiseHullLower (k t : ℕ)
    (e : (Fin (k+t) → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) × (Fin t → ZMod 2))
    (Q : (Fin (k+t) → ZMod 2) → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (E : Finset (Fin k → ZMod 2)) (o : Fin k → ZMod 2) (ho : o ∈ E)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (budget : ℕ)
    (back : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*(k+t)) C)
    (good : ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (cost : C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ budget)
    (win : ∀ s ∈ E, ∀ x b, let y := e.symm (s,b)
      C.eval ((List.ofFn fun i => decide (x i = 1)) ++ (List.ofFn fun i => decide (y i = 1))) =
        decide (dotProduct x y + Q y + h s = 1)) :
    t + Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ((fun s => s-o) '' (↑E : Set (Fin k → ZMod 2)))) ≤ budget := by
  classical
  let n := k+t
  let c := C.gates.countP (fun g => @decide
    ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let r := min c n
  have hb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+n) C := by
    simpa only [two_mul, n] using back
  obtain ⟨U, a, dim, bound⟩ := hullFourierEstimate n n C hb good
  let j : Fin (2^r) := ⟨0, by positivity⟩
  apply (promiseHullDimension e E o ho (U j) (a j) ?_).trans
  · exact (dim j).le.trans ((Nat.min_le_left c n).trans cost)
  intro s hs b
  let y := e.symm (s,b)
  let z := fun i => decide (y i = 1)
  have tag : ∀ v q d : ZMod 2,
      (decide (v+q+d = 1) = decide (v = 1)) ↔ q+d=0 := by decide
  have agree (x : Fin n → ZMod 2) :
      (C.eval ((List.ofFn fun i => decide (x i = 1)) ++ List.ofFn z) =
        decide (dotProduct y x = 1)) ↔ Q y + h s = 0 := by
    change (C.eval ((List.ofFn fun i => decide (x i = 1)) ++
      (List.ofFn fun i => decide (y i = 1))) = _) ↔ _
    rw [win s hs x b, dotProduct_comm y x]
    exact tag _ _ _
  let A := (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x =>
    C.eval ((List.ofFn fun i => decide (x i = 1)) ++ List.ofFn z) =
      decide (dotProduct y x = 1))
  have casesA : A.card = 2^n ∨ A.card=0 := by
    by_cases hzero : Q y+h s=0
    · left
      have full : A = Finset.univ := Finset.eq_univ_of_forall (fun x =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, (agree x).2 hzero⟩)
      rw [full]
      simp [n, ZMod.card]
    · right
      apply Finset.card_eq_zero.mpr
      exact Finset.eq_empty_of_forall_notMem (fun x hx =>
        hzero ((agree x).1 (Finset.mem_filter.mp hx).2))
  have mag : (2*(A.card : ℤ)-(2:ℤ)^n).natAbs = 2^n := by
    rcases casesA with heq | heq
    · rw [heq, Nat.cast_pow, Nat.cast_ofNat]
      rw [show 2*(2:ℤ)^n-2^n=2^n by ring]
      simp
    · simp [heq]
  let I := Fin (2^r)
  let H := (Finset.univ : Finset I).filter (fun i => y - a i ∈ U i)
  have allCount := bound z y
  change 2^r * (2*(A.card : ℤ)-(2:ℤ)^n).natAbs ≤ 2^n * H.card at allCount
  rw [mag, Nat.mul_comm (2^r)] at allCount
  have ge : 2^r ≤ H.card := Nat.le_of_mul_le_mul_left allCount (by positivity)
  have hf : H = Finset.univ := Finset.eq_univ_of_card H (by
    apply le_antisymm (Finset.card_le_univ H)
    change Fintype.card (Fin (2^r)) ≤ H.card
    rw [Fintype.card_fin]
    exact ge)
  have hmem : j ∈ H := hf ▸ Finset.mem_univ j
  exact (Finset.mem_filter.mp hmem).2

theorem hullLowerFirstConjunct : (∀ k t : ℕ,
  let n := k+t
  let F := ZMod 2
  let S := Fin k → F
  let D := Fin t → F
  let V := Fin n → F
  let quad := fun (j : ℕ) (f : (Fin j → F) → F) =>
    ∃ (b : F) (l : Fin j → F) (M : Fin j → Fin j → F), ∀ u,
      f u = b + dotProduct l u + ∑ i, ∑ v, M i v * u i * u v
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let fits := fun (p : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ p
  let bits := fun (u : V) => List.ofFn (fun i => decide (u i = 1))
  ∀ (e : V ≃ₗ[F] S × D) (Q : V → F) (h : S → F), quad n Q →
    let score := fun (C : Circ) (s : S) =>
      (∑ x : V, ∑ b : D, let y := e.symm (s,b)
        if C.eval (bits x ++ bits y) = decide (dotProduct x y + Q y + h s = 1)
        then (1 : ℝ) else -1) / 2^(n+t)
    ∀ (E : Finset S) (o : S), o ∈ E →
      let W := Submodule.span F (Set.image (fun s : S => s-o) (↑E : Set S))
      let p := t + Module.finrank F W
      let perfect := fun (b : ℕ) => ∃ C : Circ, fits b C ∧ ∀ s ∈ E, score C s = 1
      ∀ b : ℕ, perfect b → p ≤ b) := by
  intro k t
  dsimp only
  intro e Q h _ E o ho b hb
  obtain ⟨C, ⟨back, good, cost⟩, wins⟩ := hb
  apply perfectPointwiseHullLower k t e Q h E o ho C b back good cost
  intro s hs
  exact (normalizedScore_eq_one_iff (k+t) t _).mp (wins s hs)

end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611

open scoped BigOperators

lemma finiteMatrixSaddle {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (A : I → J → ℝ) :
    ∃ (p : I → ℝ) (d : J → ℝ) (a : ℝ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ j, 0 ≤ d j) ∧ (∑ j, d j) = 1 ∧
      (∀ j, ∑ i, p i * A i j ≤ a) ∧ (∀ i, a ≤ ∑ j, d j * A i j) := by
  classical
  let f (x : I → ℝ) (y : J → ℝ) := ∑ i, ∑ j, x i * y j * A i j
  have hx : (stdSimplex ℝ I).Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary I)⟩
  have hy : (stdSimplex ℝ J).Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary J)⟩
  have cx (y : J → ℝ) : Continuous (fun x => f x y) := by unfold f; fun_prop
  have cy (x : I → ℝ) : Continuous (fun y => f x y) := by unfold f; fun_prop
  have ax (y : J → ℝ) : ConvexOn ℝ (stdSimplex ℝ I) (fun x => f x y) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro x _ z _ a b _ _ _
    apply le_of_eq
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have ay (x : I → ℝ) : ConcaveOn ℝ (stdSimplex ℝ J) (f x) := by
    refine ⟨convex_stdSimplex ℝ J, ?_⟩
    intro y _ z _ a b _ _ _
    apply le_of_eq
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨p, hp, d, hd, hs⟩ := Sion.exists_isSaddlePointOn hx (convex_stdSimplex ℝ I)
    (isCompact_stdSimplex ℝ I) (fun y _ => (cx y).continuousOn.lowerSemicontinuousOn)
    (fun y _ => (ax y).quasiconvexOn) (convex_stdSimplex ℝ J) hy (isCompact_stdSimplex ℝ J)
    (fun x _ => (cy x).continuousOn.upperSemicontinuousOn) (fun x _ => (ay x).quasiconcaveOn)
  refine ⟨p, d, f p d, hp.1, hp.2, hd.1, hd.2, ?_, ?_⟩
  · intro j
    have h := hs p hp _ (ite_eq_mem_stdSimplex ℝ j)
    simpa [f, mul_ite, ite_mul] using h
  · intro i
    have h := hs _ (ite_eq_mem_stdSimplex ℝ i) d hd
    simpa [f, mul_ite, ite_mul] using h

lemma finiteMatrixWeakDual {I J : Type*} [Fintype I] [Fintype J]
    (L : I → J → ℝ) (w : J → ℝ) (p : I → ℝ) (z : J → ℝ) (q : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : (∑ i, p i) = 1) (hz : ∀ j, 0 ≤ z j)
    (hc : ∀ i, 1 ≤ ∑ j, L i j * z j) (hf : ∀ j, ∑ i, p i * L i j ≤ q * w j) :
    1 ≤ q * ∑ j, w j * z j := by
  classical
  calc
    1 = ∑ i, p i * 1 := by simpa using hp1.symm
    _ ≤ ∑ i, p i * ∑ j, L i j * z j :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (hp i)
    _ = ∑ j, z j * ∑ i, p i * L i j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ j, z j * (q * w j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j) (hz j)
    _ = q * ∑ j, w j * z j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

lemma finiteMatrixCoverDual {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (L : I → J → ℝ) (w : J → ℝ) (hw : ∀ j, 0 < w j)
    (hL : ∀ i j, 0 ≤ L i j) (hpos : ∀ i, ∃ j, 0 < L i j) :
    let cover := fun z : J → ℝ => (∀ j, 0 ≤ z j) ∧ ∀ i, 1 ≤ ∑ j, L i j * z j
    let cost := fun z : J → ℝ => ∑ j, w j * z j
    let feasible := fun q : ℝ => ∃ p : I → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      ∀ j, ∑ i, p i * L i j ≤ q * w j
    ∃ z, cover z ∧ (∀ y, cover y → cost z ≤ cost y) ∧ 0 < cost z ∧
      ∀ q, feasible q ↔ 1 ≤ q * cost z := by
  classical
  dsimp only
  obtain ⟨p, d, a, hp, hp1, hd, hd1, hpr, hdu⟩ :=
    finiteMatrixSaddle (fun i j => L i j / w j)
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
    by_contra! hn
    have he (i) : p i = 0 := le_antisymm (hn i) (hp i)
    simp [he] at hp1
  obtain ⟨j, hj⟩ := hpos i
  have ha : 0 < a := by
    apply (mul_pos hi (div_pos hj (hw j))).trans_le
    exact (Finset.single_le_sum (fun l _ => mul_nonneg (hp l) (div_nonneg (hL l j)
      (hw j).le)) (Finset.mem_univ i)).trans (hpr j)
  let z (j : J) := d j / w j / a
  have hz (j) : 0 ≤ z j := div_nonneg (div_nonneg (hd j) (hw j).le) ha.le
  have hc (i) : 1 ≤ ∑ j, L i j * z j := by
    calc
      1 = a / a := (div_self ha.ne').symm
      _ ≤ (∑ j, d j * (L i j / w j)) / a :=
        div_le_div_of_nonneg_right (hdu i) ha.le
      _ = ∑ j, L i j * z j := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by dsimp [z]; ring
  have hcost : (∑ j, w j * z j) = 1 / a := by
    calc
      _ = ∑ j, d j / a := Finset.sum_congr rfl fun j _ => by
        dsimp [z]
        field_simp [(hw j).ne', ha.ne']
      _ = _ := by rw [← Finset.sum_div, hd1]
  have hf (j) : ∑ i, p i * L i j ≤ a * w j := by
    apply (div_le_iff₀ (hw j)).mp
    rw [Finset.sum_div]
    simpa only [mul_div_assoc] using hpr j
  refine ⟨z, ⟨hz, hc⟩, ?_, ?_, ?_⟩
  · intro y hy
    rw [hcost]
    apply (div_le_iff₀ ha).mpr
    simpa [mul_comm] using finiteMatrixWeakDual L w p y a hp hp1 hy.1 hy.2 hf
  · rw [hcost]
    exact div_pos zero_lt_one ha
  · intro q
    constructor
    · rintro ⟨r, hr, hr1, hrf⟩
      exact finiteMatrixWeakDual L w r z q hr hr1 hz hc hrf
    · intro hq
      rw [hcost, ← mul_div_assoc, mul_one, le_div_iff₀ ha, one_mul] at hq
      exact ⟨p, hp, hp1, fun j => (hf j).trans (mul_le_mul_of_nonneg_right hq (hw j).le)⟩

end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611

theorem finiteCoverMinimum {S : Type*} (E : Finset S)
    (A : Finset S → ℝ → Prop)
    (rows : ∀ T r, A T r → T.Nonempty ∧ T ⊆ E ∧ r ≤ 1)
    (w : S → ℝ) (hw : ∀ s ∈ E, 0 ≤ w s) :
    let cov := fun (z : S → ℝ) => (∀ s ∈ E, 0 ≤ z s) ∧
      ∀ T r, A T r → r ≤ ∑ s ∈ T, z s
    ∃ z, cov z ∧ ∀ y, cov y → (∑ s ∈ E, w s * z s) ≤ ∑ s ∈ E, w s * y s := by
  classical
  intro cov
  let I := {i : Finset S × ℝ // A i.1 i.2}
  let K := Set.univ.pi (fun _ : S => Set.Icc (0 : ℝ) 1)
  let H := ⋂ i : I, {z : S → ℝ | i.val.2 ≤ ∑ s ∈ i.val.1, z s}
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hH : IsClosed H := isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have ones : (fun _ : S => (1 : ℝ)) ∈ K ∩ H := by
    constructor
    · intro s _
      exact ⟨zero_le_one, le_rfl⟩
    · apply Set.mem_iInter.mpr
      intro i
      have hr := rows _ _ i.property
      change i.val.2 ≤ ∑ _s ∈ i.val.1, (1 : ℝ)
      have hcard : 1 ≤ i.val.1.card := hr.1.card_pos
      simpa using hr.2.2.trans (by exact_mod_cast hcard : (1 : ℝ) ≤ i.val.1.card)
  let obj := fun z : S → ℝ => ∑ s ∈ E, w s * z s
  have hc : Continuous obj := by dsimp [obj]; fun_prop
  obtain ⟨z, hz, minimal⟩ := (hK.inter_right hH).exists_isMinOn ⟨_, ones⟩ hc.continuousOn
  refine ⟨z, ⟨fun s _ => (hz.1 s (Set.mem_univ s)).1, ?_⟩, ?_⟩
  · intro T r ha
    exact Set.mem_iInter.mp hz.2 (⟨(T,r),ha⟩ : I)
  · intro y hy
    let a := fun s : S => if s ∈ E then min (y s) 1 else 0
    have aeq (s : S) (hs : s ∈ E) : a s = min (y s) 1 := if_pos hs
    have aK : a ∈ K := by
      intro s _
      by_cases h : s ∈ E
      · rw [Set.mem_Icc, aeq _ h]
        exact ⟨le_min (hy.1 s h) zero_le_one, min_le_right _ _⟩
      · simp [a, h, Set.mem_Icc]
    have aH : a ∈ H := by
      apply Set.mem_iInter.mpr
      intro i
      obtain ⟨hne, hsub, hr⟩ := rows _ _ i.property
      change i.val.2 ≤ ∑ s ∈ i.val.1, a s
      by_cases hit : ∃ s ∈ i.val.1, 1 ≤ y s
      · obtain ⟨s, hs, hys⟩ := hit
        have ha : a s = 1 := (aeq s (hsub hs)).trans (min_eq_right hys)
        exact hr.trans (ha ▸ Finset.single_le_sum (fun u _ => (aK u (Set.mem_univ u)).1) hs)
      · have same : ∀ s ∈ i.val.1, a s = y s := by
          intro s hs
          apply (aeq s (hsub hs)).trans
          exact min_eq_left (le_of_not_ge (fun f => hit ⟨s, hs, f⟩))
        rw [Finset.sum_congr rfl same]
        exact hy.2 _ _ i.property
    have low : obj z ≤ obj a := (isMinOn_iff.mp minimal) a ⟨aK, aH⟩
    exact low.trans (Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left
      ((aeq s hs).le.trans (min_le_left _ _)) (hw s hs))

theorem cutRepairMinimum {S : Type*} (E : Finset S)
    (cuts repairs : Finset S → Prop)
    (hcuts : ∀ T, cuts T → T.Nonempty ∧ T ⊆ E)
    (repairIn : ∀ T, repairs T → T ⊆ E) (noempty : ¬repairs ∅)
    (w : S → ℝ) (hw : ∀ s ∈ E, 0 ≤ w s) :
    let cov := fun (z : S → ℝ) => (∀ s ∈ E, 0 ≤ z s) ∧
      (∀ T, cuts T → 1 ≤ ∑ s ∈ T, z s) ∧
      ∀ T, repairs T → (∀ U, U ⊂ T → ¬repairs U) → 1 ≤ 2 * ∑ s ∈ T, z s
    ∃ z, cov z ∧ ∀ y, cov y → (∑ s ∈ E, w s * z s) ≤ ∑ s ∈ E, w s * y s := by
  classical
  intro cov
  let A := fun (T : Finset S) (r : ℝ) => (cuts T ∧ r = 1) ∨
    (repairs T ∧ (∀ U, U ⊂ T → ¬repairs U) ∧ r = 1/2)
  have rows : ∀ T r, A T r → T.Nonempty ∧ T ⊆ E ∧ r ≤ 1 := by
    rintro T r (⟨ht, rfl⟩ | ⟨ht, _, rfl⟩)
    · exact ⟨(hcuts _ ht).1, (hcuts _ ht).2, le_rfl⟩
    · exact ⟨Finset.nonempty_iff_ne_empty.mpr (fun he => noempty (he ▸ ht)),
        repairIn _ ht, by norm_num⟩
  have eqv (z : S → ℝ) : cov z ↔ (∀ s ∈ E, 0 ≤ z s) ∧
      ∀ T r, A T r → r ≤ ∑ s ∈ T, z s := by
    constructor
    · rintro ⟨hn, hc, hr⟩
      refine ⟨hn, ?_⟩
      rintro T r (⟨hT, rfl⟩ | ⟨hT, hm, rfl⟩)
      · exact hc T hT
      · linarith [hr T hT hm]
    · rintro ⟨hn, ha⟩
      refine ⟨hn, fun T hT => ha T 1 (Or.inl ⟨hT, rfl⟩), ?_⟩
      intro T hT hm
      linarith [ha T (1/2) (Or.inr ⟨hT, hm, rfl⟩)]
  obtain ⟨z, hz, hmin⟩ := finiteCoverMinimum E A rows w hw
  exact ⟨z, (eqv z).mpr hz, fun y hy => hmin _ ((eqv y).mp hy)⟩

end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611.Upper
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
end PEqualNP.Outside.L_meta_33611.Upper

namespace PEqualNP.Outside.L_meta_33611.Upper.PivotFinish

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem bit_gate_pair :
    ∀ a b : F,
    let ba := decide (a = 1)
    let bb := decide (b = 1)
    PEqualNP.CircuitLowerBounds.GateOp.and.eval [ba,bb] = decide (a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.or.eval [ba,bb] = decide (a+b+a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.not.eval
      [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ba,bb]] =
      decide (a+b = 1) := by
  decide +kernel

end PEqualNP.Outside.L_meta_33611.Upper.PivotFinish

namespace PEqualNP.Outside.L_meta_33611.Upper.GateDecode
open PEqualNP.CircuitLowerBounds
abbrev F := ZMod 2

def bit (x : F) : Bool := decide (x = 1)

def costly (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def legal (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

end PEqualNP.Outside.L_meta_33611.Upper.GateDecode

namespace PEqualNP.Outside.L_meta_33611.Upper.CircuitBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_33611.Upper.GateDecode
noncomputable def paid (g : Gate) : Bool := @decide (costly g) (Classical.propDecidable _)
def gateCost (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [_, _] | .or, [_, _] => 1
  | _, _ => 0
end PEqualNP.Outside.L_meta_33611.Upper.CircuitBridge

namespace PEqualNP.Outside.L_meta_33611.Upper.Lower
def bits {n : ℕ} (x : Fin n → ZMod 2) := List.ofFn (fun i => GateDecode.bit (x i))
end PEqualNP.Outside.L_meta_33611.Upper.Lower

namespace PEqualNP.Outside.L_meta_33611.Upper.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_33611.Upper.GateDecode PEqualNP.Outside.L_meta_33611.Upper.CircuitBridge

structure Build (n : ℕ) where
  gates : List Gate
  hlegal : ∀ g ∈ gates, legal g
  hback : ReadsBack n ⟨gates,0⟩

def Build.circ {n : ℕ} (B : Build n) (out : ℕ) : Circuit := ⟨B.gates,out⟩

def Build.next {n : ℕ} (B : Build n) : ℕ := n + B.gates.length

noncomputable def Build.cost {n : ℕ} (B : Build n) : ℕ := B.gates.countP paid

def empty (n : ℕ) : Build n :=
  ⟨[], by simp, by simp [ReadsBack]⟩

private theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,hj]

def Build.snoc {n : ℕ} (B : Build n) (g : Gate) (h : legal g)
    (hb : ∀ i ∈ g.inputs, i < B.next) : Build n where
  gates := B.gates++[g]
  hlegal := by
    intro a ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact B.hlegal a ha
    · exact h
  hback := by
    intro j hj i hi
    have hf : j < (B.gates++[g]).length := hj
    rw [gateAt_eq hj] at hi
    change i ∈ ((B.gates++[g])[j]'hf).inputs at hi
    by_cases hr : j < B.gates.length
    · rw [List.getElem_append_left hr] at hi
      have hh : j < (⟨B.gates,0⟩ : Circuit).gates.length := hr
      apply B.hback j hh i
      simpa only [gateAt_eq hh] using hi
    · have hj' : j = B.gates.length := by simp at hf; omega
      subst j
      have hg : (B.gates++[g])[B.gates.length] = g := by
        rw [List.getElem_append_right (by omega)]
        simp
      rw [hg] at hi
      exact hb i hi

theorem Build.next_snoc {n : ℕ} (B : Build n) (g : Gate) (h) (hb) :
    (B.snoc g h hb).next = B.next+1 := by
  simp [Build.next,Build.snoc,Nat.add_assoc]

theorem Build.cost_snoc {n : ℕ} (B : Build n) (g : Gate) (h) (hb) :
    (B.snoc g h hb).cost = B.cost + gateCost g := by
  classical
  simp only [Build.cost, Build.snoc, List.countP_append]
  congr 1
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> cases op <;>
    simp [List.countP_cons, paid, costly, gateCost]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem Build.len_wires {n : ℕ} (B : Build n) (w : List Bool) (hw : w.length = n) :
    ((B.circ 0).wires w).length = B.next := by
  have aux (gs : List Gate) (l : List Bool) :
      (gs.foldl step l).length = l.length + gs.length := by
    induction gs generalizing l with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [step]
      omega
  change (B.gates.foldl step w).length = _
  rw [aux,hw]
  rfl

def Build.get {n : ℕ} (B : Build n) (w : List Bool) (i : ℕ) : Bool :=
  (B.circ i).eval w

private theorem Build.step_wires {n : ℕ} (B : Build n) (g : Gate) (h) (hb) (w : List Bool) :
    ((B.snoc g h hb).circ 0).wires w = step ((B.circ 0).wires w) g := by
  change (B.gates++[g]).foldl step w = step (B.gates.foldl step w) g
  rw [List.foldl_append]
  rfl

theorem Build.get_snoc_old {n : ℕ} (B : Build n) (g : Gate) (h) (hb)
    (w : List Bool) (hw : w.length=n) (i : ℕ) (hi : i < B.next) :
    (B.snoc g h hb).get w i = B.get w i := by
  change (((B.snoc g h hb).circ 0).wires w).getD i false = ((B.circ 0).wires w).getD i false
  rw [Build.step_wires]
  unfold step
  exact List.getD_append _ _ _ _ (by rw [B.len_wires w hw]; exact hi)

theorem Build.get_snoc_new {n : ℕ} (B : Build n) (g : Gate) (h) (hb)
    (w : List Bool) (hw : w.length=n) :
    (B.snoc g h hb).get w B.next = g.op.eval (g.inputs.map fun i => B.get w i) := by
  change (((B.snoc g h hb).circ 0).wires w).getD B.next false =
    g.op.eval (g.inputs.map fun i => ((B.circ 0).wires w).getD i false)
  rw [Build.step_wires]
  rw [← B.len_wires w hw]
  unfold step
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
  rfl

end PEqualNP.Outside.L_meta_33611.Upper.Builder

namespace PEqualNP.Outside.L_meta_33611.Upper.BuildOps
open PEqualNP.Outside.L_meta_33611.Upper.Builder
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_33611.Upper.GateDecode

structure Ext {n : ℕ} (A B : Build n) : Prop where
  next_le : A.next ≤ B.next
  keeps : ∀ w : List Bool, w.length = n → ∀ i < A.next, B.get w i = A.get w i

theorem Ext.refl {n} (A : Build n) : Ext A A := ⟨le_rfl,fun _ _ _ _ => rfl⟩
theorem Ext.trans {n} {A B C : Build n} (h : Ext A B) (k : Ext B C) : Ext A C :=
  ⟨h.next_le.trans k.next_le, fun w hw i hi => (k.keeps w hw i (hi.trans_le h.next_le)).trans (h.keeps w hw i hi)⟩

theorem grow {n} (A : Build n) (g : Gate) (hl) (hb) : Ext A (A.snoc g hl hb) :=
  ⟨by rw [A.next_snoc]; omega, fun w hw i hi => A.get_snoc_old g hl hb w hw i hi⟩

theorem genConst {n} (A : Build n) (b : Bool) :
    ∃ (B : Build n) (i : ℕ), Ext A B ∧ i < B.next ∧ B.cost = A.cost ∧
      ∀ w : List Bool, w.length = n → B.get w i = b := by
  let g : Gate := ⟨if b then .and else .or, []⟩
  have hl : legal g := by cases b <;> simp [legal,g]
  have hb : ∀ i ∈ g.inputs, i < A.next := by simp [g]
  refine ⟨A.snoc g hl hb,A.next,grow A g hl hb,by rw [A.next_snoc]; omega,?_ , ?_⟩
  · rw [A.cost_snoc]
    cases b <;> rfl
  · intro w hw
    rw [A.get_snoc_new g hl hb w hw]
    cases b <;> rfl

theorem genAnd {n} (A : Build n) (i j : ℕ) (hi : i < A.next) (hj : j < A.next) :
    ∃ (B : Build n) (k : ℕ), Ext A B ∧ k < B.next ∧ B.cost = A.cost+1 ∧
    ∀ w : List Bool, w.length=n → B.get w k = (A.get w i && A.get w j) := by
  let g : Gate := ⟨.and,[i,j]⟩
  have hl : legal g := by simp [legal,g]
  have hb : ∀ a ∈ g.inputs, a < A.next := by
    intro a ha
    simp only [g,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> assumption
  refine ⟨A.snoc g hl hb,A.next,grow A g hl hb,by rw [A.next_snoc]; omega,?_ , ?_⟩
  · rw [A.cost_snoc]; rfl
  · intro w hw
    rw [A.get_snoc_new g hl hb w hw]
    simp [g,GateOp.eval]

theorem genXor {n} (A : Build n) (i j : ℕ) (hi : i < A.next) (hj : j < A.next) :
    ∃ (B : Build n) (k : ℕ), Ext A B ∧ k < B.next ∧ B.cost = A.cost ∧
    ∀ (w : List Bool), w.length=n → ∀ a b : F, A.get w i = bit a → A.get w j = bit b →
      B.get w k = bit (a+b) := by
  let g : Gate := ⟨.mod 2,[i,j]⟩
  have hg : legal g := by simp [legal,g]
  have gh : ∀ a ∈ g.inputs, a < A.next := by
    intro a ha
    simp only [g,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> assumption
  let M := A.snoc g hg gh
  let v := A.next
  have hv : v < M.next := by dsimp [v,M]; rw [A.next_snoc]; omega
  let t : Gate := ⟨.not,[v]⟩
  have ht : legal t := by simp [legal,t]
  have th : ∀ a ∈ t.inputs, a < M.next := by simpa [t] using hv
  refine ⟨M.snoc t ht th,M.next,(grow A g hg gh).trans (grow M t ht th), by rw [M.next_snoc]; omega,?_,?_⟩
  · rw [M.cost_snoc,A.cost_snoc]; rfl
  · intro w hw a b ha hb
    rw [M.get_snoc_new t ht th w hw]
    change GateOp.not.eval [M.get w v] = bit (a+b)
    rw [show M.get w v = (GateOp.mod 2).eval [A.get w i,A.get w j] from A.get_snoc_new g hg gh w hw]
    rw [ha,hb]
    exact (PEqualNP.Outside.L_meta_33611.Upper.PivotFinish.bit_gate_pair a b).2.2

theorem bitMul (a b : F) : (bit a && bit b) = bit (a*b) :=
  (by decide : ∀ a b : F, (bit a && bit b) = bit (a*b)) a b

end PEqualNP.Outside.L_meta_33611.Upper.BuildOps

namespace PEqualNP.Outside.L_meta_33611.Upper.UpperBase
open scoped BigOperators
open PEqualNP.Outside.L_meta_33611.Upper
abbrev Vec (n : ℕ) := V n
open PEqualNP.Outside.L_meta_33611.Upper.GateDecode (bit)
open PEqualNP.Outside.L_meta_33611.Upper.Lower (bits)
open PEqualNP.Outside.L_meta_33611.Upper.Builder PEqualNP.Outside.L_meta_33611.Upper.BuildOps

abbrev width (k t : ℕ) := 2*k+t

def inp {k t : ℕ} (x y : Vec k) (z : Vec t) : List Bool := bits x ++ bits y ++ bits z

theorem inp_len {k t : ℕ} (x y : Vec k) (z : Vec t) : (inp x y z).length = width k t := by
  simp [inp,bits,width] <;> omega

def xwire {k : ℕ} (i : Fin k) : ℕ := i.val
def ywire {k : ℕ} (i : Fin k) : ℕ := k+i.val
def zwire {t : ℕ} (k : ℕ) (j : Fin t) : ℕ := 2*k+j.val

theorem xbound {k t : ℕ} (i : Fin k) : xwire i < (empty (width k t)).next := by
  simp [xwire,empty,Build.next,width] <;> omega

theorem ybound {k t : ℕ} (i : Fin k) : ywire i < (empty (width k t)).next := by
  simp [ywire,empty,Build.next,width] <;> omega

theorem zbound {k t : ℕ} (j : Fin t) : zwire k j < (empty (width k t)).next := by
  simp [zwire,empty,Build.next,width] <;> omega

private theorem bits_get {k : ℕ} (x : Vec k) (i : Fin k) : (bits x).getD i.val false = bit (x i) := by
  rw [List.getD_eq_getElem _ _ (by simp [bits])]
  simp [bits]

theorem xval {k t : ℕ} (x y : Vec k) (z : Vec t) (i : Fin k) :
    (empty (width k t)).get (inp x y z) (xwire i) = bit (x i) := by
  change ((bits x ++ bits y) ++ bits z).getD i.val false = _
  rw [List.getD_append _ _ _ _ (by simp [bits] <;> omega),
    List.getD_append _ _ _ _ (by simp [bits])]
  exact bits_get x i

theorem yval {k t : ℕ} (x y : Vec k) (z : Vec t) (i : Fin k) :
    (empty (width k t)).get (inp x y z) (ywire i) = bit (y i) := by
  change ((bits x ++ bits y) ++ bits z).getD (k+i.val) false = _
  rw [List.getD_append _ _ _ _ (by simp [bits] <;> omega),
      List.getD_append_right _ _ _ _ (by simp [bits])]
  simp only [bits,List.length_ofFn, Nat.add_sub_cancel_left]
  exact bits_get y i

theorem zval {k t : ℕ} (x y : Vec k) (z : Vec t) (j : Fin t) :
    (empty (width k t)).get (inp x y z) (zwire k j) = bit (z j) := by
  change ((bits x ++ bits y) ++ bits z).getD (2*k+j.val) false = _
  rw [List.getD_append_right _ _ _ _ (by simp [bits] <;> omega)]
  simp only [bits,List.length_ofFn,List.length_append]
  rw [show 2*k+j.val-(k+k) = j.val by omega]
  exact bits_get z j

theorem empty_cost (n : ℕ) : (empty n).cost = 0 := rfl

end PEqualNP.Outside.L_meta_33611.Upper.UpperBase

namespace PEqualNP.Outside.L_meta_33611.Upper
open Builder BuildOps PEqualNP.CircuitLowerBounds
open GateDecode (bit)
abbrev XY (n : Nat) := V n × V n
def Input {n} (x : XY n) := Lower.bits x.1 ++ Lower.bits x.2
theorem input_len {n} (x : XY n) : (Input x).length=2*n := by simp [Input,Lower.bits];omega

def Free {n} (B : Build (2*n)) (f : XY n → F) : Prop :=
  ∀ C, Ext B C → ∃ (E : Build (2*n)) (i : Nat), Ext C E ∧ i<E.next ∧ E.cost=C.cost ∧
    ∀ x, E.get (Input x) i=bit (f x)

theorem free_next {n} {B C : Build (2*n)} {f : XY n → F} (h : Ext B C) (hf : Free B f) : Free C f :=
  fun Z hz => hf Z (h.trans hz)

theorem free_wire {n} (B : Build (2*n)) (j : Nat) (lt : j<B.next) (f : XY n → F)
    (ev : ∀ x, B.get (Input x) j=bit (f x)) : Free B f := by
  intro C h
  exact ⟨C,j,Ext.refl _,lt.trans_le h.next_le,rfl,fun x => (h.keeps _ (input_len x) j lt).trans (ev x)⟩

theorem free_const {n} (B : Build (2*n)) (s : F) : Free B (fun _ => s) := by
  intro C _
  obtain ⟨E,i,he,hi,hc,ev⟩ := genConst C (bit s)
  exact ⟨E,i,he,hi,hc,fun x => ev _ (input_len x)⟩

theorem free_add {n} {B : Build (2*n)} {f g : XY n → F} (hf : Free B f) (hg : Free B g) :
    Free B (fun x => f x+g x) := by
  intro C h
  obtain ⟨E,i,hCE,hi,cE,vi⟩ := hf C h
  obtain ⟨K,j,hEK,hj,cK,vj⟩ := hg E (h.trans hCE)
  obtain ⟨Q,q,hKQ,hq,cQ,vq⟩ := genXor K i j (hi.trans_le hEK.next_le) hj
  refine ⟨Q,q,(hCE.trans hEK).trans hKQ,hq,cQ.trans (cK.trans cE),?_⟩
  intro x
  exact vq _ (input_len x) _ _ ((hEK.keeps _ (input_len x) _ hi).trans (vi x)) (vj x)

theorem free_scale {n} {B : Build (2*n)} {f : XY n → F} (s : F) (hf : Free B f) :
    Free B (fun x => s*f x) := by
  rcases (show s=0 ∨ s=1 from (by decide : ∀ s : F, s=0 ∨ s=1) s) with h|h
  · simpa only [h,zero_mul] using free_const B 0
  · simpa only [h,one_mul] using hf

theorem free_sum {n} {B : Build (2*n)} {ι : Type*} [DecidableEq ι] (S : Finset ι) {f : ι → XY n → F}
    (h : ∀ i∈S,Free B (f i)) : Free B (fun x => ∑ i∈S, f i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using free_const B 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact free_add (h i (by simp)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem paid_set {n} {B : Build (2*n)} {ι : Type*} [DecidableEq ι] (S : Finset ι) (f g : ι → XY n → F)
    (hf : ∀ i∈S,Free B (f i)) (hg : ∀ i∈S,Free B (g i)) :
    ∃ C, Ext B C ∧ C.cost=B.cost+S.card ∧ ∀ i∈S, Free C (fun x => f i x*g i x) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨B,Ext.refl _,by simp,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨C,hBC,cC,vC⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,a,hCE,ha,cE,va⟩ := hf i (by simp) C hBC
    obtain ⟨K,b,hEK,hb,cK,vb⟩ := hg i (by simp) E (hBC.trans hCE)
    obtain ⟨Q,j,hKQ,hj,cQ,vj⟩ := genAnd K a b (ha.trans_le hEK.next_le) hb
    let hCQ := (hCE.trans hEK).trans hKQ
    refine ⟨Q,hBC.trans hCQ,by rw [cQ,cK,cE,cC,Finset.card_insert_of_notMem hi];omega,?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with eq|mem
    · subst t
      apply free_wire Q j hj
      intro x
      rw [vj _ (input_len x),hEK.keeps _ (input_len x) _ ha,va,vb,bitMul]
    · exact free_next hCQ (vC t mem)

theorem raw_x {n} (i : Fin n) : Free (empty (2*n)) (fun z : XY n => z.1 i) := by
  apply free_wire _ (UpperBase.xwire i) (UpperBase.xbound (t:=0) i)
  intro z
  simpa [Input,UpperBase.inp,Lower.bits] using UpperBase.xval z.1 z.2 (0 : V 0) i

theorem raw_y {n} (i : Fin n) : Free (empty (2*n)) (fun z : XY n => z.2 i) := by
  apply free_wire _ (UpperBase.ywire i) (UpperBase.ybound (t:=0) i)
  intro z
  simpa [Input,UpperBase.inp,Lower.bits] using UpperBase.yval z.1 z.2 (0 : V 0) i

theorem raw_dot {n} (l : V n) : Free (empty (2*n)) (fun z : XY n => dotProduct l z.2) :=
  free_sum Finset.univ (fun j _ => free_scale (l j) (raw_y j))

theorem affineInput {n : ℕ} (f : V n →ₗ[F] F) (c : F) :
    Free (empty (2*n)) (fun z : XY n => c + f z.2) := by
  have hf : (fun z : XY n => f z.2) = fun z => ∑ i, f (Pi.single i 1) * z.2 i := by
    funext z
    have row : (∑ i : Fin n, z.2 i • Pi.single i (1 : F)) = z.2 := by
      ext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    calc
      f z.2 = f (∑ i : Fin n, z.2 i • Pi.single i (1 : F)) := congrArg f row.symm
      _ = _ := by simp [map_sum, mul_comm]
  apply free_add (free_const _ c)
  change Free _ (fun z : XY n => f z.2)
  rw [hf]
  exact free_sum Finset.univ fun i _ => free_scale _ (raw_y i)

theorem compileFactors {n d c : ℕ} (constPart : XY n → F)
    (Lin Sum : Fin d → XY n → F) (A B : Fin c → XY n → F)
    (offset : Fin c → F) (coeff : Fin d → Fin c → F)
    (constantFree : Free (empty (2*n)) constPart)
    (linFree : ∀ j, Free (empty (2*n)) (Lin j)) (sumFree : ∀ j, Free (empty (2*n)) (Sum j))
    (aFree : ∀ i, Free (empty (2*n)) (A i)) (bFree : ∀ i, Free (empty (2*n)) (B i)) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
      (∀ g ∈ C.gates, GateDecode.legal g) ∧ C.gates.countP CircuitBridge.paid ≤ d+c ∧
      ∀ z : XY n, C.eval (Input z) = bit ((constPart z + ∑ i, offset i * (A i z * B i z)) +
        ∑ j, (Sum j z + ∑ i, coeff j i * (A i z * B i z)) * Lin j z) := by
  classical
  obtain ⟨B₁, h₁, cost₁, v₁⟩ := paid_set (B := empty (2*n)) Finset.univ A B
    (fun i _ => aFree i) (fun i _ => bFree i)
  let T := fun j (z : XY n) => Sum j z + ∑ i, coeff j i * (A i z * B i z)
  have hT (j) : Free B₁ (T j) := free_add (free_next h₁ (sumFree j))
    (free_sum Finset.univ fun i _ => free_scale _ (v₁ i (Finset.mem_univ _)))
  obtain ⟨B₂, h₂, cost₂, v₂⟩ := paid_set Finset.univ T Lin (fun j _ => hT j)
    (fun j _ => free_next h₁ (linFree j))
  have h₀ := free_next h₂ (free_add (free_next h₁ constantFree)
    (free_sum Finset.univ fun i _ => free_scale (offset i) (v₁ i (Finset.mem_univ _))))
  obtain ⟨Z, o, _, _, hc, hv⟩ := (free_add h₀ (free_sum Finset.univ v₂)) B₂ (Ext.refl _)
  refine ⟨Z.circ o, Z.hback, Z.hlegal, ?_, hv⟩
  change Z.cost ≤ d+c
  rw [hc, cost₂, cost₁]
  simp [UpperBase.empty_cost, Nat.add_comm]

def reconstruct {n d : ℕ} (o : V n) (K : Fin d → V n) (u : Fin d → V n → F)
    (y : V n) : V n := o + ∑ j, u j y • K j

theorem form_reconstruct {n d : ℕ} (o : V n) (K : Fin d → V n) (u : Fin d → V n → F)
    (L : V n →ₗ[F] F) (y : V n) :
    L (reconstruct o K u y) = L o + ∑ j, L (K j) * u j y := by
  simp [reconstruct, mul_comm]

theorem freeReconstruct {n d : ℕ} (o : V n) (K : Fin d → V n) (u : Fin d → V n → F)
    (hu : ∀ j, Free (empty (2*n)) (fun z : XY n => u j z.2)) (L : V n →ₗ[F] F) :
    Free (empty (2*n)) (fun z : XY n => L (reconstruct o K u z.2)) := by
  simp_rw [form_reconstruct]
  exact free_add (free_const _ _) (free_sum Finset.univ fun j _ => free_scale _ (hu j))

theorem regroup {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R o : ι → F) (K : κ → ι → F) (u : κ → F) :
    ∑ i, R i * (o i + ∑ j, K j i * u j) =
      (∑ i, o i * R i) + ∑ j, (∑ i, K j i * R i) * u j := by
  classical
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem compileProjected {n d c : ℕ} {ι : Type*} [Fintype ι]
    (o : V n) (K : Fin d → V n) (u : Fin d → V n → F)
    (H : XY n → F) (R : ι → XY n → F) (L : ι → V n →ₗ[F] F)
    (A B C₃ : Fin c → V n →ₗ[F] F)
    (hu : ∀ j, Free (empty (2*n)) (fun z : XY n => u j z.2))
    (hf : Free (empty (2*n)) H) (hR : ∀ i, Free (empty (2*n)) (R i)) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
      (∀ g ∈ C.gates, GateDecode.legal g) ∧ C.gates.countP CircuitBridge.paid ≤ d+c ∧
      ∀ z : XY n, let y := reconstruct o K u z.2
        C.eval (Input z) = bit ((H z + ∑ i, R i z * L i y) +
          ∑ i, (A i y * B i y) * C₃ i y) := by
  classical
  let P := reconstruct o K u
  let H₀ := fun z => H z + ∑ i, L i o * R i z
  let U := fun j (z : XY n) => u j z.2
  let S := fun j z => ∑ i, L i (K j) * R i z
  let a := fun i (z : XY n) => A i (P z.2)
  let b := fun i (z : XY n) => B i (P z.2)
  have hH : Free (empty (2*n)) H₀ := free_add hf
    (free_sum Finset.univ (fun i _ => free_scale _ (hR i)))
  have hS (j) : Free (empty (2*n)) (S j) :=
    free_sum Finset.univ (fun i _ => free_scale _ (hR i))
  obtain ⟨C, hback, good, cost, vals⟩ := compileFactors H₀ U S a b
    (fun i => C₃ i o) (fun j i => C₃ i (K j)) hH hu hS
    (fun i => freeReconstruct o K u hu (A i)) (fun i => freeReconstruct o K u hu (B i))
  refine ⟨C, hback, good, cost, ?_⟩
  intro z
  rw [vals]
  congr 1
  dsimp only [H₀, U, S, a, b, P]
  conv_rhs =>
    enter [1, 2, 2, i, 2]
    rw [form_reconstruct]
  conv_rhs =>
    enter [2, 2, i, 2]
    rw [form_reconstruct]
  rw [regroup (fun i => R i z) (fun i => L i o) (fun j i => L i (K j)) (fun j => u j z.2)]
  rw [regroup (fun i => A i (reconstruct o K u z.2) * B i (reconstruct o K u z.2))
    (fun i => C₃ i o) (fun j i => C₃ i (K j)) (fun j => u j z.2)]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

def dotForm {n : ℕ} (v : V n) : V n →ₗ[F] F :=
  ∑ i : Fin n, v i • LinearMap.proj i

theorem dotForm_apply {n : ℕ} (v x : V n) : dotForm v x = dotProduct v x := by
  simp [dotForm, dotProduct, LinearMap.sum_apply]

theorem hullChart {n : ℕ} (W : Submodule F (V n)) (o : V n) :
    ∃ (K : Fin (Module.finrank F W) → V n) (u : Fin (Module.finrank F W) → V n → F),
      (∀ j, Free (empty (2*n)) (fun z : XY n => u j z.2)) ∧
      (∀ y, y-o ∈ W → reconstruct o K u y = y) ∧
      ∀ y, reconstruct o K u y - o ∈ W := by
  classical
  let B := Module.finBasis F W
  obtain ⟨W', hW⟩ := W.exists_isCompl
  let P := W.projectionOnto W' hW
  let L := fun j => (B.coord j).comp P
  let K := fun j => (B j : V n)
  let u := fun j y => L j (y-o)
  refine ⟨K, u, ?_, ?_, ?_⟩
  · intro j
    have hu : (fun z : XY n => u j z.2) = fun z => -(L j o) + L j z.2 := by
      funext z
      simp [u, map_sub, sub_eq_add_neg, add_comm]
    rw [hu]
    exact affineInput (L j) _
  · intro y hy
    let v : W := ⟨y-o, hy⟩
    have hv : P (y-o) = v := W.projectionOnto_apply_of_mem_left hW hy
    have eq : (∑ j, u j y • K j) = y-o := by
      have hj (j) : u j y = B.repr v j := by
        change (B.coord j) (P (y-o)) = _
        rw [hv]
        rfl
      calc
        _ = W.subtype (∑ j, B.repr v j • B j) := by
          simp only [map_sum, map_smul, hj]
          rfl
        _ = y-o := by rw [B.sum_repr]; rfl
    simpa [reconstruct, eq, add_comm] using (sub_add_cancel y o)
  · intro y
    rw [reconstruct, add_sub_cancel_left]
    exact W.sum_mem fun j _ => W.smul_mem _ (B j).property

def quadVal {k : ℕ} (a : F) (l : V k) (M : Fin k → V k) (y : V k) :=
  a + dotProduct l y + ∑ i, ∑ j, M i j * y i * y j

theorem quadRegroup {k : ℕ} (a : F) (l : V k) (M : Fin k → V k) (y : V k) :
    quadVal a l M y = (a + dotForm l y) + ∑ i, dotForm (M i) y * y i := by
  simp only [quadVal, dotForm_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem compilePromise {n k d c : ℕ} (sel : V n →ₗ[F] V k)
    (o : V n) (K : Fin d → V n) (u : Fin d → V n → F)
    (hu : ∀ j, Free (empty (2*n)) (fun z : XY n => u j z.2))
    (a₁ a₂ : F) (l₁ : V n) (l₂ : V k) (M₁ : Fin n → V n) (M₂ : Fin k → V k)
    (a b h : Fin c → V k) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
      (∀ g ∈ C.gates, GateDecode.legal g) ∧ C.gates.countP CircuitBridge.paid ≤ d+c ∧
      ∀ x y, let py := reconstruct o K u y
        C.eval (Input (x,y)) = bit (dotProduct x py + quadVal a₁ l₁ M₁ py +
          quadVal a₂ l₂ M₂ (sel py) +
          ∑ i, (dotProduct (a i) (sel py) * dotProduct (b i) (sel py)) * dotProduct (h i) (sel py)) := by
  classical
  let P := reconstruct o K u
  let I := Fin n ⊕ (Fin n ⊕ Fin k)
  let H := fun (z : XY n) => (a₁ + dotForm l₁ (P z.2)) + (a₂ + dotForm l₂ (sel (P z.2)))
  let R : I → XY n → F := Sum.elim (fun i z => z.1 i) (Sum.elim
    (fun i z => dotForm (M₁ i) (P z.2)) (fun j z => dotForm (M₂ j) (sel (P z.2))))
  let L : I → V n →ₗ[F] F := Sum.elim (fun i => LinearMap.proj i) (Sum.elim
    (fun i => LinearMap.proj i) (fun j => (LinearMap.proj j).comp sel))
  have fh : Free (empty (2*n)) H := free_add
    (free_add (free_const _ _) (freeReconstruct o K u hu (dotForm l₁)))
    (free_add (free_const _ _) (freeReconstruct o K u hu ((dotForm l₂).comp sel)))
  have fr : ∀ i, Free (empty (2*n)) (R i) := by
    rintro (i | (i | j))
    · exact raw_x i
    · exact freeReconstruct o K u hu (dotForm (M₁ i))
    · exact freeReconstruct o K u hu ((dotForm (M₂ j)).comp sel)
  obtain ⟨C, hback, good, cost, he⟩ := compileProjected o K u H R L
    (fun i => (dotForm (a i)).comp sel) (fun i => (dotForm (b i)).comp sel)
    (fun i => (dotForm (h i)).comp sel) hu fh fr
  refine ⟨C, hback, good, cost, ?_⟩
  intro x y
  rw [he]
  congr 1
  simp only [I, H, P, R, L, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    LinearMap.proj_apply, LinearMap.comp_apply, quadRegroup, dotForm_apply]
  change _ = dotProduct x _ + _ + _ + _
  unfold dotProduct
  ring

theorem compileOnSelectors {n k t c : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (E : Finset (V k)) (o : V k) (a₁ a₂ : F) (l₁ : V n) (l₂ : V k)
    (M₁ : Fin n → V n) (M₂ : Fin k → V k) (a b h : Fin c → V k) :
    let W := Submodule.span F ((fun s => s-o) '' (↑E : Set (V k)))
    ∃ C : Circuit, PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
      (∀ g ∈ C.gates, GateDecode.legal g) ∧
      C.gates.countP CircuitBridge.paid ≤ (t + Module.finrank F W) + c ∧
      ∀ s ∈ E, ∀ x z, let y := e.symm (s,z)
        C.eval (Input (x,y)) = bit (dotProduct x y + quadVal a₁ l₁ M₁ y +
          quadVal a₂ l₂ M₂ s + ∑ i, (dotProduct (a i) s * dotProduct (b i) s) * dotProduct (h i) s) := by
  classical
  intro W
  let embed : (W × V t) →ₗ[F] V n := e.symm.toLinearMap.comp (W.subtype.prodMap LinearMap.id)
  let U := LinearMap.range embed
  let y₀ := e.symm (o, 0)
  let sel : V n →ₗ[F] V k := (LinearMap.fst F (V k) (V t)).comp e.toLinearMap
  obtain ⟨K,u,hfree,agree,_⟩ := hullChart U y₀
  obtain ⟨C, back, good, cost, val⟩ := compilePromise sel y₀ K u hfree a₁ a₂ l₁ l₂ M₁ M₂ a b h
  have hd : Module.finrank F U ≤ t + Module.finrank F W := by
    have hh := LinearMap.finrank_range_le embed
    simpa [U, Module.finrank_prod, Module.finrank_pi, Nat.add_comm] using hh
  refine ⟨C, back, good, cost.trans (Nat.add_le_add_right hd c), ?_⟩
  intro s hs x z
  have hsW : s-o ∈ W := Submodule.subset_span ⟨s, hs, rfl⟩
  have hin : e.symm (s,z) - y₀ ∈ U := by
    refine ⟨(⟨s-o,hsW⟩, z), ?_⟩
    change e.symm (s-o,z) = e.symm (s,z) - e.symm (o,0)
    rw [← map_sub]
    congr 1
    exact Prod.ext rfl (sub_zero z).symm
  have chosen := agree _ hin
  have selector : sel (e.symm (s,z)) = s := by simp [sel]
  simpa only [chosen, selector] using val x (e.symm (s,z))

def Quad {k : ℕ} (f : V k → F) := ∃ a l M, ∀ s, f s = quadVal a l M s

def Fits (n p : ℕ) (C : Circuit) := PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
  (∀ g ∈ C.gates, GateDecode.legal g) ∧ C.gates.countP CircuitBridge.paid ≤ p

noncomputable def budget {k : ℕ} (t : ℕ) (E : Finset (V k)) (o : V k) :=
  t + Module.finrank F (Submodule.span F ((fun s => s-o) '' (↑E : Set (V k))))

noncomputable def Score {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t) (Q : V n → F) (h : V k → F)
    (C : Circuit) (s : V k) : ℝ :=
  (∑ x : V n, ∑ b : V t, let y := e.symm (s,b)
    if C.eval (Input (x,y)) = bit (dotProduct x y + Q y + h s) then (1 : ℝ) else -1) / 2^(n+t)

theorem realizeQuad {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (Q : V n → F) (hq : Quad Q) (f : V k → F) (hf : Quad f) (E : Finset (V k)) (o : V k) :
    ∃ C : Circuit, Fits n (budget t E o) C ∧ ∀ s ∈ E, ∀ x z, let y := e.symm (s,z)
      C.eval (Input (x,y)) = bit (dotProduct x y + Q y + f s) := by
  obtain ⟨a₁,l₁,M₁,h₁⟩ := hq
  obtain ⟨a₂,l₂,M₂,h₂⟩ := hf
  obtain ⟨C,bk,gd,cost,val⟩ := compileOnSelectors (c:=0) e E o a₁ a₂ l₁ l₂ M₁ M₂
    Fin.elim0 Fin.elim0 Fin.elim0
  refine ⟨C, ⟨bk,gd,by simpa [budget] using cost⟩, ?_⟩
  intro s hs x z
  simpa [h₁,h₂] using val s hs x z

theorem realizeOne {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (Q : V n → F) (hq : Quad Q) (h : V k → F) (E : Finset (V k)) (o : V k)
    (one : ∃ (a b c : V k) (f : V k → F), Quad f ∧ ∀ s ∈ E,
      h s = f s + dotProduct a s * dotProduct b s * dotProduct c s) :
    ∃ C : Circuit, Fits n (budget t E o + 1) C ∧ ∀ s ∈ E, ∀ x z, let y := e.symm (s,z)
      C.eval (Input (x,y)) = bit (dotProduct x y + Q y + h s) := by
  obtain ⟨a,b,c,f, ⟨a₂,l₂,M₂,h₂⟩, hs⟩ := one
  obtain ⟨a₁,l₁,M₁,h₁⟩ := hq
  obtain ⟨C,bk,gd,cost,val⟩ := compileOnSelectors (c:=1) e E o a₁ a₂ l₁ l₂ M₁ M₂
    (fun _ => a) (fun _ => b) (fun _ => c)
  refine ⟨C, ⟨bk,gd,cost⟩, ?_⟩
  intro s he x z
  simpa [h₁, hs s he, h₂, add_assoc] using val s he x z

theorem realizeRepairLoss {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (Q : V n → F) (hq : Quad Q) (h : V k → F) (E T : Finset (V k)) (o : V k)
    (repair : ∃ f : V k → F, Quad f ∧ ∀ s ∈ E,
      h s = f s + (if s ∈ T then 1 else 0)) :
    ∃ C : Circuit, Fits n (budget t E o) C ∧ ∀ s ∈ E,
      1 - Score e Q h C s = if s ∈ T then (2 : ℝ) else 0 := by
  classical
  obtain ⟨f,hf,hr⟩ := repair
  obtain ⟨C,cost,correct⟩ := realizeQuad e Q hq f hf E o
  refine ⟨C,cost,?_⟩
  intro s hs
  have flip : ∀ x y z : F, bit (x+y+z) ≠ bit (x+y+(z+1)) := by decide
  by_cases hT : s ∈ T
  · have hbad (x : V n) (b : V t) : C.eval (Input (x,e.symm (s,b))) ≠
        bit (dotProduct x (e.symm (s,b)) + Q (e.symm (s,b)) + h s) := by
      rw [correct s hs x b, hr s hs, if_pos hT]
      exact flip _ _ _
    simp [Score,hT,hbad,ZMod.card,Fintype.card_fun,pow_add] <;> norm_num
  · have heq (x : V n) (b : V t) : C.eval (Input (x,e.symm (s,b))) =
        bit (dotProduct x (e.symm (s,b)) + Q (e.symm (s,b)) + h s) := by
      simpa [hr s hs, hT] using correct s hs x b
    simp [Score,hT,heq,ZMod.card,Fintype.card_fun,pow_add]

end PEqualNP.Outside.L_meta_33611.Upper

namespace PEqualNP.Outside.L_meta_33611

theorem pivotProductOperand {F X Y : Type*} [Field F] [AddCommGroup X] [Module F X]
    [FiniteDimensional F X] (l : X →ₗ[F] F) (nonzero : l ≠ 0) (a : Y → F) :
    Module.finrank F l.ker + 1 = Module.finrank F X ∧
    ∃ v : X, l v = 1 ∧
      (∀ (u : l.ker) y, l ((u : X) - a y • v) + a y = 0) ∧
      ∀ (r : X →ₗ[F] F) (c : Y → F) (u : l.ker) y,
        r ((u : X) - a y • v) + c y = r u + (c y - r v * a y) := by
  obtain ⟨v, hv⟩ := LinearMap.surjective nonzero 1
  refine ⟨Module.Dual.finrank_ker_add_one_of_ne_zero nonzero, v, hv, ?_, ?_⟩
  · intro u y
    have hu : l (u : X) = 0 := u.property
    simp [map_sub, hu, hv, smul_eq_mul]
  · intro r c u y
    simp only [map_sub, map_smul, smul_eq_mul]
    ring

theorem freeDirectionRank {F : Type*} [Field F] {n : ℕ}
    (U : Submodule F (Fin n → F)) (Y : Set (Fin n → F)) (o : Fin n → F)
    (fixed : ∀ y ∈ Y, ∀ u ∈ U, dotProduct y u = dotProduct o u) :
    Module.finrank F U +
      Module.finrank F (Submodule.span F ((fun y => y-o) '' Y)) ≤ n := by
  let W := Submodule.span F ((fun y => y-o) '' Y)
  let e := dotProductEquiv F (Fin n)
  have inc : W ≤ U.dualAnnihilator.comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    apply (U.mem_dualAnnihilator _).mpr
    intro u hu
    change dotProduct (y-o) u = 0
    rw [sub_dotProduct, fixed y hy u hu, sub_self]
  have m := Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr inc)
  change Module.finrank F U + Module.finrank F W ≤ n
  rw [e.finrank_map_eq] at m
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have dimension : Module.finrank F (Fin n → F) = n := by simp
  omega

def selectorQuadratic {k : ℕ} (f : (Fin k → ZMod 2) → ZMod 2) : Prop :=
  ∃ (d : ZMod 2) (l : Fin k → ZMod 2) (M : Fin k → Fin k → ZMod 2), ∀ u,
    f u = d + dotProduct l u + ∑ i, ∑ j, M i j * u i * u j

private theorem selectorDotMul {k : ℕ} (a b s : Fin k → ZMod 2) :
    dotProduct a s * dotProduct b s = ∑ i, ∑ j, (a i * b j) * s i * s j := by
  simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem residualGivesOne {k : ℕ} (E : Finset (Fin k → ZMod 2))
    (h f : (Fin k → ZMod 2) → ZMod 2) (a b c : Fin k → ZMod 2)
    (a₀ b₀ c₀ : ZMod 2) (quad : selectorQuadratic f)
    (agree : ∀ s ∈ E, h s = f s +
      (a₀ + dotProduct a s) * (b₀ + dotProduct b s) * (c₀ + dotProduct c s)) :
    ∃ g : (Fin k → ZMod 2) → ZMod 2, selectorQuadratic g ∧
      ∀ s ∈ E, h s = g s + dotProduct a s * dotProduct b s * dotProduct c s := by
  obtain ⟨d, l, M, hf⟩ := quad
  let l' := fun i => l i + (b₀*c₀)*a i + (a₀*c₀)*b i + (a₀*b₀)*c i
  let M' := fun i j => M i j + c₀*(a i*b j) + b₀*(a i*c j) + a₀*(b i*c j)
  let g := fun s => (d + a₀*b₀*c₀) + dotProduct l' s + ∑ i, ∑ j, M' i j * s i * s j
  refine ⟨g, ⟨_, l', M', fun _ => rfl⟩, ?_⟩
  intro s hs
  rw [agree s hs, hf s]
  have lin : dotProduct l' s = dotProduct l s + (b₀*c₀)*dotProduct a s +
      (a₀*c₀)*dotProduct b s + (a₀*b₀)*dotProduct c s := by
    simp only [l', dotProduct, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  have mat : (∑ i, ∑ j, M' i j * s i * s j) = (∑ i, ∑ j, M i j * s i * s j) +
      c₀*(dotProduct a s * dotProduct b s) + b₀*(dotProduct a s * dotProduct c s) +
      a₀*(dotProduct b s * dotProduct c s) := by
    simp only [M', selectorDotMul, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  change _ = ((d + a₀*b₀*c₀) + dotProduct l' s + (∑ i, ∑ j, M' i j * s i * s j)) + _
  rw [lin, mat]
  ring

end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611.Normal.PivotFinish

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem bit_gate_pair :
    ∀ a b : F,
    let ba := decide (a = 1)
    let bb := decide (b = 1)
    PEqualNP.CircuitLowerBounds.GateOp.and.eval [ba,bb] = decide (a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.or.eval [ba,bb] = decide (a+b+a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.not.eval
      [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ba,bb]] =
      decide (a+b = 1) := by
  decide +kernel

theorem no_free_after_elimination {p k t : ℕ} (A : Vec p →ₗ[F] Vec k)
    (hA : Function.Injective A) (b : Vec k → Vec t → Vec k)
    (g h : Vec k → Vec t → F) (l : Vec p → F)
    (heval : ∀ q y z, dotProduct (A q + b y z) y + g y z = l q + h y z) :
    p = 0 := by
  have hconst : ∀ q, l q = l 0 := by
    intro q
    have hq := heval q 0 0
    have h0 := heval 0 0 0
    simp only [dotProduct_zero] at hq h0
    exact add_right_cancel (hq.symm.trans h0)
  have hvanish : ∀ q, A q = 0 := by
    intro q
    ext i
    let y : Vec k := fun j => if i = j then 1 else 0
    have hq := heval q y 0
    have h0 := heval 0 y 0
    rw [hconst q] at hq
    have hd : dotProduct (A q + b y 0) y = dotProduct (b y 0) y := by
      apply add_right_cancel (b := g y 0)
      simpa only [map_zero, zero_add] using hq.trans h0.symm
    have hdot : ∀ v : Vec k, dotProduct v y = v i := by
      intro v
      simp [dotProduct,y,Finset.sum_ite_eq]
    rw [hdot, hdot] at hd
    have hz : A q i + b y 0 i = 0 + b y 0 i := hd.trans (zero_add _).symm
    exact add_right_cancel hz
  by_contra hp
  let i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
  let q : Vec p := fun _ => 1
  have he : q = 0 := hA ((hvanish q).trans (map_zero A).symm)
  have hm : (1 : F) = 0 := congrFun he i
  exact one_ne_zero hm

end PEqualNP.Outside.L_meta_33611.Normal.PivotFinish

namespace PEqualNP.Outside.L_meta_33611.Normal.PivotStep
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem solve_one {p : ℕ} (a : Vec (p+1) →ₗ[F] F) (ha : a ≠ 0) :
    ∃ (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1)),
      Function.Injective R ∧ a v = 1 ∧
      (∀ q, a (R q) = 0) ∧ (∀ q c, a (R q + c • v) + c = 0) := by
  classical
  have hsurj : Function.Surjective a := LinearMap.surjective_of_ne_zero ha
  obtain ⟨v,hv⟩ := hsurj 1
  have hkdim : Module.finrank F a.ker = p := by
    have h := LinearMap.finrank_range_add_finrank_ker a
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega
  let E : Vec p ≃ₗ[F] a.ker := LinearEquiv.ofFinrankEq _ _ (by rw [hkdim, Module.finrank_fin_fun])
  let R : Vec p →ₗ[F] Vec (p+1) := a.ker.subtype.comp E.toLinearMap
  have hR : ∀ q, a (R q) = 0 := fun q => LinearMap.mem_ker.mp (E q).property
  refine ⟨R, v, a.ker.subtype_injective.comp E.injective, hv, hR, ?_⟩
  intro q c
  simp [hR, hv, CharTwo.add_self_eq_zero]

end PEqualNP.Outside.L_meta_33611.Normal.PivotStep

namespace PEqualNP.Outside.L_meta_33611.Normal.CubeParity

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def toggle {d : ℕ} (i : Fin d) (w : Vec d) : Vec d :=
  Function.update w i (w i + 1)

theorem toggle_involutive {d : ℕ} (i : Fin d) : Function.Involutive (toggle i) := by
  intro w
  ext j
  by_cases h : j = i
  · subst j
    simp [toggle, add_assoc, CharTwo.add_self_eq_zero]
  · simp [toggle, Function.update_of_ne h]

theorem sum_zero_of_toggle {d : ℕ} (i : Fin d) (f : Vec d → F)
    (hf : ∀ w, f (toggle i w) = f w) : (∑ w, f w) = 0 := by
  let E : Vec d ≃ Vec d := ⟨toggle i, toggle i, toggle_involutive i, toggle_involutive i⟩
  have h : (∑ w : Vec d, f w * w i) = ∑ w : Vec d, f w * (w i + 1) := by
    apply Fintype.sum_equiv E
    intro w
    change f w * w i = f (toggle i w) * (toggle i w i + 1)
    rw [hf]
    simp [toggle, add_assoc, CharTwo.add_self_eq_zero]
  calc
    (∑ w, f w) = ∑ w : Vec d, (f w * w i + f w * (w i + 1)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← mul_add]
      simp [add_assoc, ← add_assoc (w i), CharTwo.add_self_eq_zero]
    _ = (∑ w : Vec d, f w * w i) + (∑ w : Vec d, f w * (w i + 1)) :=
      Finset.sum_add_distrib
    _ = 0 := h ▸ CharTwo.add_self_eq_zero _

theorem sum_monomial_eq_zero {d : ℕ} (S : Finset (Fin d)) (hS : S.card < d) (c : F) :
    (∑ w : Vec d, c * ∏ i ∈ S, w i) = 0 := by
  classical
  have hmiss : ∃ i : Fin d, i ∉ S := by
    by_contra h
    push Not at h
    have hu : S = Finset.univ := Finset.eq_univ_of_forall h
    simp [hu] at hS
  obtain ⟨i, hi⟩ := hmiss
  apply sum_zero_of_toggle i
  intro w
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  simp [toggle, Function.update_of_ne hji]

end PEqualNP.Outside.L_meta_33611.Normal.CubeParity

namespace PEqualNP.Outside.L_meta_33611.Normal.MonoSpan
open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F
abbrev Fn (n : ℕ) := Vec n → F

def mono {n : ℕ} (S : Finset (Fin n)) : Fn n := fun x => ∏ i ∈ S, x i

def degree (n q : ℕ) : Submodule F (Fn n) :=
  Submodule.span F { f | ∃ S : Finset (Fin n), S.card ≤ q ∧ mono S = f }

theorem mono_mem {n q} (S : Finset (Fin n)) (hS : S.card ≤ q) : mono S ∈ degree n q :=
  Submodule.subset_span ⟨S,hS,rfl⟩

theorem degree_mono {n a b : ℕ} (hab : a ≤ b) : degree n a ≤ degree n b := by
  apply Submodule.span_mono
  rintro x ⟨S,hS,rfl⟩
  exact ⟨S,hS.trans hab,rfl⟩

theorem constant {n q : ℕ} (c : F) : (fun _ : Vec n => c) ∈ degree n q := by
  have h := (degree n q).smul_mem c (mono_mem ∅ (Nat.zero_le q) : mono (∅ : Finset (Fin n)) ∈ degree n q)
  have he : c • mono (∅ : Finset (Fin n)) = (fun _ : Vec n => c) := by
    funext w
    simp [mono]
  rwa [he] at h

theorem coordinate {n : ℕ} (i : Fin n) : (fun w : Vec n => w i) ∈ degree n 1 := by
  have he : mono ({i} : Finset (Fin n)) = (fun w : Vec n => w i) := by
    funext w
    simp [mono]
  rw [← he]
  exact mono_mem {i} (by simp)

private theorem char_idem (q : F) : q*q=q := (by decide : ∀ q : F, q*q=q) q

theorem mono_mul {n : ℕ} (S T : Finset (Fin n)) : mono S * mono T = mono (S ∪ T) := by
  classical
  funext x
  induction T using Finset.induction_on with
  | empty => simp [mono]
  | insert a T ha ih =>
    by_cases hs : a ∈ S
    · have hu : a ∈ S ∪ T := Finset.mem_union_left T hs
      have hdup : x a * (∏ i ∈ S ∪ T, x i) = ∏ i ∈ S ∪ T, x i := by
        rw [← Finset.insert_erase hu, Finset.prod_insert (Finset.notMem_erase _ _), ← mul_assoc,
          char_idem]
      change (∏ i ∈ S, x i) * (∏ i ∈ insert a T, x i) = ∏ i ∈ S ∪ insert a T, x i
      change (∏ i ∈ S, x i) * (∏ i ∈ T, x i) = ∏ i ∈ S ∪ T, x i at ih
      rw [Finset.prod_insert ha, ← mul_left_comm, ih]
      rw [show S ∪ insert a T = S ∪ T by
        ext j
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h.symm ▸ hs)
          · exact Or.inr h
        · tauto]
      exact hdup
    · have hn : a ∉ S ∪ T := by simp [hs,ha]
      change (∏ i ∈ S, x i) * (∏ i ∈ insert a T, x i) = ∏ i ∈ S ∪ insert a T, x i
      change (∏ i ∈ S, x i) * (∏ i ∈ T, x i) = ∏ i ∈ S ∪ T, x i at ih
      rw [Finset.prod_insert ha, ← mul_left_comm, ih, Finset.union_insert, Finset.prod_insert hn]

theorem degree_mul {n a b : ℕ} {f g : Fn n}
    (hf : f ∈ degree n a) (hg : g ∈ degree n b) :
    f * g ∈ degree n (a+b) := by
  let W := degree n (a+b)
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => f * g ∈ W) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    change g ∈ Submodule.span F _ at hg
    refine Submodule.span_induction (p := fun g _ => mono S * g ∈ W) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨T,hT,rfl⟩
      rw [mono_mul]
      exact mono_mem _ ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
    · simpa using W.zero_mem
    · intro f g _ _ hf hg
      rw [mul_add]
      exact W.add_mem hf hg
    · intro c x _ hx
      have he : mono S * (c • x) = c • (mono S * x) := by
        funext y
        change (mono S y) * (c * x y) = c * (mono S y * x y)
        exact mul_left_comm _ _ _
      rw [he]
      exact W.smul_mem c hx
  · simpa using W.zero_mem
  · intro f g _ _ hf hg
    rw [add_mul]
    exact W.add_mem hf hg
  · intro c x _ hx
    have he : (c • x) * g = c • (x*g) := by
      funext y
      change (c * x y) * g y = c * (x y * g y)
      exact mul_assoc _ _ _
    rw [he]
    exact W.smul_mem c hx

theorem parity {n q : ℕ} {f : Fn n} (hf : f ∈ degree n q) (hqn : q < n) :
    (∑ w, f w) = 0 := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (∑ w, f w) = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    simpa [mono] using PEqualNP.Outside.L_meta_33611.Normal.CubeParity.sum_monomial_eq_zero S (hS.trans_lt hqn) 1
  · simp
  · intro a b _ _ ha hb
    simp [Pi.add_apply, Finset.sum_add_distrib, ha, hb]
  · intro c a _ ha
    simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha]

end PEqualNP.Outside.L_meta_33611.Normal.MonoSpan

namespace PEqualNP.Outside.L_meta_33611.Normal.ParityBudget
open scoped BigOperators
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan

private theorem linear_mem {d : ℕ} (L : Vec d →ₗ[F] F) : (fun w => L w) ∈ degree d 1 := by
  classical
  have he (w : Vec d) : w = ∑ j : Fin d, w j • (Pi.single j 1 : Vec d) := by
    funext i
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_ite_eq']
  have hL (w : Vec d) : L w = ∑ j : Fin d, L (Pi.single j 1) * w j := by
    conv_lhs => rw [he w]
    simp [map_sum, smul_eq_mul, mul_comm]
  let g : Fin d → Fn d := fun j => L (Pi.single j 1) • (fun w => w j)
  have hL' : (fun w => L w) = ∑ j : Fin d, g j := by
    funext w
    simpa [g, Finset.sum_apply] using hL w
  rw [hL']
  apply Submodule.sum_mem
  intro j _
  exact (degree d 1).smul_mem _ (coordinate j)

theorem affine_mem {d : ℕ} (c : F) (L : Vec d →ₗ[F] F) :
    (fun w => c + L w) ∈ degree d 1 :=
  (degree d 1).add_mem (constant c) (linear_mem L)

theorem affine_cube_budget {d k r : ℕ} (A : Vec d →ₗ[F] Vec k)
    (y₀ : Vec k) (b : Fin k → Fn d) (h : Fn d)
    (hb : ∀ i, b i ∈ degree d (r+1))
    (hh : h ∈ degree d (r+1))
    (hsum : (∑ w : Vec d, (h w + ∑ i : Fin k, (y₀ i + A w i) * b i w)) = 1) :
    d ≤ r + (if A = 0 then 1 else 2) := by
  classical
  let q : ℕ := if A = 0 then 0 else 1
  have hy : ∀ i : Fin k, (fun w : Vec d => y₀ i + A w i) ∈ degree d q := by
    intro i
    by_cases ha : A = 0
    · simpa [q,ha] using (constant (n := d) (q := 0) (y₀ i))
    · have hp := affine_mem (y₀ i) ((LinearMap.proj i).comp A)
      simpa [q,ha] using hp
  let u : Fin k → Fn d := fun i => (fun w => y₀ i + A w i) * b i
  have hprod : ∀ i, u i ∈ degree d (r+1+q) := by
    intro i
    have hi := degree_mul (hb i) (hy i)
    simpa [u, mul_comm] using hi
  have hu : (∑ i : Fin k, u i) ∈ degree d (r+1+q) := by
    apply Submodule.sum_mem
    intro i _
    exact hprod i
  have hde := (degree d (r+1+q)).add_mem (degree_mono (Nat.le_add_right _ _) hh) hu
  have he : h + (∑ i : Fin k, u i) = (fun w : Vec d =>
      h w + ∑ i : Fin k, (y₀ i + A w i) * b i w) := by
    funext w
    simp [u,Finset.sum_apply]
  rw [he] at hde
  have hn : d ≤ r+1+q := by
    by_contra ht
    push Not at ht
    have hz := parity hde ht
    rw [hsum] at hz
    contradiction
  by_cases e : A = 0
  · simpa [q,e] using hn
  · simpa [q,e, Nat.add_assoc] using hn

end PEqualNP.Outside.L_meta_33611.Normal.ParityBudget

namespace PEqualNP.Outside.L_meta_33611.Normal.Substitute
open scoped BigOperators
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan

def front {n : ℕ} (H : Fn n) (w : Vec n) : Vec (n+1) :=
  Fin.cases (H w) w

theorem substitute {n q : ℕ} (H : Fn n) (hH : H ∈ degree n 2)
    {f : Fn (n+1)} (hf : f ∈ degree (n+1) q) :
    (fun w => f (front H w)) ∈ degree n (q+1) := by
  classical
  let W := degree n (q+1)
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (fun w => f (front H w)) ∈ W)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    let U : Finset (Fin n) := (S.erase 0).preimage Fin.succ (Fin.succ_injective n).injOn
    have huI : U.image Fin.succ = S.erase 0 := by
      ext i
      cases i using Fin.cases with
      | zero => simp [U]
      | succ i => simp [U]
    have huC : U.card = (S.erase 0).card := by
      rw [← huI, Finset.card_image_of_injective U (Fin.succ_injective n)]
    have huP (w : Vec n) : (∏ i ∈ S.erase 0, front H w i) = mono U w := by
      rw [← huI, Finset.prod_image (Fin.succ_injective n).injOn]
      rfl
    by_cases hz : 0 ∈ S
    · have hU : U.card + 1 ≤ q := by
        rw [huC, Finset.card_erase_of_mem hz]
        have hp : 0 < S.card := Finset.card_pos.mpr ⟨0,hz⟩
        omega
      have hform : (fun w => mono S (front H w)) = mono U * H := by
        funext w
        change (∏ i ∈ S, front H w i) = mono U w * H w
        rw [← Finset.prod_erase_mul S (fun i => front H w i) hz, huP]
        rfl
      rw [hform]
      exact degree_mono (by omega) (degree_mul (mono_mem U (le_refl _)) hH)
    · have hU : U.card ≤ q := by
        rwa [huC, Finset.erase_eq_of_notMem hz]
      have hform : (fun w => mono S (front H w)) = mono U := by
        funext w
        simpa only [mono, Finset.erase_eq_of_notMem hz] using huP w
      rw [hform]
      exact mono_mem U (by omega)
  · exact W.zero_mem
  · intro a b _ _ ha hb
    exact W.add_mem ha hb
  · intro c a _ ha
    exact W.smul_mem c ha

end PEqualNP.Outside.L_meta_33611.Normal.Substitute

namespace PEqualNP.Outside.L_meta_33611.Normal.ProgramDegree
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan PEqualNP.Outside.L_meta_33611.Normal.Substitute PEqualNP.Outside.L_meta_33611.Normal.ParityBudget

inductive Run (n : ℕ) : ∀ r : ℕ, (Vec n → Vec (n+r)) → Prop
  | nil : Run n 0 id
  | cons {r : ℕ} {f : Vec n → Vec (n+r)} (hf : Run n r f)
      (a b : Fn (n+r)) (ha : a ∈ degree (n+r) 1) (hb : b ∈ degree (n+r) 1) :
      Run n (r+1) (fun w => front (a*b) (f w))

theorem degree_run {n r : ℕ} {g : Vec n → Vec (n+r)} (hg : Run n r g) :
    ∀ q, ∀ f : Fn (n+r), f ∈ degree (n+r) q → (fun w => f (g w)) ∈ degree n (q+r) := by
  induction hg with
  | nil =>
    intro q f hf
    simpa using hf
  | @cons r f h a b ha hb ih =>
    intro q fi hi
    have hp := degree_mul ha hb
    have h₀ := substitute (a*b) hp hi
    have h₁ := ih (q+1) (fun w => fi (front (a*b) w)) h₀
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁

end PEqualNP.Outside.L_meta_33611.Normal.ProgramDegree

namespace PEqualNP.Outside.L_meta_33611.Normal.SpanExact
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan

theorem as_affine {n : ℕ} {f : Fn n} (hf : f ∈ degree n 1) :
    ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ =>
    ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    by_cases he : S = ∅
    · refine ⟨1,0,?_⟩
      intro w
      simp [mono,he]
    · have hcard : S.card = 1 := by
        have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨0, LinearMap.proj j, by intro w; simp [mono]⟩
  · exact ⟨0,0,by simp⟩
  · rintro f g _ _ ⟨c,L,h⟩ ⟨d,K,hk⟩
    refine ⟨c+d,L+K,?_⟩
    intro w
    simp only [Pi.add_apply, LinearMap.add_apply, h, hk]
    abel
  · rintro c f _ ⟨d,L,h⟩
    refine ⟨c*d,c • L,?_⟩
    intro w
    simp [h, mul_add]

theorem iff_affine {n : ℕ} {f : Fn n} :
    f ∈ degree n 1 ↔ ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w := by
  refine ⟨as_affine, ?_⟩
  rintro ⟨c,L,h⟩
  rw [show f = (fun w => c + L w) from funext h]
  exact PEqualNP.Outside.L_meta_33611.Normal.ParityBudget.affine_mem c L

end PEqualNP.Outside.L_meta_33611.Normal.SpanExact

namespace PEqualNP.Outside.L_meta_33611.Normal.Wire
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan PEqualNP.Outside.L_meta_33611.Normal.SpanExact PEqualNP.Outside.L_meta_33611.Normal.Substitute

structure Wire (p n : ℕ) where
  x : Vec p →ₗ[F] F
  tail : Fn n
  tail_aff : tail ∈ degree n 1

def eval {p n : ℕ} (a : Wire p n) (q : Vec p) (w : Vec n) : F :=
  a.x q + a.tail w

def shift {p n : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1))
    (pivot : Fn n) (hp : pivot ∈ degree n 1) (a : Wire (p+1) n) : Wire p n :=
  ⟨a.x.comp R, a.tail + (a.x v) • pivot,
    (degree n 1).add_mem a.tail_aff ((degree n 1).smul_mem _ hp)⟩

theorem shift_eval {p n : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1))
    (pivot : Fn n) (hp : pivot ∈ degree n 1) (a : Wire (p+1) n)
    (q : Vec p) (w : Vec n) :
    eval (shift R v pivot hp a) q w = eval a (R q + pivot w • v) w := by
  simp [eval, shift, smul_eq_mul, mul_comm]
  abel

theorem kill_factor {p n : ℕ} (a : Wire (p+1) n) (ha : a.x ≠ 0) :
    ∃ (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1)),
      Function.Injective R ∧ ∀ q w,
        eval (shift R v a.tail a.tail_aff a) q w = 0 := by
  obtain ⟨R,v,hR,_,_,hp⟩ := PEqualNP.Outside.L_meta_33611.Normal.PivotStep.solve_one a.x ha
  refine ⟨R,v,hR,?_⟩
  intro q w
  rw [shift_eval]
  exact hp q (a.tail w)

private def tailLinear (n : ℕ) : Vec (n+1) →ₗ[F] Vec n :=
  LinearMap.pi (fun i => LinearMap.proj i.succ)

def extend {p n : ℕ} (a : Wire p n) : Wire p (n+1) where
  x := a.x
  tail := fun w => a.tail (tailLinear n w)
  tail_aff := by
    obtain ⟨c,L,h⟩ := as_affine a.tail_aff
    apply iff_affine.mpr
    exact ⟨c, L.comp (tailLinear n), fun w => h _⟩

theorem extend_eval {p n : ℕ} (a : Wire p n) (H : Fn n) (q : Vec p) (w : Vec n) :
    eval (extend a) q (front H w) = eval a q w := by
  rfl

def retained {p n : ℕ} : Wire p (n+1) :=
  ⟨0, (fun w => w 0), coordinate 0⟩

theorem retained_eval {p n : ℕ} (H : Fn n) (q : Vec p) (w : Vec n) :
    eval retained q (front H w) = H w := by
  simp [eval, retained, front]

end PEqualNP.Outside.L_meta_33611.Normal.Wire

namespace PEqualNP.Outside.L_meta_33611.Normal.GateDecode
open PEqualNP.CircuitLowerBounds
abbrev F := ZMod 2

def bit (x : F) : Bool := decide (x = 1)

def costly (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def legal (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def ops (g : Gate) (a b : F) : F :=
  match g.op, g.inputs with
  | .and, [] => 1
  | .and, [_] => a
  | .and, _ :: _ :: _ => a*b
  | .or, [] => 0
  | .or, [_] => a
  | .or, _ :: _ :: _ => a+b+a*b
  | .mod _, [] => 1
  | .mod _, [_] => 1+a
  | .mod _, _ :: _ :: _ => 1+a+b
  | .not, _ => 1+a
  | .maj, _ => 0

private theorem and1 : ∀ a : F, GateOp.and.eval [bit a] = bit a := by decide +kernel
private theorem or1 : ∀ a : F, GateOp.or.eval [bit a] = bit a := by decide +kernel
private theorem and2 : ∀ a b : F, GateOp.and.eval [bit a,bit b] = bit (a*b) := by decide +kernel
private theorem or2 : ∀ a b : F, GateOp.or.eval [bit a,bit b] = bit (a+b+a*b) := by decide +kernel
private theorem mod1 : ∀ a : F, (GateOp.mod 2).eval [bit a] = bit (1+a) := by decide +kernel
private theorem mod2 : ∀ a b : F, (GateOp.mod 2).eval [bit a,bit b] = bit (1+a+b) := by decide +kernel
private theorem not1 : ∀ a : F, GateOp.not.eval [bit a] = bit (1+a) := by decide +kernel

theorem decode (g : Gate) (u : ℕ → F) (h : legal g) :
    g.op.eval (g.inputs.map fun i => bit (u i)) =
      bit (ops g (u (g.inputs.getD 0 0)) (u (g.inputs.getD 1 0))) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := h
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | rfl | simp at h
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩
    · exact and1 (u i)
    · exact or1 (u i)
    · exact mod1 (u i)
    · exact not1 (u i)
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩
    · exact and2 (u i) (u j)
    · exact or2 (u i) (u j)
    · exact mod2 (u i) (u j)
    · simp at h
  · simp at hs

end PEqualNP.Outside.L_meta_33611.Normal.GateDecode

namespace PEqualNP.Outside.L_meta_33611.Normal.WireOps
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan PEqualNP.Outside.L_meta_33611.Normal.Wire

def zeroCostConst {p n : ℕ} (c : F) : Wire p n :=
  ⟨0, fun _ => c, constant c⟩

def plus {p n : ℕ} (a b : Wire p n) : Wire p n :=
  ⟨a.x+b.x, a.tail+b.tail, (degree n 1).add_mem a.tail_aff b.tail_aff⟩

theorem const_eval {p n} (c : F) (q : Vec p) (w : Vec n) :
    eval (zeroCostConst c) q w = c := by simp [eval,zeroCostConst]

theorem plus_eval {p n} (a b : Wire p n) (q : Vec p) (w : Vec n) :
    eval (plus a b) q w = eval a q w + eval b q w := by
  simp [plus, eval]
  abel

theorem factor_value_of_zero {p n} (a : Wire p n) (h : a.x = 0) (q : Vec p) (w : Vec n) :
    eval a q w = a.tail w := by simp [eval,h]

theorem retain_product {p n} (a b : Wire p n) (ha : a.x = 0) (hb : b.x = 0)
    (q : Vec p) (w : Vec n) :
    eval retained q (PEqualNP.Outside.L_meta_33611.Normal.Substitute.front (a.tail*b.tail) w) = eval a q w * eval b q w := by
  rw [retained_eval, factor_value_of_zero a ha, factor_value_of_zero b hb]
  rfl

end PEqualNP.Outside.L_meta_33611.Normal.WireOps

namespace PEqualNP.Outside.L_meta_33611.Normal.Normalized
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan PEqualNP.Outside.L_meta_33611.Normal.Wire PEqualNP.Outside.L_meta_33611.Normal.WireOps PEqualNP.Outside.L_meta_33611.Normal.Substitute
open PEqualNP.Outside.L_meta_33611.Normal.ProgramDegree

inductive Expr where
  | cn : F → Expr
  | rd : ℕ → Expr
  | add : Expr → Expr → Expr

def Expr.val (w : List F) : Expr → F
  | .cn c => c
  | .rd i => w.getD i 0
  | .add a b => a.val w + b.val w

def Expr.compile {p n : ℕ} (w : List (Wire p n)) : Expr → Wire p n
  | .cn c => zeroCostConst c
  | .rd i => w.getD i (zeroCostConst 0)
  | .add a b => plus (a.compile w) (b.compile w)

theorem list_getD_eval {p n : ℕ} (w : List (Wire p n)) (q : Vec p) (u : Vec n) (i : ℕ) :
    eval (w.getD i (zeroCostConst 0)) q u =
      (w.map fun z => eval z q u).getD i 0 := by
  induction w generalizing i with
  | nil => simp [const_eval]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Expr.compile_val {p n : ℕ} (w : List (Wire p n)) (q : Vec p) (u : Vec n) (e : Expr) :
    eval (e.compile w) q u = e.val (w.map fun z => eval z q u) := by
  induction e with
  | cn c => exact const_eval c q u
  | rd i => exact list_getD_eval w q u i
  | add a b ha hb => simp [Expr.compile, Expr.val, plus_eval, ha, hb]

inductive Ins where
  | free : Expr → Ins
  | paid : Expr → Expr → Expr → Ins

def Ins.cost : Ins → ℕ
  | .free _ => 0
  | .paid _ _ _ => 1

def Ins.val (w : List F) : Ins → F
  | .free e => e.val w
  | .paid e a b => e.val w + a.val w * b.val w

def Ins.step (w : List F) (g : Ins) : List F := w ++ [g.val w]

def embed {k p n : ℕ} (x : Fin k → Wire p n) : Vec p →ₗ[F] Vec k :=
  LinearMap.pi fun i => (x i).x

structure State (b k p r : ℕ) where
  env : Vec b → Vec (b+r)
  hEnv : Run b r env
  orig : Fin k → Wire p (b+r)
  hOrig : Function.Injective (embed orig)
  regs : List (Wire p (b+r))

def State.args {b k p r} (S : State b k p r) (q : Vec p) (u : Vec b) : Vec k :=
  fun i => eval (S.orig i) q (S.env u)

def State.values {b k p r} (S : State b k p r) (q : Vec p) (u : Vec b) : List F :=
  S.regs.map fun z => eval z q (S.env u)

def State.free {b k p r} (S : State b k p r) (e : Expr) : State b k p r :=
  { S with regs := S.regs ++ [e.compile S.regs] }

theorem State.free_ok {b k p r} (S : State b k p r) (e : Expr) (q : Vec p) (u : Vec b) :
    (S.free e).args q u = S.args q u ∧
    (S.free e).values q u = Ins.step (S.values q u) (.free e) := by
  refine ⟨rfl, ?_⟩
  simp [State.free, State.values, Ins.step, Ins.val, Expr.compile_val]

def State.retain {b k p r} (S : State b k p r) (e a c : Expr) : State b k p (r+1) :=
  let a' := a.compile S.regs
  let c' := c.compile S.regs
  ⟨fun u => front (a'.tail*c'.tail) (S.env u),
    .cons S.hEnv a'.tail c'.tail a'.tail_aff c'.tail_aff,
    fun i => extend (S.orig i), S.hOrig,
    (S.regs.map extend) ++ [plus (extend (e.compile S.regs)) retained]⟩

theorem State.retain_ok {b k p r} (S : State b k p r) (e a c : Expr)
    (ha : (a.compile S.regs).x = 0) (hc : (c.compile S.regs).x = 0)
    (q : Vec p) (u : Vec b) :
    (S.retain e a c).args q u = S.args q u ∧
    (S.retain e a c).values q u = Ins.step (S.values q u) (.paid e a c) := by
  constructor
  · funext i
    exact extend_eval (S.orig i) _ q (S.env u)
  · unfold State.retain State.values Ins.step Ins.val
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      plus_eval, extend_eval]
    rw [retain_product _ _ ha hc]
    simp [Expr.compile_val, extend_eval]

def State.discard {b k p r} (S : State b k (p+1) r) (e : Expr)
  (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R) (v : Vec (p+1))
  (pivot : Wire (p+1) (b+r)) : State b k p r :=
  let f := shift R v pivot.tail pivot.tail_aff
  ⟨S.env, S.hEnv, fun i => f (S.orig i), S.hOrig.comp hR,
    (S.regs.map f) ++ [f (e.compile S.regs)]⟩

theorem State.discard_ok {b k p r} (S : State b k (p+1) r) (e a c : Expr)
    (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R) (v : Vec (p+1))
    (pivot : Wire (p+1) (b+r)) (q : Vec p) (u : Vec b)
    (hz : eval (shift R v pivot.tail pivot.tail_aff (a.compile S.regs)) q (S.env u) *
          eval (shift R v pivot.tail pivot.tail_aff (c.compile S.regs)) q (S.env u) = 0) :
    let q₀ := R q + pivot.tail (S.env u) • v
    (S.discard e R hR v pivot).args q u = S.args q₀ u ∧
    (S.discard e R hR v pivot).values q u = Ins.step (S.values q₀ u) (.paid e a c) := by
  dsimp only
  constructor
  · funext i
    exact shift_eval R v pivot.tail pivot.tail_aff (S.orig i) q (S.env u)
  · unfold State.discard State.values Ins.step Ins.val
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      shift_eval]
    simp only [shift_eval] at hz
    simp [← Expr.compile_val, hz, shift_eval]

theorem zero_direction {n} (a : Wire 0 n) : a.x = 0 := by
  apply LinearMap.ext
  intro q
  have hq : q = 0 := Subsingleton.elim _ _
  rw [hq]
  exact map_zero a.x

theorem advance {b k p r} (S : State b k p r) (g : Ins) :
    ∃ (p' r' : ℕ) (S' : State b k p' r'),
      p+r' = p'+r+g.cost ∧
      ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧ S'.values q u = g.step (S.values q₀ u) := by
  cases g with
  | free e =>
    exact ⟨p,r,S.free e,by simp [Ins.cost],fun q u => ⟨q,S.free_ok e q u⟩⟩
  | paid e a c =>
    let aa := a.compile S.regs
    let cc := c.compile S.regs
    by_cases both : aa.x = 0 ∧ cc.x = 0
    · refine ⟨p,r+1,S.retain e a c,by simp [Ins.cost, Nat.add_assoc],?_⟩
      intro q u
      exact ⟨q,S.retain_ok e a c both.1 both.2 q u⟩
    · cases p with
      | zero => exact False.elim (both ⟨zero_direction aa,zero_direction cc⟩)
      | succ p =>
        have usePivot (z : Wire (p+1) (b+r)) (hz : z.x ≠ 0) (hz' : z = aa ∨ z = cc) :
            ∃ (p' r' : ℕ) (S' : State b k p' r'),
              (p+1)+r' = p'+r+(.paid e a c : Ins).cost ∧
              ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧
                S'.values q u = (.paid e a c : Ins).step (S.values q₀ u) := by
          obtain ⟨R,v,hR,hkill⟩ := kill_factor z hz
          refine ⟨p,r,S.discard e R hR v z,by simp only [Ins.cost]; omega,?_⟩
          intro q u
          have hh := hkill q (S.env u)
          refine ⟨_,S.discard_ok e a c R hR v z q u ?_⟩
          rcases hz' with h | h
          · subst z
            change _ at hh
            change eval (shift R v aa.tail aa.tail_aff aa) q (S.env u) *
              eval (shift R v aa.tail aa.tail_aff cc) q (S.env u) = 0
            rw [hh,zero_mul]
          · subst z
            change eval (shift R v cc.tail cc.tail_aff aa) q (S.env u) *
              eval (shift R v cc.tail cc.tail_aff cc) q (S.env u) = 0
            rw [hh,mul_zero]
        by_cases h : aa.x = 0
        · exact usePivot cc (fun z => both ⟨h,z⟩) (Or.inr rfl)
        · exact usePivot aa h (Or.inl rfl)

def paidCount (gs : List Ins) : ℕ := (gs.map Ins.cost).sum

theorem advance_all {b k : ℕ} (gs : List Ins) :
    ∀ p r (S : State b k p r),
      ∃ (p' r' : ℕ) (S' : State b k p' r'),
        p+r' = p'+r+paidCount gs ∧
        ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧
          S'.values q u = gs.foldl Ins.step (S.values q₀ u) := by
  induction gs with
  | nil =>
    intro p r S
    exact ⟨p,r,S,by simp [paidCount],fun q _ => ⟨q,rfl,rfl⟩⟩
  | cons g t ih =>
    intro p r S
    obtain ⟨p₁,r₁,S₁,h₁,e₁⟩ := advance S g
    obtain ⟨p₂,r₂,S₂,h₂,e₂⟩ := ih p₁ r₁ S₁
    refine ⟨p₂,r₂,S₂,?_ ,?_⟩
    · simp only [paidCount,List.map_cons,List.sum_cons] at *
      omega
    · intro q u
      obtain ⟨q₁,ha,hw⟩ := e₂ q u
      obtain ⟨q₀,ha₀,hw₀⟩ := e₁ q₁ u
      exact ⟨q₀,ha.trans ha₀,by rw [List.foldl_cons,hw,hw₀]⟩

end PEqualNP.Outside.L_meta_33611.Normal.Normalized

namespace PEqualNP.Outside.L_meta_33611.Normal.CircuitBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_33611.Normal.Normalized PEqualNP.Outside.L_meta_33611.Normal.GateDecode

private def free0 (x : F) : Ins := .free (.cn x)
private def read (i : ℕ) : Ins := .free (.rd i)
private def neg (i : ℕ) : Ins := .free (.add (.cn 1) (.rd i))

def lower (g : Gate) : Ins :=
  match g.op, g.inputs with
  | .and, [] => free0 1
  | .or, [] => free0 0
  | .and, [i] | .or, [i] => read i
  | .and, i :: j :: _ => .paid (.cn 0) (.rd i) (.rd j)
  | .or, i :: j :: _ => .paid (.add (.rd i) (.rd j)) (.rd i) (.rd j)
  | .mod _, [] => free0 1
  | .mod _, [i] => neg i
  | .mod _, i :: j :: _ => .free (.add (.add (.cn 1) (.rd i)) (.rd j))
  | .not, i :: _ => neg i
  | _, _ => free0 0

theorem lower_ops (g : Gate) (w : List F) (hg : legal g) :
    (lower g).val w =
      ops g (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := hg
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | rfl | simp at h
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;> rfl
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩
    · simp [lower, ops, Ins.val, Expr.val]
    · rfl
    · rfl
    · simp at h
  · simp at hs

private theorem bit_zero : bit 0 = false := by decide

private theorem getD_map_bit (w : List F) (i : ℕ) :
    (w.map bit).getD i false = bit (w.getD i 0) := by
  induction w generalizing i with
  | nil => simp [bit_zero]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_bridge (g : Gate) (w : List F) (h : legal g) :
    stepBool (w.map bit) g = ((lower g).step w).map bit := by
  unfold stepBool Ins.step
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq]
  simp only [getD_map_bit]
  rw [decode g _ h, lower_ops g w h]

theorem fold_bridge (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List F) :
    gs.foldl stepBool (w.map bit) = ((gs.map lower).foldl Ins.step w).map bit := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [step_bridge g w (hg g (by simp))]
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) _

theorem eval_bridge (C : Circuit) (hg : ∀ g ∈ C.gates, legal g) (w : List F) :
    C.eval (w.map bit) = bit (((C.gates.map lower).foldl Ins.step w).getD C.output 0) := by
  change (C.gates.foldl stepBool (w.map bit)).getD C.output false = _
  rw [fold_bridge C.gates hg, getD_map_bit]

noncomputable def paid (g : Gate) : Bool := @decide (costly g) (Classical.propDecidable _)

theorem cost_one (g : Gate) (hg : legal g) :
    (lower g).cost = @ite ℕ (costly g) (Classical.propDecidable _) 1 0 := by
  classical
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := hg
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> simp [lower,costly,Ins.cost,free0] at *
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;> simp [lower,costly,Ins.cost,read,neg]
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> simp [lower,costly,Ins.cost] at *
  · simp at hs

theorem cost_bridge (gs : List Gate) (hg : ∀ g ∈ gs, legal g) :
    paidCount (gs.map lower) = gs.countP paid := by
  classical
  induction gs with
  | nil => rfl
  | cons g t ih =>
    have ht := ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    simp only [paidCount,List.map_cons,List.sum_cons,List.countP_cons]
    change (lower g).cost + paidCount (t.map lower) = _
    rw [cost_one g (hg g (by simp)), ht]
    by_cases h : costly g <;> simp [paid,h,Nat.add_comm]

end PEqualNP.Outside.L_meta_33611.Normal.CircuitBridge

namespace PEqualNP.Outside.L_meta_33611.Normal.Pullback
open scoped BigOperators
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan PEqualNP.Outside.L_meta_33611.Normal.ParityBudget

theorem pullback {d n q : ℕ} (Y : Vec d →ₗ[F] Vec n) (y₀ : Vec n)
    {f : Fn n} (hf : f ∈ degree n q) :
    (fun w => f (y₀ + Y w)) ∈ degree d q := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (fun w => f (y₀ + Y w)) ∈ degree d q)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    apply degree_mono hS
    clear hS
    induction S using Finset.induction_on with
    | empty =>
      have eq : (fun w => mono (∅ : Finset (Fin n)) (y₀ + Y w)) = (fun _ : Vec d => (1:F)) := by
        funext w
        simp [mono]
      rw [eq]
      exact constant 1
    | insert i s hi ih =>
      have he : (fun w => mono (insert i s) (y₀ + Y w)) =
          (fun w => y₀ i + Y w i) * (fun w => mono s (y₀ + Y w)) := by
        funext w
        simp [mono, Finset.prod_insert hi,Pi.mul_apply]
      rw [he,Finset.card_insert_of_notMem hi, Nat.add_comm]
      exact degree_mul (affine_mem (y₀ i) ((LinearMap.proj i).comp Y)) ih
  · exact (degree d q).zero_mem
  · intro a b _ _ ha hb
    exact (degree d q).add_mem ha hb
  · intro c a _ ha
    exact (degree d q).smul_mem c ha

def appendLinear {d k t : ℕ} (B : Vec d →ₗ[F] Vec k) (T : Vec d →ₗ[F] Vec t) :
    Vec d →ₗ[F] Vec (k+t) :=
  LinearMap.pi (Fin.addCases (fun i => (LinearMap.proj i).comp B)
    (fun j => (LinearMap.proj j).comp T))

theorem append_affine {d k t : ℕ} (B : Vec d →ₗ[F] Vec k) (T : Vec d →ₗ[F] Vec t)
    (y₀ : Vec k) (z₀ : Vec t) (w : Vec d) :
    Fin.append (y₀ + B w) (z₀ + T w) = Fin.append y₀ z₀ + appendLinear B T w := by
  funext i
  cases i using Fin.addCases with
  | left i => simp [appendLinear]
  | right i => simp [appendLinear]

end PEqualNP.Outside.L_meta_33611.Normal.Pullback

namespace PEqualNP.Outside.L_meta_33611.Normal.Lower

open scoped BigOperators
open PEqualNP.Outside.L_meta_33611.Normal.MonoSpan PEqualNP.Outside.L_meta_33611.Normal.Wire PEqualNP.Outside.L_meta_33611.Normal.WireOps
open PEqualNP.Outside.L_meta_33611.Normal.Normalized PEqualNP.Outside.L_meta_33611.Normal.ProgramDegree PEqualNP.Outside.L_meta_33611.Normal.Pullback
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_33611.Normal.CircuitBridge
open PEqualNP.Outside.L_meta_33611.Normal.GateDecode (bit legal)

private def xreg {k b : ℕ} (i : Fin k) : Wire k b :=
  ⟨LinearMap.proj i, fun _ => 0, constant 0⟩

private def baseReg {k b : ℕ} (i : Fin b) : Wire k b :=
  ⟨0, fun w => w i, coordinate i⟩

private def start (k b : ℕ) : State b k k 0 :=
  ⟨id, .nil, fun i => xreg i, by
    intro q s h
    funext i
    exact congrFun h i,
    (List.ofFn fun i : Fin k => xreg i) ++ (List.ofFn fun i : Fin b => baseReg i)⟩

private theorem args_start {k b : ℕ} (q : Vec k) (u : Vec b) :
    (start k b).args q u = q := by
  funext i
  simp [start,State.args,eval,xreg]

private theorem regs_start {k b : ℕ} (q : Vec k) (u : Vec b) :
    (start k b).values q u = List.ofFn q ++ List.ofFn u := by
  simp [start,State.values,eval,xreg,baseReg,List.map_ofFn,Function.comp_def]

private theorem ofFn_append {k t : ℕ} (y : Vec k) (z : Vec t) :
    List.ofFn (Fin.append y z) = List.ofFn y ++ List.ofFn z := by
  rw [List.ofFn_add]
  simp only [Fin.append_left', Fin.append_right]

private def areg {b k p r : ℕ} (S : State b k p r) (i : ℕ) : Wire p (b+r) :=
  S.regs.getD i (zeroCostConst 0)

theorem bit_inj : Function.Injective bit := by
  exact (by decide : ∀ a b : F, bit a = bit b → a = b)

def bits {n : ℕ} (x : Vec n) : List Bool := List.ofFn (fun i => bit (x i))

set_option maxHeartbeats 1500000 in
theorem promisedReadout {n : ℕ} (Y : Set (Vec n)) (y₀ : Vec n) (anchor : y₀ ∈ Y)
    (g : Vec n → F) (C : Circuit) (hlegal : ∀ a ∈ C.gates, legal a)
    (hfit : ∀ x y : Vec n, y ∈ Y →
      C.eval (bits x ++ bits y) = bit (dotProduct x y + g y)) :
    ∃ (r : ℕ) (env : Vec n → Vec (n+r)) (o : Fn (n+r)) (p : Fin n → Fn (n+r)),
      Module.finrank F (Submodule.span F ((fun y => y-y₀) '' Y)) + r ≤ C.gates.countP paid ∧
      Run n r env ∧ o ∈ degree (n+r) 1 ∧ (∀ i, p i ∈ degree (n+r) 1) ∧
      ∀ y ∈ Y, g y = o (env y) + ∑ i, y i * p i (env y) := by
  classical
  let gs := C.gates.map lower
  have hFld (x y : Vec n) (hy : y ∈ Y) :
      (gs.foldl Ins.step (List.ofFn x ++ List.ofFn y)).getD C.output 0 = dotProduct x y + g y := by
    apply bit_inj
    rw [← eval_bridge C hlegal]
    simpa [bits,List.map_ofFn,Function.comp_def] using hfit x y hy
  obtain ⟨p,r,S,hs,hstate⟩ := advance_all gs n 0 (start n n)
  let O := areg S C.output
  let A := embed S.orig
  let b : Vec n → Vec n := fun u i => (S.orig i).tail (S.env u)
  let h : Vec n → F := fun u => O.tail (S.env u)
  have hv (q : Vec p) (y : Vec n) (hy : y ∈ Y) :
      dotProduct (A q+b y) y + g y=O.x q+h y := by
    obtain ⟨q₀,hq,hrs⟩ := hstate q y
    have ha : A q+b y=q₀ := by
      change S.args q y=q₀
      simpa only [args_start] using hq
    have hO : eval O q (S.env y)=(S.values q y).getD C.output 0 :=
      list_getD_eval S.regs q (S.env y) _
    change dotProduct (A q+b y) y+g y=eval O q (S.env y)
    rw [ha,hO,hrs,regs_start]
    exact (hFld q₀ y hy).symm

  have slope (q : Vec p) (y : Vec n) (hy : y ∈ Y) : dotProduct (A q) y = O.x q := by
    have hq := hv q y hy
    have hz := hv 0 y hy
    rw [add_dotProduct] at hq
    simp only [map_zero, zero_add] at hz
    linear_combination hq - hz
  have bound := PEqualNP.Outside.L_meta_33611.freeDirectionRank A.range Y y₀ (by
    intro y hy u hu
    obtain ⟨q, rfl⟩ := hu
    rw [dotProduct_comm y, dotProduct_comm y₀, slope q y hy, slope q y₀ anchor])
  have inj : Function.Injective A := S.hOrig
  rw [LinearMap.finrank_range_of_inj inj, Module.finrank_fin_fun] at bound
  have exactBound : p + Module.finrank F (Submodule.span F ((fun y => y-y₀) '' Y)) ≤ n :=
    bound
  have key : paidCount gs = C.gates.countP paid := cost_bridge C.gates hlegal
  refine ⟨r,S.env,O.tail,(fun i => (S.orig i).tail),by omega,S.hEnv,O.tail_aff,
    (fun i => (S.orig i).tail_aff),?_⟩
  intro y hy
  have hf := hv 0 y hy
  simp only [map_zero,zero_add] at hf
  change dotProduct (b y) y + g y=h y at hf
  have he : g y=h y+dotProduct (b y) y := by
    rw [←hf]
    conv_rhs => rw [add_comm (dotProduct (b y) y) (g y)]
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
  simpa [h,b,dotProduct,mul_comm] using he
end PEqualNP.Outside.L_meta_33611.Normal.Lower
namespace PEqualNP.Outside.L_meta_33611.Normal
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
def Quad {n} (q : V n → F) := ∃ (s : F) (h : V n) (M : Fin n → V n),
    ∀ x, q x=s+dotProduct h x+∑ i,∑ j, M i j*x i*x j

structure Features {n : ℕ} (g : V n → F) (r : ℕ) where
  A : Fin r × Fin 3 → V n
  q : V n → F
  hq : Quad q
  H : Fin r → V n → F
  co : Fin r → F
  start : Fin r → Fin 2 → F
  earlier : Fin r → Fin 2 → Fin r → F
  strict : ∀ i k j, i.val ≤ j.val → earlier i k j=0
  gate : ∀ i x, H i x =
    (start i 0+dotProduct (A (i,0)) x+∑ j, earlier i 0 j * H j x) *
    (start i 1+dotProduct (A (i,1)) x+∑ j, earlier i 1 j * H j x)
  out : ∀ x, g x=q x+∑ i, (co i+dotProduct (A (i,2)) x)*H i x

open MonoSpan (degree Fn)
open ProgramDegree (Run)
structure WRep (n r : Nat) where
  s : F
  raw : V n
  h : V r

def WRep.val {n r} (w : WRep n r) (H : Fin r → V n → F) (x : V n) :=
  w.s+dotProduct w.raw x+∑ j, w.h j*H j x

def WRep.plus {n r} (w v : WRep n r) : WRep n r := ⟨w.s+v.s,w.raw+v.raw,w.h+v.h⟩
def WRep.scale {n r} (c : F) (w : WRep n r) : WRep n r := ⟨c*w.s,c • w.raw,c • w.h⟩
def WRep.const {n r} (c : F) : WRep n r := ⟨c,0,0⟩
def WRep.extend {n r} (w : WRep n r) : WRep n (r+1) := ⟨w.s,w.raw,Fin.snoc w.h 0⟩
def WRep.top (n r : Nat) : WRep n (r+1) := ⟨0,0,Fin.snoc (fun _ => 0) 1⟩

theorem WRep.plus_val {n r} (w v : WRep n r) (H x) :
    (w.plus v).val H x=w.val H x+v.val H x := by
  simp only [plus,val,dotProduct,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  ring
theorem WRep.scale_val {n r} (w : WRep n r) (c : F) (H x) :
    (w.scale c).val H x=c*w.val H x := by
  simp [scale,val,dotProduct,Finset.mul_sum,mul_add,mul_assoc]
theorem WRep.const_val {n r} (c : F) (H x) : (const (n:=n) (r:=r) c).val H x=c := by simp [const,val]
theorem WRep.extend_val {n r} (w : WRep n r) (H : Fin r → V n → F) (h : V n → F) (x) :
    w.extend.val (Fin.snoc H h) x=w.val H x := by
  simp only [extend,val,Fin.sum_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,zero_mul,add_zero]
theorem WRep.top_val {n r} (H : Fin r → V n → F) (h : V n → F) (x) :
    (top n r).val (Fin.snoc H h) x=h x := by
  simp [top,val,Fin.sum_univ_castSucc]

structure Bank (n r : Nat) where
  H : Fin r → V n → F
  w : Fin r → Fin 2 → WRep n r
  bound : ∀ i k j, i.val≤j.val → (w i k).h j=0
  gates : ∀ i x, H i x=(w i 0).val H x * (w i 1).val H x

def Bank.empty (n) : Bank n 0 := ⟨Fin.elim0,Fin.elim0,(fun i => i.elim0),(fun i => i.elim0)⟩

def Bank.snoc {n r} (B : Bank n r) (a b : WRep n r) : Bank n (r+1) where
  H := Fin.snoc B.H (fun x => a.val B.H x*b.val B.H x)
  w := Fin.snoc (fun i k => (B.w i k).extend) (fun k => if k=0 then a.extend else b.extend)
  bound := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro k j hj
      have e : j=Fin.last r := Fin.ext (by have := j.isLt;change r≤j.val at hj;change j.val=r;omega)
      subst j
      by_cases e : k=0 <;> simp [WRep.extend,e]
    · intro k j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [WRep.extend]
      · intro le
        simpa [WRep.extend] using B.bound i k j le
  gates := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro x
      simp [WRep.extend_val]
    · intro x
      simpa [WRep.extend_val] using B.gates i x

def Real {n r} (B : Bank n r) (f : V n → F) := ∃ w : WRep n r, ∀ x, f x=w.val B.H x

theorem real_const {n r} (B : Bank n r) (c : F) : Real B (fun _ => c) :=
  ⟨WRep.const c, fun x => (WRep.const_val ..).symm⟩
theorem real_plus {n r} {B : Bank n r} {f g : V n → F} (a : Real B f) (b : Real B g) :
    Real B (fun x => f x+g x) := by
  obtain ⟨w,hw⟩ := a;obtain ⟨v,hv⟩ := b
  exact ⟨w.plus v,fun x => by change f x+g x=_;rw [WRep.plus_val,hw,hv]⟩
theorem real_scale {n r} {B : Bank n r} {f : V n → F} (c : F) (a : Real B f) :
    Real B (fun x => c*f x) := by
  obtain ⟨w,hw⟩ := a
  exact ⟨WRep.scale c w,fun x => by change c*f x=_;rw [WRep.scale_val,hw]⟩
theorem real_sum {n r} {B : Bank n r} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {f : ι → V n → F} (h : ∀ i∈S, Real B (f i)) : Real B (fun x => ∑ i∈S, f i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using real_const B 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact real_plus (h i (by simp)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem real_linear {n r t} {B : Bank n r} {env : V n → V t}
    (hs : ∀ j, Real B (fun x => env x j)) {f : Fn t} (hf : f∈degree t 1) :
    Real B (fun x => f (env x)) := by
  classical
  obtain ⟨c,L,he⟩ := SpanExact.as_affine hf
  have basis (v : V t) : v=∑ j : Fin t, v j • (Pi.single j 1 : V t) := by
    funext i
    simp [Pi.single_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_ite_eq']
  have calcL (v : V t) : L v=∑ j, L (Pi.single j 1) * v j := by
    conv_lhs => rw [basis v]
    simp [map_sum,smul_eq_mul,mul_comm]
  have cv : (fun x => f (env x))=(fun x => c+∑ j, L (Pi.single j 1)*env x j) := by
    funext x
    exact (he (env x)).trans (congrArg (c+·) (calcL (env x)))
  rw [cv]
  exact real_plus (real_const B c) (real_sum Finset.univ (fun j _ => real_scale _ (hs j)))

theorem bank_run {n r} {env : V n → V (n+r)} (run : Run n r env) :
    ∃ B : Bank n r, ∀ i, Real B (fun x => env x i) := by
  induction run with
  | nil =>
    refine ⟨Bank.empty n,?_⟩
    intro j
    exact ⟨⟨0,Pi.single j 1,0⟩,fun x => by simp [WRep.val,dotProduct,Pi.single_apply]⟩
  | @cons r f hf a b ha hb ih =>
    obtain ⟨B,hB⟩ := ih
    obtain ⟨ca,ea⟩ := real_linear hB ha
    obtain ⟨cb,eb⟩ := real_linear hB hb
    refine ⟨B.snoc ca cb,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨WRep.top n r,?_⟩
      intro x
      change a (f x)*b (f x) = (WRep.top n r).val (Fin.snoc B.H _) x
      dsimp only at ea eb
      rw [WRep.top_val,ea,eb]
    · obtain ⟨w,hw⟩ := hB j
      refine ⟨w.extend,?_⟩
      intro x
      change f x j=w.extend.val (Fin.snoc B.H _) x
      dsimp only at hw
      rw [WRep.extend_val,hw]

def arrA {n r} (B : Bank n r) (ww : Fin n → WRep n r) (p : Fin r × Fin 3) : V n :=
  if p.2=0 then (B.w p.1 0).raw else if p.2=1 then (B.w p.1 1).raw else fun i => (ww i).h p.1

def writeQ {n r} (o : WRep n r) (ww : Fin n → WRep n r) (x : V n) :=
  o.s+dotProduct (o.raw + fun i => (ww i).s) x+∑ i,∑ j, (ww i).raw j*x i*x j

theorem agg {n r} (B : Bank n r) (o : WRep n r) (ww : Fin n → WRep n r) (x : V n) :
    o.val B.H x + ∑ i, x i*(ww i).val B.H x =
      writeQ o ww x + ∑ i, (o.h i+dotProduct (arrA B ww (i,2)) x)*B.H i x := by
  simp only [WRep.val,writeQ,arrA,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
    if_false,dotProduct, Pi.add_apply, add_mul,mul_add,Finset.sum_add_distrib,
    Finset.mul_sum,Finset.sum_mul]
  have h₁ : (∑ i, x i*(ww i).s)=∑ i, (ww i).s*x i := by
    apply Finset.sum_congr rfl;intro i _;ring
  have h₂ : (∑ i,∑ j, x i*((ww i).raw j*x j))= ∑ i,∑ j, (ww i).raw j*x i*x j := by
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
  have h₃ : (∑ i,∑ j, x i*((ww i).h j*B.H j x))=∑ j,∑ i, ((ww i).h j*x i)*B.H j x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
  rw [h₁,h₂,h₃]
  ring

theorem assemble {n r} {g : V n → F} {env : V n → V (n+r)}
    (run : Run n r env) {o : Fn (n+r)} {p : Fin n → Fn (n+r)}
    (ho : o∈degree (n+r) 1) (hp : ∀ i,p i∈degree (n+r) 1)
    (h : ∀ y,g y=o (env y)+∑ i, y i*p i (env y)) : Nonempty (Features g r) := by
  classical
  obtain ⟨B,hB⟩ := bank_run run
  obtain ⟨out,eo⟩ := real_linear hB ho
  choose ww ew using fun i => real_linear hB (hp i)
  refine ⟨⟨arrA B ww,writeQ out ww,⟨_,_,_,fun _ => rfl⟩,B.H,out.h,
    (fun i k => (B.w i k).s),(fun i k => (B.w i k).h),B.bound,?_,?_⟩⟩
  · intro i x
    simpa [arrA,WRep.val] using B.gates i x
  · intro x
    dsimp only at eo ew
    rw [h,eo]
    simp_rw [ew]
    exact agg B out ww x

private theorem splitOne {n r : ℕ} (g : V n → F) (S : Features g r) (small : r ≤ 1) :
    ∃ (a b c : V n) (f : V n → F), Quad f ∧
      ∀ y, g y = f y + dotProduct a y * dotProduct b y * dotProduct c y := by
  classical
  have cases : r = 0 ∨ r = 1 := by omega
  rcases cases with rfl | rfl
  · refine ⟨0, 0, 0, S.q, S.hq, ?_⟩
    intro y
    simpa using S.out y
  · have gate (x : V n) : S.H 0 x =
        (S.start 0 0 + dotProduct (S.A (0,0)) x) *
        (S.start 0 1 + dotProduct (S.A (0,1)) x) := by
      simpa [Fin.sum_univ_one, S.strict 0 0 0 le_rfl, S.strict 0 1 0 le_rfl]
        using S.gate 0 x
    obtain ⟨f, hf, he⟩ := PEqualNP.Outside.L_meta_33611.residualGivesOne
      Finset.univ g S.q (S.A (0,0)) (S.A (0,1)) (S.A (0,2))
      (S.start 0 0) (S.start 0 1) (S.co 0) S.hq (by
        intro x _
        rw [S.out, Fin.sum_univ_one, gate]
        ring)
    exact ⟨_, _, _, f, hf, fun y => he y (Finset.mem_univ y)⟩

theorem promiseOneResidual {n : ℕ} (Y : Set (V n)) (y₀ : V n) (anchor : y₀ ∈ Y)
    (g : V n → F) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : ∀ a ∈ C.gates, GateDecode.legal a)
    (fit : ∀ x y, y ∈ Y → C.eval (Lower.bits x ++ Lower.bits y) =
      GateDecode.bit (dotProduct x y + g y))
    (cost : C.gates.countP CircuitBridge.paid ≤
      Module.finrank F (Submodule.span F ((fun y => y-y₀) '' Y)) + 1) :
    ∃ (a b c : V n) (f : V n → F), Quad f ∧
      ∀ y ∈ Y, g y = f y + dotProduct a y * dotProduct b y * dotProduct c y := by
  classical
  obtain ⟨r, env, o, p, bound, run, ho, hp, readout⟩ :=
    Lower.promisedReadout Y y₀ anchor g C legal fit
  let extended : V n → F := fun y => o (env y) + ∑ i, y i * p i (env y)
  obtain ⟨S⟩ := assemble (g := extended) run ho hp (fun _ => rfl)
  have small : r ≤ 1 := Nat.le_of_add_le_add_left (bound.trans cost)
  obtain ⟨a,b,c,f,hf,he⟩ := splitOne extended S small
  exact ⟨a,b,c,f,hf,fun y hy => (readout y hy).trans (he y)⟩

theorem promiseNoResidual {n : ℕ} (Y : Set (V n)) (y₀ : V n) (anchor : y₀ ∈ Y)
    (g : V n → F) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : ∀ a ∈ C.gates, GateDecode.legal a)
    (fit : ∀ x y, y ∈ Y → C.eval (Lower.bits x ++ Lower.bits y) =
      GateDecode.bit (dotProduct x y + g y))
    (cost : C.gates.countP CircuitBridge.paid ≤
      Module.finrank F (Submodule.span F ((fun y => y-y₀) '' Y))) :
    ∃ f : V n → F, Quad f ∧ ∀ y ∈ Y, g y = f y := by
  classical
  obtain ⟨r, env, o, p, bound, run, ho, hp, readout⟩ :=
    Lower.promisedReadout Y y₀ anchor g C legal fit
  let extended : V n → F := fun y => o (env y) + ∑ i, y i * p i (env y)
  obtain ⟨S⟩ := assemble (g := extended) run ho hp (fun _ => rfl)
  have small : r ≤ 0 := Nat.le_of_add_le_add_left (show _ ≤ _ + 0 from bound.trans cost)
  haveI : IsEmpty (Fin r) := ⟨fun i => by have := i.isLt; omega⟩
  exact ⟨S.q, S.hq, fun y hy => (show g y = extended y from readout y hy).trans
    (by simpa using S.out y)⟩

theorem qadd {n} {f g : V n → F} (hf : Quad f) (hg : Quad g) :
    Quad (fun x => f x+g x) := by
  obtain ⟨s,h,M,he⟩ := hf
  obtain ⟨t,l,N,le⟩ := hg
  refine ⟨s+t,h+l,M+N,?_⟩
  intro x
  simp only [he,le,dotProduct,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  ring

theorem qzero (n : Nat) : Quad (fun _ : V n => (0:F)) := by
  exact ⟨0,0,0,by simp⟩

theorem qscale {n} {f : V n → F} (c : F) (hf : Quad f) :
    Quad (fun x => c*f x) := by
  obtain ⟨s,h,M,e⟩ := hf
  refine ⟨c*s,c • h,c • M,?_⟩
  intro x
  simp [e,dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_add,mul_assoc]

theorem qsum {n} {ι : Type*} [DecidableEq ι] (S : Finset ι) {f : ι → V n → F}
    (h : ∀ i∈S, Quad (f i)) : Quad (fun x => ∑ i∈S,f i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using qzero n
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact qadd (h i (by simp)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem qmul {n} (s t : F) (a b : V n) :
    Quad (fun x => (s+dotProduct a x)*(t+dotProduct b x)) := by
  refine ⟨s*t,s • b + t • a,fun i j => b i*a j,?_⟩
  intro x
  simp only [dotProduct, Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,mul_add,
    Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  simp only [mul_comm,mul_assoc,mul_left_comm]
  first | rfl | ring | simp only [Finset.sum_comm,add_assoc,add_left_comm,add_comm]

theorem promiseHullDimension {k t n : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) × (Fin t → ZMod 2))
    (E : Finset (Fin k → ZMod 2)) (o : Fin k → ZMod 2) (ho : o ∈ E)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (contain : ∀ s ∈ E, ∀ z, e.symm (s,z) - a ∈ U) :
    t + Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ((fun s => s-o) '' (↑E : Set (Fin k → ZMod 2)))) ≤
      Module.finrank (ZMod 2) U := by
  let S := Fin k → ZMod 2
  let D := Fin t → ZMod 2
  let W := Submodule.span (ZMod 2) ((fun s => s-o) '' (↑E : Set S))
  let f : S →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    e.symm.toLinearMap.comp (LinearMap.inl (ZMod 2) S D)
  have diff (s : S) (hs : s ∈ E) (z : D) : e.symm (s-o,z) ∈ U := by
    have hh := U.sub_mem (contain s hs z) (contain o ho 0)
    rw [sub_sub_sub_cancel_right] at hh
    have pair : ((s,z) - (o,0) : S × D) = (s-o,z) := Prod.ext rfl (sub_zero z)
    have linear : e.symm ((s,z) - (o,0)) = e.symm (s,z) - e.symm (o,0) :=
      map_sub e.symm (s,z) (o,0)
    rwa [← linear, pair] at hh
  have incl : W ≤ U.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    exact diff s hs 0
  let A : (W × D) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    e.symm.toLinearMap.comp (W.subtype.prodMap LinearMap.id)
  have hA (x : W × D) : A x ∈ U := by
    have hu : e.symm (x.1.val,0) ∈ U := incl x.1.property
    have hv : e.symm (0,x.2) ∈ U := by simpa using diff o ho x.2
    have hadd := U.add_mem hu hv
    rw [← e.symm.map_add] at hadd
    simpa [A] using hadd
  let B := A.codRestrict U hA
  have hi : Function.Injective B := by
    intro x y h
    have h' : ((x.1 : S),x.2) = ((y.1 : S),y.2) :=
      e.symm.injective (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (congrArg (fun p : S × D => p.1) h'))
      (congrArg (fun p : S × D => p.2) h')
  have result := LinearMap.finrank_le_finrank_of_injective hi
  rw [Module.finrank_prod, show Module.finrank (ZMod 2) D = t from Module.finrank_fin_fun _] at result
  exact (Nat.add_comm ..) ▸ result

noncomputable def pullCoeff {k n : ℕ} (L : V k →ₗ[F] V n) (a : V n) : V k :=
  (dotProductEquiv F (Fin k)).symm (((dotProductEquiv F (Fin n)) a).comp L)

theorem dot_pull {k n : ℕ} (L : V k →ₗ[F] V n) (a : V n) (s : V k) :
    dotProduct a (L s) = dotProduct (pullCoeff L a) s := by
  exact (congrArg (fun f : Module.Dual F (V k) => f s)
    ((dotProductEquiv F (Fin k)).apply_symm_apply (((dotProductEquiv F (Fin n)) a).comp L))).symm

theorem quad_pull {k n : ℕ} (L : V k →ₗ[F] V n) {q : V n → F} (hq : Quad q) :
    Quad (fun s => q (L s)) := by
  classical
  obtain ⟨d, l, M, h⟩ := hq
  let m := fun i : Fin n => (dotProductEquiv F (Fin k)).symm ((LinearMap.proj i).comp L)
  have rows (i : Fin n) (s : V k) : L s i = dotProduct (m i) s :=
    (congrArg (fun f : Module.Dual F (V k) => f s)
      ((dotProductEquiv F (Fin k)).apply_symm_apply ((LinearMap.proj i).comp L))).symm
  have lin : Quad (fun s => d + dotProduct (pullCoeff L l) s) :=
    ⟨d, pullCoeff L l, 0, by simp⟩
  have terms (i j : Fin n) : Quad (fun s => M i j * (L s i * L s j)) := by
    apply qscale
    simpa only [rows, zero_add] using qmul 0 0 (m i) (m j)
  have mat := qsum Finset.univ (fun (i : Fin n) _ =>
    qsum Finset.univ (fun (j : Fin n) _ => terms i j))
  convert qadd lin mat using 1
  funext s
  simp only [h (L s), dot_pull L l, mul_assoc]

theorem selectorNecessary {k t : ℕ}
    (e : V (k+t) ≃ₗ[F] V k × V t) (Q : V (k+t) → F) (hq : Quad Q)
    (h : V k → F) (E : Finset (V k)) (o : V k) (ho : o ∈ E)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (legal : ∀ a ∈ C.gates, GateDecode.legal a)
    (win : ∀ s ∈ E, ∀ x b, let y := e.symm (s,b)
      C.eval (Lower.bits x ++ Lower.bits y) = GateDecode.bit (dotProduct x y + Q y + h s)) :
    let p := t + Module.finrank F (Submodule.span F ((fun s => s-o) '' (↑E : Set (V k))))
    (C.gates.countP CircuitBridge.paid ≤ p → ∃ f : V k → F, Quad f ∧ ∀ s ∈ E, h s = f s) ∧
    (C.gates.countP CircuitBridge.paid ≤ p+1 → ∃ (a b c : V k) (f : V k → F), Quad f ∧
      ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s) := by
  classical
  dsimp only
  let Y : Set (V (k+t)) := {y | (e y).1 ∈ E}
  let y₀ := e.symm (o,0)
  let G := fun y => Q y + h (e y).1
  let L := e.symm.toLinearMap.comp (LinearMap.inl F (V k) (V t))
  have co (s : V k) : e (L s) = (s,0) := e.apply_symm_apply (s,0)
  have origin : y₀ ∈ Y := by simpa [y₀, Y] using ho
  have mem (s : V k) (hs : s ∈ E) : L s ∈ Y := by simpa [Y, co] using hs
  have rank := promiseHullDimension e E o ho (Submodule.span F ((fun y => y-y₀) '' Y))
    y₀ (by
      intro s hs b
      apply Submodule.subset_span
      exact ⟨e.symm (s,b), by simpa [Y] using hs, rfl⟩)
  have fit (x y : V (k+t)) (hy : y ∈ Y) : C.eval (Lower.bits x ++ Lower.bits y) =
      GateDecode.bit (dotProduct x y + G y) := by
    have hwin := win (e y).1 hy x (e y).2
    simpa [G, add_assoc] using hwin
  have recover (s : V k) : h s = G (L s) + Q (L s) := by
    simp only [G, co]
    rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  constructor
  · intro cost
    obtain ⟨q, hq', agree⟩ := promiseNoResidual Y y₀ origin G C legal fit (cost.trans rank)
    exact ⟨fun s => q (L s) + Q (L s), qadd (quad_pull L hq') (quad_pull L hq),
      fun s hs => (recover s).trans (by rw [agree (L s) (mem s hs)])⟩
  · intro cost
    obtain ⟨a,b,c,q,hq',agree⟩ := promiseOneResidual Y y₀ origin G C legal fit
      (cost.trans (Nat.add_le_add_right rank 1))
    refine ⟨pullCoeff L a, pullCoeff L b, pullCoeff L c, fun s => q (L s) + Q (L s),
      qadd (quad_pull L hq') (quad_pull L hq), ?_⟩
    intro s hs
    rw [recover s, agree (L s) (mem s hs), dot_pull L a, dot_pull L b, dot_pull L c]
    ring

end PEqualNP.Outside.L_meta_33611.Normal

namespace PEqualNP.Outside.L_meta_33611
lemma finiteMixedLoss {I : Type*} [Fintype I] (v score : I → ℝ) (h : ∑ i, v i = 1) :
    ∑ i, v i * (1 - score i) = 1 - ∑ i, v i * score i := by
  simp [mul_sub, Finset.sum_sub_distrib, h]

lemma finiteCircuitCoverTransfer {I J C : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (L : I → J → ℝ) (w : J → ℝ) (loss : C → J → ℝ)
    (hw : ∀ j, 0 < w j) (hL : ∀ i j, 0 ≤ L i j) (hpos : ∀ i, ∃ j, 0 < L i j)
    (realize : ∀ i, ∃ c, ∀ j, loss c j ≤ L i j)
    (valid : ∀ (c : C) (z : J → ℝ), (∀ j, 0 ≤ z j) → (∀ i, 1 ≤ ∑ j, L i j * z j) →
      1 ≤ ∑ j, loss c j * z j) :
    let cover := fun z : J → ℝ => (∀ j, 0 ≤ z j) ∧ ∀ i, 1 ≤ ∑ j, L i j * z j
    let cost := fun z : J → ℝ => ∑ j, w j * z j
    let feasible := fun q : ℝ => ∃ (N : ℕ) (cs : Fin N → C) (v : Fin N → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ ∀ j, ∑ i, v i * loss (cs i) j ≤ q * w j
    ∃ z, cover z ∧ (∀ y, cover y → cost z ≤ cost y) ∧ 0 < cost z ∧
      ∀ q, feasible q ↔ 1 ≤ q * cost z := by
  classical
  dsimp only
  obtain ⟨z, hz, hm, hzp, hq⟩ := finiteMatrixCoverDual L w hw hL hpos
  refine ⟨z, hz, hm, hzp, fun q => ⟨?_, ?_⟩⟩
  · rintro ⟨N, cs, v, hv, hsum, hcs⟩
    exact finiteMatrixWeakDual (fun i j => loss (cs i) j) w v z q hv hsum hz.1
      (fun i => valid (cs i) z hz.1 hz.2) hcs
  · intro h
    obtain ⟨p, hp, hp1, hpf⟩ := (hq q).mpr h
    choose c hc using realize
    let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
    refine ⟨_, fun i => c (e i), fun i => p (e i), fun i => hp _, ?_, ?_⟩
    · exact (e.sum_comp p).trans hp1
    · intro j
      calc
        _ ≤ ∑ i, p (e i) * L (e i) j := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hc (e i) j) (hp _)
        _ = ∑ i, p i * L i j := e.sum_comp (fun i => p i * L i j)
        _ ≤ q * w j := hpf j

theorem finiteSetLossTransfer {S I C : Type*} [DecidableEq S] [Fintype I] [Nonempty I]
    (E : Finset S) (he : E.Nonempty) (T : I → Finset S) (a : I → ℝ)
    (row : ∀ i, (T i).Nonempty ∧ T i ⊆ E ∧ 0 < a i)
    (w : S → ℝ) (hw : ∀ s ∈ E, 0 < w s) (loss : C → S → ℝ)
    (realize : ∀ i, ∃ c, ∀ s ∈ E, loss c s ≤ if s ∈ T i then a i else 0)
    (valid : ∀ (c : C) (z : S → ℝ), (∀ s ∈ E, 0 ≤ z s) → (∀ i, 1 ≤ a i * ∑ s ∈ T i, z s) →
      1 ≤ ∑ s ∈ E, loss c s * z s) :
    let cov := fun (z : S → ℝ) => (∀ s ∈ E, 0 ≤ z s) ∧ ∀ i, 1 ≤ a i * ∑ s ∈ T i, z s
    let cost := fun (z : S → ℝ) => ∑ s ∈ E, w s * z s
    let feasible := fun (q : ℝ) => ∃ (N : ℕ) (cs : Fin N → C) (v : Fin N → ℝ),
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ ∀ s ∈ E, ∑ i, v i * loss (cs i) s ≤ q * w s
    ∃ z, cov z ∧ (∀ y, cov y → cost z ≤ cost y) ∧ 0 < cost z ∧
      ∀ q : ℝ, feasible q ↔ 1 ≤ q * cost z := by
  classical
  intro cov cost feasible
  letI : Nonempty E := ⟨⟨he.choose, he.choose_spec⟩⟩
  let L := fun (i : I) (s : E) => if s.val ∈ T i then a i else (0 : ℝ)
  let ext := fun (z : E → ℝ) (s : S) => if hs : s ∈ E then z ⟨s,hs⟩ else 0
  have ext_eq (z : E → ℝ) (s : E) : ext z s.val = z s := dif_pos s.property
  have dot (z : S → ℝ) (i : I) : (∑ s : E, L i s * z s.val) = a i * ∑ s ∈ T i, z s := by
    change (∑ s : E, (if s.val ∈ T i then a i else 0) * z s.val) = _
    rw [Finset.sum_coe_sort E (fun s : S => (if s ∈ T i then a i else 0) * z s), Finset.mul_sum]
    simp only [ite_mul, zero_mul, ← Finset.sum_filter]
    have eq : E.filter (fun s => s ∈ T i) = T i := by
      ext s
      exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨(row i).2.1 h, h⟩⟩
    rw [eq]
  have valid' (c : C) (z : E → ℝ) (hn : ∀ s, 0 ≤ z s)
      (hc : ∀ i, 1 ≤ ∑ s, L i s * z s) : 1 ≤ ∑ s : E, loss c s.val * z s := by
    have heq : ∀ s : E, z s = ext z s.val := fun s => (ext_eq z s).symm
    simp_rw [heq] at hc ⊢
    rw [Finset.sum_coe_sort E (fun s : S => loss c s * ext z s)]
    exact valid c (ext z) (fun s hs => by simpa [ext,hs] using hn ⟨s,hs⟩)
      (fun i => (dot (ext z) i) ▸ hc i)
  have hp (i : I) : ∃ s : E, 0 < L i s := by
    obtain ⟨s,hs⟩ := (row i).1
    exact ⟨⟨s,(row i).2.1 hs⟩, by simpa [L,hs] using (row i).2.2⟩
  obtain ⟨z,hz,hmin,hpos,hq⟩ := finiteCircuitCoverTransfer L (fun s : E => w s.val)
    (fun c (s : E) => loss c s.val) (fun s => hw _ s.property)
    (fun i s => by dsimp [L]; split <;> simp [(row i).2.2.le]) hp
    (fun i => (realize i).imp fun c hc s => hc s.val s.property) valid'
  have costEq (g : S → ℝ) : (∑ s : E, w s.val * g s.val) = cost g := Finset.sum_coe_sort E (fun s => w s * g s)
  have costEx : (∑ s : E, w s.val * z s) = cost (ext z) := by
    simpa only [ext_eq] using costEq (ext z)
  refine ⟨ext z, ⟨fun s hs => by simpa [ext,hs] using hz.1 ⟨s,hs⟩, ?_⟩, ?_, costEx ▸ hpos, ?_⟩
  · intro i
    simpa only [← dot (ext z) i, ext_eq] using hz.2 i
  · intro y hy
    rw [← costEx, ← costEq y]
    exact hmin (fun s => y s.val) ⟨fun s => hy.1 _ s.property, fun i => (dot y i).symm ▸ hy.2 i⟩
  · intro q
    rw [← costEx, ← hq q]
    constructor
    · rintro ⟨N,cs,v,hn,hs,hv⟩
      exact ⟨N,cs,v,hn,hs,fun s => hv s.val s.property⟩
    · rintro ⟨N,cs,v,hn,hs,hv⟩
      exact ⟨N,cs,v,hn,hs,fun s h => hv ⟨s,h⟩⟩

end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611.SelectorLP

open Upper PEqualNP.CircuitLowerBounds

def side {k : ℕ} (E : Finset (V k)) (a : V k) (v : F) := E.filter (fun s => dotProduct a s ≠ v)

def repair {k : ℕ} (E : Finset (V k)) (h : V k → F) (T : Finset (V k)) :=
  T ⊆ E ∧ ∃ f : V k → F, Quad f ∧ ∀ s ∈ E, h s = f s + if s ∈ T then 1 else 0

def cover {k : ℕ} (E : Finset (V k)) (h : V k → F) (z : V k → ℝ) :=
  (∀ s ∈ E, 0 ≤ z s) ∧
  (∀ a v, (side E a v).Nonempty → side E a v ≠ E → 1 ≤ ∑ s ∈ side E a v, z s) ∧
  ∀ T, repair E h T → (∀ U, U ⊂ T → ¬repair E h U) → 1 ≤ 2 * ∑ s ∈ T, z s

theorem exactOptimization {k t : ℕ} (e : V (k+t) ≃ₗ[F] V k × V t) (Q : V (k+t) → F)
    (hQ : Quad Q) (h : V k → F) (E : Finset (V k)) (o : V k) (ho : o ∈ E)
    (none : ¬repair E h ∅) (w : V k → ℝ) (hw : ∀ s ∈ E, 0 < w s)
    (cuts : ∀ a v, (side E a v).Nonempty → side E a v ≠ E →
      ∃ C, Fits (k+t) (budget t E o) C ∧ ∀ s ∈ E,
        Score e Q h C s = if dotProduct a s = v then 1 else 0)
    (valid : ∀ C, Fits (k+t) (budget t E o) C → ∀ z, cover E h z →
      1 ≤ ∑ s ∈ E, (1 - Score e Q h C s) * z s) :
    let total := fun z : V k → ℝ => ∑ s ∈ E, w s * z s
    let feasible := fun (q : ℝ) => ∃ (N : ℕ) (Cs : Fin N → Circuit) (v : Fin N → ℝ),
      (∀ i, Fits (k+t) (budget t E o) (Cs i) ∧ 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
      ∀ s ∈ E, 1 - (∑ i, v i * Score e Q h (Cs i) s) ≤ q * w s
    ∃ z, cover E h z ∧ (∀ y, cover E h y → total z ≤ total y) ∧ 0 < total z ∧
      ∀ q, feasible q ↔ 1 ≤ q * total z := by
  classical
  intro total feasible
  let cut := fun (T : Finset (V k)) => ∃ a v, T = side E a v ∧ T.Nonempty ∧ T ≠ E
  let minr := fun T => repair E h T ∧ ∀ U, U ⊂ T → ¬repair E h U
  let I := {T : Finset (V k) // cut T} ⊕ {T : Finset (V k) // minr T}
  let T : I → Finset (V k) := Sum.elim Subtype.val Subtype.val
  let a : I → ℝ := Sum.elim (fun _ => 1) (fun _ => 2)
  have someRepair : ∃ T, repair E h T := selectorRepairExists E h
  obtain ⟨M, hM, hMin⟩ := existsMinimalRepair (repair E h) someRepair
  letI : Nonempty I := ⟨Sum.inr ⟨M,hM,hMin⟩⟩
  have rows (i : I) : (T i).Nonempty ∧ T i ⊆ E ∧ 0 < a i := by
    rcases i with ⟨U, a',v,rfl,hn,hp⟩ | ⟨U,hr,hm⟩
    · exact ⟨hn, Finset.filter_subset _ _, zero_lt_one⟩
    · exact ⟨Finset.nonempty_iff_ne_empty.mpr (fun hU => none (hU ▸ hr)), hr.1, by norm_num [a]⟩
  have coveq (z : V k → ℝ) : cover E h z ↔
      (∀ s ∈ E, 0 ≤ z s) ∧ ∀ i, 1 ≤ a i * ∑ s ∈ T i, z s := by
    constructor
    · rintro ⟨hn,hc,hr⟩
      refine ⟨hn, ?_⟩
      rintro (⟨U,a',v,rfl,hn',hp⟩ | ⟨U,hu,hm⟩)
      · simpa [a,T] using hc a' v hn' hp
      · exact hr _ hu hm
    · rintro ⟨hn,hrow⟩
      refine ⟨hn, ?_, fun U hu hm => hrow (Sum.inr ⟨U,hu,hm⟩)⟩
      intro a' v hn' hp
      simpa [a,T] using hrow (Sum.inl ⟨side E a' v,a',v,rfl,hn',hp⟩)
  let PC := {C : Circuit // Fits (k+t) (budget t E o) C}
  let loss := fun (c : PC) s => 1 - Score e Q h c.val s
  have realize (i : I) : ∃ c : PC, ∀ s ∈ E, loss c s ≤ if s ∈ T i then a i else 0 := by
    rcases i with ⟨U,a',v,rfl,hn,hp⟩ | ⟨U,hr,hm⟩
    · obtain ⟨C,good,hval⟩ := cuts a' v hn hp
      refine ⟨⟨C,good⟩, fun s hs => ?_⟩
      change 1 - Score e Q h C s ≤ if s ∈ side E a' v then 1 else 0
      rw [hval s hs]
      by_cases hh : dotProduct a' s = v <;> simp [side, hs, hh]
    · obtain ⟨C,good,hval⟩ := realizeRepairLoss e Q hQ h E U o hr.2
      exact ⟨⟨C,good⟩, fun s hs => (hval s hs).le⟩
  obtain ⟨z,cz,zm,zp,eqv⟩ := finiteSetLossTransfer E ⟨o,ho⟩ T a rows w hw loss realize
    (fun c y hn hc => valid c.val c.property y ((coveq y).mpr ⟨hn,hc⟩))
  refine ⟨z,(coveq z).mpr cz,fun y hy => zm y ((coveq y).mp hy), zp, ?_⟩
  intro q
  rw [← eqv q]
  constructor
  · rintro ⟨N,C,v,hc,hs,hv⟩
    refine ⟨N,fun i => ⟨C i,(hc i).1⟩,v, fun i => (hc i).2, hs, fun s hsel => ?_⟩
    exact (finiteMixedLoss v (fun i => Score e Q h (C i) s) hs).trans_le (hv s hsel)
  · rintro ⟨N,C,v,hc,hs,hv⟩
    refine ⟨N,fun i => (C i).val,v,fun i => ⟨(C i).property, hc i⟩, hs,fun s hsel => ?_⟩
    exact (finiteMixedLoss v (fun i => Score e Q h (C i).val s) hs).symm.trans_le (hv s hsel)

end PEqualNP.Outside.L_meta_33611.SelectorLP

namespace PEqualNP.Outside.L_meta_33611.CutAttainment

abbrev F := ZMod 2
abbrev V (k : ℕ) := Fin k → F

abbrev differences {k : ℕ} (E : Finset (V k)) (r : V k) :=
  Submodule.span F ((fun s : V k => s-r) '' (↑E : Set (V k)))

theorem selectorCut {k : ℕ} (E : Finset (V k)) (o : V k) (a : V k) (v : F)
    (hn : (E.filter (fun s => dotProduct a s ≠ v)).Nonempty)
    (hp : E.filter (fun s => dotProduct a s ≠ v) ≠ E) :
    ∃ r ∈ E, dotProduct a r = v ∧
      let K := differences (E.filter (fun s => dotProduct a s = v)) r
      K < differences E o ∧ ∀ s ∈ E, s-r ∈ K ↔ dotProduct a s = v := by
  classical
  obtain ⟨r,hr,hrv⟩ : ∃ r ∈ E, dotProduct a r = v := by
    by_contra! h
    exact hp (Finset.Subset.antisymm (Finset.filter_subset _ _)
      (fun s hs => Finset.mem_filter.mpr ⟨hs,h s hs⟩))
  refine ⟨r,hr,hrv,?_⟩
  let T := E.filter (fun s => dotProduct a s = v)
  let K := differences T r
  let W := differences E o
  let L : V k →ₗ[F] F := ∑ i : Fin k, a i • LinearMap.proj i
  have ev (s : V k) : L s = dotProduct a s := by
    simp [L, dotProduct, LinearMap.sum_apply]
  have ker : K ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    change L (s-r) = 0
    rw [map_sub, ev, ev, (Finset.mem_filter.mp hs).2, hrv, sub_self]
  have memW (s : V k) (hs : s ∈ E) : s-o ∈ W :=
    Submodule.subset_span ⟨s,hs,rfl⟩
  have wd (s : V k) (hs : s ∈ E) : s-r ∈ W := by
    simpa only [sub_sub_sub_cancel_right] using W.sub_mem (memW s hs) (memW r hr)
  have incl : K ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    exact wd s (Finset.mem_filter.mp hs).1
  have classify (s : V k) (hs : s ∈ E) : s-r ∈ K ↔ dotProduct a s = v := by
    constructor
    · intro h
      have z : L (s-r) = 0 := ker h
      rw [map_sub, ev, ev, hrv] at z
      exact sub_eq_zero.mp z
    · intro h
      exact Submodule.subset_span ⟨s, Finset.mem_filter.mpr ⟨hs,h⟩,rfl⟩
  refine ⟨lt_of_le_of_ne incl ?_, classify⟩
  intro eq
  obtain ⟨s, hs⟩ := hn
  obtain ⟨hs, hv⟩ := Finset.mem_filter.mp hs
  change K = W at eq
  exact hv ((classify s hs).mp (eq.ge (wd s hs)))

theorem liftedSelectorCut {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (E : Finset (V k)) (o a : V k) (v : F)
    (hn : (E.filter (fun s => dotProduct a s ≠ v)).Nonempty)
    (hp : E.filter (fun s => dotProduct a s ≠ v) ≠ E) :
    ∃ (y₀ : V n) (U : Submodule F (V n)),
      Module.finrank F U + 1 ≤ t + Module.finrank F (differences E o) ∧
      ∀ s ∈ E, ∀ b : V t, e.symm (s,b) - y₀ ∈ U ↔ dotProduct a s = v := by
  obtain ⟨r, _, _, hK, classify⟩ := selectorCut E o a v hn hp
  let K := differences (E.filter (fun s => dotProduct a s = v)) r
  let A : (K × V t) →ₗ[F] V n :=
    e.symm.toLinearMap.comp (K.subtype.prodMap LinearMap.id)
  have hi : Function.Injective A := by
    intro x y h
    have eq : ((x.1 : V k),x.2) = ((y.1 : V k),y.2) := e.symm.injective h
    exact Prod.ext (Subtype.ext (congrArg (fun p : V k × V t => p.1) eq))
      (congrArg (fun p : V k × V t => p.2) eq)
  refine ⟨e.symm (r,0), LinearMap.range A, ?_, ?_⟩
  · have lt : Module.finrank F K < Module.finrank F (differences E o) :=
      Submodule.finrank_lt_finrank_of_lt hK
    have dim := (LinearEquiv.ofInjective A hi).finrank_eq
    rw [Module.finrank_prod, show Module.finrank F (V t) = t from Module.finrank_fin_fun _] at dim
    omega
  · intro s hs b
    have sub : e.symm (s,b) - e.symm (r,0) = e.symm (s-r,b) := by
      rw [← map_sub]
      exact congrArg e.symm (Prod.ext rfl (sub_zero b))
    rw [sub, ← classify s hs]
    constructor
    · rintro ⟨⟨u,w⟩,hw⟩
      have pair : ((u : V k),w) = (s-r,b) := e.symm.injective hw
      have left : (u : V k) = s-r := congrArg (fun p : V k × V t => p.1) pair
      rw [← left]
      exact u.property
    · intro hk
      exact ⟨(⟨s-r,hk⟩,b),rfl⟩

theorem projectionClassifies {n : ℕ} (U : Submodule F (V n)) (base : V n)
    (P : V n → V n) (fix : ∀ y, y-base ∈ U → P y = y)
    (image : ∀ y, P y-base ∈ U) (y : V n) :
    P y = y ↔ y-base ∈ U := ⟨fun he => he ▸ image y, fix y⟩

theorem walshOrthogonal {n : ℕ} (u v : V n) (huv : u ≠ v) (c d : F) :
    (∑ x : V n, if decide (dotProduct x u + c = 1) = decide (dotProduct x v + d = 1)
      then (1:ℝ) else -1) = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, u i ≠ v i := by
    by_contra! h
    exact huv (funext h)
  let f := fun x : V n =>
    if decide (dotProduct x u + c = 1) = decide (dotProduct x v + d = 1) then (1:ℝ) else -1
  let w : V n := Pi.single i 1
  have flip : ∀ m s h j : F, h ≠ j →
      (decide (m+h=1) = decide (s+j=1) ↔ ¬decide (m=1) = decide (s=1)) := by decide
  have anti (x : V n) : f (x+w) = - f x := by
    dsimp [f]
    simp only [add_dotProduct, w, single_dotProduct, one_mul]
    rw [add_right_comm (dotProduct x u) (u i) c, add_right_comm (dotProduct x v) (v i) d]
    simp only [flip _ _ _ _ hi]
    by_cases h : decide (dotProduct x u+c = 1) = decide (dotProduct x v+d = 1) <;> simp [h]
  have shifted := Equiv.sum_comp (Equiv.addRight w) f
  change (∑ x : V n, f (x+w)) = ∑ x : V n, f x at shifted
  simp only [anti, Finset.sum_neg_distrib] at shifted
  change ∑ x : V n, f x = 0
  linarith

theorem projectedSelectorScore {n t : ℕ} (Y : V t → V n) (P : V n → V n)
    (off : V n → F) (target : V t → F) (keep : Prop) [Decidable keep]
    (fixed : ∀ b, P (Y b) = Y b ↔ keep)
    (matched : keep → ∀ b, off (Y b) = target b) :
    ((∑ x : V n, ∑ b : V t,
      if decide (dotProduct x (P (Y b)) + off (P (Y b)) = 1) =
          decide (dotProduct x (Y b) + target b = 1) then (1:ℝ) else -1) / 2^(n+t)) =
        if keep then 1 else 0 := by
  classical
  by_cases hk : keep
  · have fixed' (b : V t) := (fixed b).2 hk
    simp [hk, fixed', matched hk, F, V, ZMod.card, pow_add]
  · rw [ite_eq_right hk, Finset.sum_comm]
    have zero (b : V t) := walshOrthogonal (P (Y b)) (Y b) (fun eq => hk ((fixed b).1 eq))
      (off (P (Y b))) (target b)
    simp only [zero, Finset.sum_const_zero, zero_div]

end PEqualNP.Outside.L_meta_33611.CutAttainment

namespace PEqualNP.Outside.L_meta_33611.CutAttainment

open PEqualNP.CircuitLowerBounds

theorem attainedCut {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (Q : V n → F) (h : V k → F)
    (hQ : ∃ (a : F) (l : V n) (M : Fin n → V n),
      ∀ y, Q y = Upper.quadVal a l M y)
    (E : Finset (V k)) (o cut : V k) (v : F)
    (one : ∃ (a b c : V k) (f : V k → F),
      (∃ (z : F) (l : V k) (M : Fin k → V k), ∀ s, f s = Upper.quadVal z l M s) ∧
      ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s)
    (hn : (E.filter (fun s => dotProduct cut s ≠ v)).Nonempty)
    (hp : E.filter (fun s => dotProduct cut s ≠ v) ≠ E) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
      (∀ g ∈ C.gates, Upper.GateDecode.legal g) ∧
      C.gates.countP Upper.CircuitBridge.paid ≤ t + Module.finrank F (differences E o) ∧
      ∀ s ∈ E, ((∑ x : V n, ∑ b : V t, let y := e.symm (s,b)
        if C.eval (Upper.Input (x,y)) = decide (dotProduct x y + Q y + h s = 1)
        then (1:ℝ) else -1) / 2^(n+t)) = if dotProduct cut s = v then 1 else 0 := by
  obtain ⟨base,U,hdim,classification⟩ := liftedSelectorCut e E o cut v hn hp
  obtain ⟨K,u,hu,fix,image⟩ := Upper.hullChart U base
  obtain ⟨a₁,l₁,M₁,hQ⟩ := hQ
  obtain ⟨a,b,c,f,⟨a₂,l₂,M₂,hf⟩,hh⟩ := one
  let sel := (LinearMap.fst F (V k) (V t)).comp e.toLinearMap
  let P := Upper.reconstruct base K u
  let off := fun y : V n => Upper.quadVal a₁ l₁ M₁ y +
    (Upper.quadVal a₂ l₂ M₂ (sel y) + dotProduct a (sel y) * dotProduct b (sel y) * dotProduct c (sel y))
  obtain ⟨C,back,good,cost,eval⟩ := Upper.compilePromise sel base K u hu a₁ a₂ l₁ l₂ M₁ M₂
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (fun _ : Fin 1 => c)
  refine ⟨C,back,good,cost.trans hdim,?_⟩
  have val (x y : V n) : C.eval (Upper.Input (x,y)) =
      decide (dotProduct x (P y) + off (P y) = 1) := by
    simpa [P, off, Upper.GateDecode.bit, add_assoc] using eval x y
  intro s hs
  let Y := fun z : V t => e.symm (s,z)
  have sY (z : V t) : sel (Y z) = s := by simp [Y, sel]
  have bias (z : V t) : off (Y z) = Q (Y z) + h s := by
    simp only [off, sY, hQ, hh s hs, hf]
  have same (z : V t) : P (Y z) = Y z ↔ dotProduct cut s = v :=
    (projectionClassifies U base P fix image (Y z)).trans (classification s hs z)
  have score := projectedSelectorScore Y P off (fun z => Q (Y z) + h s)
    (dotProduct cut s = v) same (fun _ => bias)
  simp only [val, add_assoc]
  exact score

theorem realizeSideLoss {n k t : ℕ} (e : V n ≃ₗ[F] V k × V t)
    (Q : V n → F) (hq : Upper.Quad Q) (h : V k → F) (E : Finset (V k)) (o cut : V k) (v : F)
    (one : ∃ (a b c : V k) (f : V k → F), Upper.Quad f ∧ ∀ s ∈ E,
      h s = f s + dotProduct a s * dotProduct b s * dotProduct c s)
    (hn : (E.filter (fun s => dotProduct cut s ≠ v)).Nonempty)
    (hp : E.filter (fun s => dotProduct cut s ≠ v) ≠ E) :
    ∃ C : Circuit, Upper.Fits n (Upper.budget t E o) C ∧ ∀ s ∈ E,
      1 - Upper.Score e Q h C s = if s ∈ E.filter (fun s => dotProduct cut s ≠ v)
        then (1 : ℝ) else 0 := by
  obtain ⟨C,back,good,cost,score⟩ := attainedCut e Q h hq E o cut v one hn hp
  refine ⟨C,⟨back,good,cost⟩,?_⟩
  intro s hs
  have value : Upper.Score e Q h C s = if dotProduct cut s = v then 1 else 0 := score s hs
  by_cases hv : dotProduct cut s = v <;> simp [value, hs, hv]

end PEqualNP.Outside.L_meta_33611.CutAttainment

namespace PEqualNP.Outside.L_meta_33611.Weighted

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

def chi (a : F) : ℤ := if a = 1 then -1 else 1
def sg (b : Bool) : ℤ := if b then -1 else 1
def b2f (b : Bool) : F := if b then 1 else 0

lemma zmod2_add_self (a : F) : a + a = 0 := by fin_cases a <;> decide
lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by fin_cases a <;> fin_cases b <;> decide
lemma zmod2_mul_self (a : F) : a * a = a := by revert a; decide
lemma zmod2_eq_one_of_ne_zero (a : F) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl
lemma zmod2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma chi_zero : chi 0 = 1 := by decide
lemma chi_one : chi 1 = -1 := by decide
lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by fin_cases a <;> fin_cases b <;> decide
lemma chi_sub (a b : F) : chi (a - b) = chi a * chi b := by fin_cases a <;> fin_cases b <;> decide
lemma chi_abs (a : F) : (chi a).natAbs = 1 := by fin_cases a <;> decide
lemma sg_xor (b : Bool) (a : F) : sg (xor b (decide (a = 1))) = sg b * chi a := by
  cases b <;> fin_cases a <;> decide
lemma agree_eq_sg_chi (b : Bool) (a : F) :
    (if b = decide (a = 1) then (1 : ℤ) else -1) = sg b * chi a := by
  cases b <;> fin_cases a <;> decide
lemma sg_eq_chi_b2f (b : Bool) : sg b = chi (b2f b) := by cases b <;> decide
lemma b2f_decide (a : F) : b2f (decide (a = 1)) = a := by revert a; decide
lemma decide_b2f (b : Bool) : decide (b2f b = 1) = b := by cases b <;> decide
lemma dec_add (a b : F) : decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
lemma dec_mul (a b : F) : decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by cases a <;> cases b <;> decide
lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by cases a <;> cases b <;> decide
lemma vec_sub_eq_add {n : ℕ} (x y : Fin n → F) : x - y = x + y := by
  funext j; exact zmod2_sub_eq_add (x j) (y j)
lemma vec_add_self {n : ℕ} (x : Fin n → F) : x + x = 0 := by
  funext j; exact zmod2_add_self (x j)

lemma card_fin_fun (n : ℕ) : Fintype.card (Fin n → F) = 2 ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma card_submodule {n : ℕ} (U : Submodule F (Fin n → F)) [Fintype U] :
    Fintype.card U = 2 ^ (Module.finrank F U) := by
  classical
  let e : (Fin (Module.finrank F U) → F) ≃ₗ[F] U :=
    LinearEquiv.ofFinrankEq (R := F) (M := Fin (Module.finrank F U) → F) (M' := U)
      (by rw [Module.finrank_fin_fun])
  rw [← Fintype.card_congr e.toEquiv, card_fin_fun]

def dotLin {n : ℕ} (v : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun := fun x => dotProduct v x
  map_add' := fun x y => dotProduct_add v x y
  map_smul' := fun c x => by simp [dotProduct_smul]

def dualMap {n : ℕ} (U : Submodule F (Fin n → F)) : (Fin n → F) →ₗ[F] (U →ₗ[F] F) where
  toFun := fun x => (dotLin x).comp U.subtype
  map_add' := fun x y => by
    ext u; simp [dotLin, add_dotProduct]
  map_smul' := fun c x => by
    ext u; simp [dotLin, smul_dotProduct]

def perp {n : ℕ} (U : Submodule F (Fin n → F)) : Submodule F (Fin n → F) :=
  LinearMap.ker (dualMap U)

lemma mem_perp {n : ℕ} (U : Submodule F (Fin n → F)) (x : Fin n → F) :
    x ∈ perp U ↔ ∀ u ∈ U, dotProduct x u = 0 := by
  simp only [perp, LinearMap.mem_ker, LinearMap.ext_iff, dualMap, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.comp_apply, Submodule.coe_subtype, dotLin, LinearMap.zero_apply,
    Subtype.forall]

lemma proj_of_isCompl {V : Type*} [AddCommGroup V] [Module F V]
    (U W : Submodule F V) (hUW : IsCompl U W) :
    ∃ π : V →ₗ[F] U, ∀ u : U, π u.1 = u := by
  classical
  have huniq : ∀ x : V, ∃! p : U × W, (p.1 : V) + (p.2 : V) = x := by
    intro x
    obtain ⟨u, w, hxw, hu⟩ := Submodule.existsUnique_add_of_isCompl hUW x
    refine ⟨(u, w), hxw, fun p hp => ?_⟩
    have h := hu p.1 p.2 hp
    exact Prod.ext h.1 h.2
  choose f hf1 hf2 using huniq
  refine ⟨{
    toFun := fun x => (f x).1
    map_add' := fun x y => by
      have hsum : (((f x).1 + (f y).1 : U) : V) + (((f x).2 + (f y).2 : W) : V) = x + y := by
        have hx : ((f x).1 : V) + ((f x).2 : V) = x := hf1 x
        have hy : ((f y).1 : V) + ((f y).2 : V) = y := hf1 y
        calc (((f x).1 + (f y).1 : U) : V) + (((f x).2 + (f y).2 : W) : V)
            = (((f x).1 : V) + ((f y).1 : V)) + (((f x).2 : V) + ((f y).2 : V)) := by simp
          _ = (((f x).1 : V) + ((f x).2 : V)) + (((f y).1 : V) + ((f y).2 : V)) := by abel
          _ = x + y := by rw [hx, hy]
      have heq := hf2 (x + y) ((f x).1 + (f y).1, (f x).2 + (f y).2) hsum
      exact congrArg Prod.fst heq.symm
    map_smul' := fun c x => by
      have hsm : ((c • (f x).1 : U) : V) + ((c • (f x).2 : W) : V) = c • x := by
        simp only [SetLike.val_smul, ← smul_add, hf1 x]
      have heq := hf2 (c • x) (c • (f x).1, c • (f x).2) hsm
      exact congrArg Prod.fst heq.symm
  }, fun u => by
    have h0 : ((u : U) : V) + ((0 : W) : V) = u.1 := by simp
    exact congrArg Prod.fst (hf2 u.1 (u, 0) h0).symm⟩

lemma dualMap_surjective {n : ℕ} (U : Submodule F (Fin n → F)) :
    Function.Surjective (dualMap U) := by
  intro φ
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  obtain ⟨π, hπ⟩ := proj_of_isCompl U W hUW
  let ψ : (Fin n → F) →ₗ[F] F := φ.comp π
  refine ⟨fun j => ψ (Pi.single j 1), ?_⟩
  ext u
  simp only [dualMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    Submodule.coe_subtype, dotLin]
  have hrep : u.1 = ∑ j : Fin n, u.1 j • Pi.single j (1 : F) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hdot : dotProduct (fun j => ψ (Pi.single j 1)) u.1 = ψ u.1 := by
    conv_rhs => rw [hrep, map_sum]
    simp only [dotProduct, map_smul, smul_eq_mul, mul_comm]
  rw [hdot]
  show φ (π u.1) = φ u
  rw [hπ u]

lemma finrank_perp {n : ℕ} (U : Submodule F (Fin n → F)) :
    Module.finrank F (perp U) + Module.finrank F U = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (dualMap U)
  have hr : LinearMap.range (dualMap U) = ⊤ :=
    LinearMap.range_eq_top.mpr (dualMap_surjective U)
  rw [hr, finrank_top, Subspace.dual_finrank_eq, Module.finrank_fin_fun] at h1
  change Module.finrank F U + Module.finrank F (perp U) = n at h1
  omega

lemma perp_perp {n : ℕ} (U : Submodule F (Fin n → F)) : perp (perp U) = U := by
  have hle : U ≤ perp (perp U) := by
    intro u hu
    rw [mem_perp]
    intro v hv
    rw [dotProduct_comm]
    exact (mem_perp U v).mp hv u hu
  have hfr : Module.finrank F U = Module.finrank F (perp (perp U)) := by
    have h1 := finrank_perp U
    have h2 := finrank_perp (perp U)
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfr).symm

lemma exists_left_inv {s k : ℕ} (B : (Fin s → F) →ₗ[F] (Fin k → F))
    (hB : Function.Injective B) :
    ∃ P : (Fin k → F) →ₗ[F] (Fin s → F), ∀ t, P (B t) = t := by
  obtain ⟨W, hBW⟩ := Submodule.exists_isCompl (LinearMap.range B)
  obtain ⟨π, hπ⟩ := proj_of_isCompl (LinearMap.range B) W hBW
  let e : (Fin s → F) ≃ₗ[F] LinearMap.range B := LinearEquiv.ofInjective B hB
  refine ⟨e.symm.toLinearMap.comp π, fun t => ?_⟩
  have hmem : B t ∈ LinearMap.range B := ⟨t, rfl⟩
  change e.symm (π (⟨B t, hmem⟩ : LinearMap.range B).1) = t
  rw [hπ ⟨B t, hmem⟩]
  exact e.symm_apply_apply t

lemma sum_chi_dot_subspace {n : ℕ} (U : Submodule F (Fin n → F)) [Fintype U] (v : Fin n → F)
    [Decidable (v ∈ perp U)] :
    (∑ u : U, chi (dotProduct v u.1)) = if v ∈ perp U then (Fintype.card U : ℤ) else 0 := by
  by_cases hv : v ∈ perp U
  · rw [if_pos hv]
    have h1 : ∀ u : U, chi (dotProduct v u.1) = 1 := fun u => by
      rw [(mem_perp U v).mp hv u.1 u.2, chi_zero]
    simp [h1]
  · rw [if_neg hv]
    rw [mem_perp] at hv
    push Not at hv
    obtain ⟨u0, hu0, hne⟩ := hv
    have h1 : dotProduct v u0 = 1 := zmod2_eq_one_of_ne_zero _ hne
    let S : ℤ := ∑ u : U, chi (dotProduct v u.1)
    have hshift : S = -S := by
      change (∑ u : U, chi (dotProduct v u.1)) = -(∑ u : U, chi (dotProduct v u.1))
      rw [← Finset.sum_neg_distrib]
      refine Fintype.sum_equiv (Equiv.addRight (⟨u0, hu0⟩ : U)) _ _ (fun u => ?_)
      change chi (dotProduct v u.1) = -chi (dotProduct v (u.1 + u0))
      rw [dotProduct_add, h1, chi_add, chi_one]
      ring
    omega

lemma sum_chi_dot_univ {n : ℕ} (v : Fin n → F) :
    (∑ x : Fin n → F, chi (dotProduct x v)) = if v = 0 then (2 ^ n : ℤ) else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [chi_zero, card_fin_fun]
  · rw [if_neg hv]
    have hex : ∃ j : Fin n, v j = 1 := by
      by_contra h
      push Not at h
      apply hv
      funext j
      rcases zmod2_eq_zero_or_one (v j) with hj | hj
      · exact hj
      · exact absurd hj (h j)
    obtain ⟨j, hj⟩ := hex
    let S : ℤ := ∑ x : Fin n → F, chi (dotProduct x v)
    have hshift : S = -S := by
      change (∑ x : Fin n → F, chi (dotProduct x v)) = -(∑ x : Fin n → F, chi (dotProduct x v))
      rw [← Finset.sum_neg_distrib]
      let σ : (Fin n → F) ≃ (Fin n → F) :=
        { toFun := fun x => x + Pi.single j (1 : F)
          invFun := fun x => x + Pi.single j (1 : F)
          left_inv := fun x => by dsimp only; rw [add_assoc, vec_add_self, add_zero]
          right_inv := fun x => by dsimp only; rw [add_assoc, vec_add_self, add_zero] }
      refine Fintype.sum_equiv σ
        (fun x => chi (dotProduct x v)) (fun x => -chi (dotProduct x v)) (fun x => ?_)
      dsimp only [σ, Equiv.coe_fn_mk]
      rw [add_dotProduct, single_dotProduct, one_mul, hj, chi_add, chi_one]
      ring
    omega

lemma perp_basis_three {s : ℕ} (W : Submodule F (Fin s → F))
    (hW : Module.finrank F W + 3 = s) :
    ∃ a b c : Fin s → F, ∀ u : Fin s → F,
      u ∈ W ↔ dotProduct a u = 0 ∧ dotProduct b u = 0 ∧ dotProduct c u = 0 := by
  have hfr : Module.finrank F (perp W) = 3 := by
    have := finrank_perp W; omega
  let e : (Fin 3 → F) ≃ₗ[F] perp W :=
    LinearEquiv.ofFinrankEq (R := F) (M := Fin 3 → F) (M' := perp W)
      (by rw [Module.finrank_fin_fun, hfr])
  let a : Fin s → F := (e (Pi.single 0 1)).1
  let b : Fin s → F := (e (Pi.single 1 1)).1
  let c : Fin s → F := (e (Pi.single 2 1)).1
  refine ⟨a, b, c, fun u => ?_⟩
  constructor
  · intro hu
    exact ⟨(mem_perp W a).mp (e (Pi.single 0 1)).2 u hu,
      (mem_perp W b).mp (e (Pi.single 1 1)).2 u hu,
      (mem_perp W c).mp (e (Pi.single 2 1)).2 u hu⟩
  · rintro ⟨ha, hb, hc⟩
    rw [← perp_perp W, mem_perp]
    intro v hv
    let lam : Fin 3 → F := e.symm ⟨v, hv⟩
    have hv_eq : v = lam 0 • a + lam 1 • b + lam 2 • c := by
      have hlam : lam = lam 0 • Pi.single 0 1 + lam 1 • Pi.single 1 1 + lam 2 • Pi.single 2 1 := by
        funext i; fin_cases i <;> simp [Pi.single_apply]
      have he : (e lam).1 = v := congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
      conv_lhs => rw [← he, hlam, map_add, map_add, map_smul, map_smul, map_smul]
      simp only [Submodule.coe_add, SetLike.val_smul]
      rfl
    rw [dotProduct_comm, hv_eq, add_dotProduct, add_dotProduct, smul_dotProduct,
      smul_dotProduct, smul_dotProduct, ha, hb, hc]
    simp

def dd {n : ℕ} (f : (Fin n → F) → F) (u x : Fin n → F) : F := f (x + u) - f x

lemma dd_eq_add {n : ℕ} (f : (Fin n → F) → F) (u x : Fin n → F) :
    dd f u x = f (x + u) + f x := zmod2_sub_eq_add _ _

lemma dd_const {n : ℕ} (c : F) (u x : Fin n → F) : dd (fun _ => c) u x = 0 := by
  simp [dd]

lemma dd_add {n : ℕ} (f₁ f₂ : (Fin n → F) → F) (u x : Fin n → F) :
    dd (fun t => f₁ t + f₂ t) u x = dd f₁ u x + dd f₂ u x := by
  simp only [dd_eq_add]; ring

lemma dd_smul {n : ℕ} (c : F) (f : (Fin n → F) → F) (u x : Fin n → F) :
    dd (fun t => c * f t) u x = c * dd f u x := by
  simp only [dd_eq_add]; ring

lemma dd_comp_aff {s k : ℕ} (g : (Fin k → F) → F) (B : (Fin s → F) →ₗ[F] (Fin k → F))
    (a : Fin k → F) (u x : Fin s → F) :
    dd (fun t => g (a + B t)) u x = dd g (B u) (a + B x) := by
  simp only [dd, map_add]
  rw [add_assoc]

lemma dd_mul {n : ℕ} (f₁ f₂ : (Fin n → F) → F) (u x : Fin n → F) :
    dd (fun t => f₁ t * f₂ t) u x = dd f₁ u x * f₂ (x + u) + f₁ x * dd f₂ u x := by
  simp only [dd_eq_add]
  have h : ∀ a b c d : F, a * c + b * d = (a + b) * c + b * (c + d) := by decide
  exact h _ _ _ _

def HasDeg {n : ℕ} : ℕ → ((Fin n → F) → F) → Prop
  | 0, f => ∀ u x, dd f u x = 0
  | d + 1, f => ∀ u, HasDeg d (dd f u)

lemma hasDeg_zero_iff {n : ℕ} (f : (Fin n → F) → F) :
    HasDeg 0 f ↔ ∀ x y, f x = f y := by
  constructor
  · intro h x y
    have h1 := h (y - x) x
    simp only [dd, add_sub_cancel] at h1
    exact (sub_eq_zero.mp h1).symm
  · intro h u x
    simp only [dd, h (x + u) x, sub_self]

lemma hasDeg_const {n : ℕ} (d : ℕ) (c : F) : HasDeg d (fun _ : Fin n → F => c) := by
  induction d generalizing c with
  | zero => intro u x; exact dd_const c u x
  | succ d ih =>
    intro u
    have : dd (fun _ : Fin n → F => c) u = fun _ => 0 := by funext x; exact dd_const c u x
    rw [this]
    exact ih 0

lemma hasDeg_zero_fn {n : ℕ} (d : ℕ) : HasDeg d (fun _ : Fin n → F => (0 : F)) :=
  hasDeg_const d 0

lemma hasDeg_mono {n d : ℕ} {f : (Fin n → F) → F} (h : HasDeg d f) : HasDeg (d + 1) f := by
  induction d generalizing f with
  | zero =>
    intro u v x
    have h0 : dd f u = fun _ => 0 := by funext t; exact h u t
    rw [h0]
    exact dd_const 0 v x
  | succ d ih =>
    intro u
    exact ih (h u)

lemma hasDeg_add {n d : ℕ} {f₁ f₂ : (Fin n → F) → F}
    (h1 : HasDeg d f₁) (h2 : HasDeg d f₂) : HasDeg d (fun t => f₁ t + f₂ t) := by
  induction d generalizing f₁ f₂ with
  | zero =>
    intro u x
    rw [dd_add, h1 u x, h2 u x, zero_add]
  | succ d ih =>
    intro u
    have heq : dd (fun t => f₁ t + f₂ t) u = fun t => dd f₁ u t + dd f₂ u t := by
      funext t; exact dd_add f₁ f₂ u t
    rw [heq]
    exact ih (h1 u) (h2 u)

lemma hasDeg_smul {n d : ℕ} (c : F) {f : (Fin n → F) → F} (h : HasDeg d f) :
    HasDeg d (fun t => c * f t) := by
  induction d generalizing f with
  | zero =>
    intro u x
    rw [dd_smul, h u x, mul_zero]
  | succ d ih =>
    intro u
    have heq : dd (fun t => c * f t) u = fun t => c * dd f u t := by
      funext t; exact dd_smul c f u t
    rw [heq]
    exact ih (h u)

lemma hasDeg_sum {n d : ℕ} {ι : Type*} (S : Finset ι) (f : ι → (Fin n → F) → F)
    (hf : ∀ i ∈ S, HasDeg d (f i)) :
    HasDeg d (fun t => ∑ i ∈ S, f i t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using hasDeg_zero_fn (n := n) d
  | insert a S ha ih =>
    have heq : (fun t => ∑ i ∈ insert a S, f i t) = fun t => f a t + ∑ i ∈ S, f i t := by
      funext t; exact Finset.sum_insert ha
    rw [heq]
    exact hasDeg_add (hf a (Finset.mem_insert_self a S))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma hasDeg_translate {n d : ℕ} (a : Fin n → F) {f : (Fin n → F) → F} (h : HasDeg d f) :
    HasDeg d (fun t => f (a + t)) := by
  induction d generalizing f with
  | zero =>
    intro u x
    have : dd (fun t => f (a + t)) u x = dd f u (a + x) := by
      simp only [dd, add_assoc]
    rw [this, h u (a + x)]
  | succ d ih =>
    intro u
    have : dd (fun t => f (a + t)) u = fun t => dd f u (a + t) := by
      funext t; simp only [dd, add_assoc]
    rw [this]
    exact ih (h u)

lemma hasDeg_comp_aff {s k d : ℕ} (B : (Fin s → F) →ₗ[F] (Fin k → F)) (a : Fin k → F)
    {g : (Fin k → F) → F} (hg : HasDeg d g) :
    HasDeg d (fun t => g (a + B t)) := by
  induction d generalizing g with
  | zero =>
    intro u x
    rw [dd_comp_aff, hg (B u) (a + B x)]
  | succ d ih =>
    intro u
    have : dd (fun t => g (a + B t)) u = fun t => dd g (B u) (a + B t) := by
      funext t; exact dd_comp_aff g B a u t
    rw [this]
    exact ih (hg (B u))

lemma hasDeg_dot {n : ℕ} (v : Fin n → F) (c : F) :
    HasDeg 1 (fun t : Fin n → F => dotProduct v t + c) := by
  intro u w x
  have h1 : dd (fun t => dotProduct v t + c) u = fun _ => dotProduct v u := by
    funext t
    simp only [dd_eq_add, dotProduct_add]
    have h2 : dotProduct v t + dotProduct v t = 0 := zmod2_add_self _
    have h3 : c + c = 0 := zmod2_add_self _
    calc dotProduct v t + dotProduct v u + c + (dotProduct v t + c)
        = (dotProduct v t + dotProduct v t) + (c + c) + dotProduct v u := by ring
      _ = dotProduct v u := by rw [h2, h3]; ring
  rw [h1]
  exact dd_const _ w x

lemma hasDeg_mul_aff {n d : ℕ} {f₁ f₂ : (Fin n → F) → F}
    (h1 : HasDeg 1 f₁) (h2 : HasDeg d f₂) :
    HasDeg (d + 1) (fun t => f₁ t * f₂ t) := by
  induction d generalizing f₂ with
  | zero =>
    have hc : ∀ x, f₂ x = f₂ 0 := fun x => (hasDeg_zero_iff f₂).mp h2 x 0
    have heq : (fun t => f₁ t * f₂ t) = fun t => f₂ 0 * f₁ t := by
      funext t; rw [hc t, mul_comm]
    rw [heq]
    exact hasDeg_smul (f₂ 0) h1
  | succ d ih =>
    intro u
    have hconst : ∀ x, dd f₁ u x = dd f₁ u 0 := fun x => (hasDeg_zero_iff (dd f₁ u)).mp (h1 u) x 0
    have heq : dd (fun t => f₁ t * f₂ t) u =
        fun t => dd f₁ u 0 * f₂ (u + t) + f₁ t * dd f₂ u t := by
      funext t
      rw [dd_mul, hconst t, add_comm t u]
    rw [heq]
    exact hasDeg_add (hasDeg_smul _ (hasDeg_translate u h2)) (ih (h2 u))

lemma dd3_eq_zero_of_hasDeg2 {n : ℕ} {f : (Fin n → F) → F} (h : HasDeg 2 f) (u v w x : Fin n → F) :
    dd (dd (dd f u) v) w x = 0 := h u v w x

lemma dd3_const_in_x {n : ℕ} {f : (Fin n → F) → F} (h : HasDeg 3 f) (u v w x : Fin n → F) :
    dd (dd (dd f u) v) w x = dd (dd (dd f u) v) w 0 :=
  (hasDeg_zero_iff (dd (dd (dd f u) v) w)).mp (h u v w) x 0

lemma dd3_add {n : ℕ} (f₁ f₂ : (Fin n → F) → F) (u v w x : Fin n → F) :
    dd (dd (dd (fun t => f₁ t + f₂ t) u) v) w x =
      dd (dd (dd f₁ u) v) w x + dd (dd (dd f₂ u) v) w x := by
  have h1 : dd (fun t => f₁ t + f₂ t) u = fun t => dd f₁ u t + dd f₂ u t := by
    funext t; exact dd_add f₁ f₂ u t
  have h2 : dd (fun t => dd f₁ u t + dd f₂ u t) v = fun t => dd (dd f₁ u) v t + dd (dd f₂ u) v t := by
    funext t; exact dd_add _ _ v t
  rw [h1, h2, dd_add]

lemma dd3_comp_aff {s k : ℕ} {g : (Fin k → F) → F} (hg : HasDeg 3 g)
    (B : (Fin s → F) →ₗ[F] (Fin k → F)) (a : Fin k → F) (u v w x : Fin s → F) :
    dd (dd (dd (fun t => g (a + B t)) u) v) w x = dd (dd (dd g (B u)) (B v)) (B w) 0 := by
  have h1 : dd (fun t => g (a + B t)) u = fun t => dd g (B u) (a + B t) := by
    funext t; exact dd_comp_aff g B a u t
  have h2 : dd (fun t => dd g (B u) (a + B t)) v = fun t => dd (dd g (B u)) (B v) (a + B t) := by
    funext t; exact dd_comp_aff (dd g (B u)) B a v t
  rw [h1, h2, dd_comp_aff]
  exact dd3_const_in_x hg (B u) (B v) (B w) (a + B x)

def wt {n : ℕ} (f : (Fin n → F) → F) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → F => f x = 1)).card

lemma wt_add_one {n : ℕ} (f : (Fin n → F) → F) :
    wt f + wt (fun x => f x + 1) = 2 ^ n := by
  have hunion : Finset.univ.filter (fun x : Fin n → F => f x = 1) ∪
      Finset.univ.filter (fun x : Fin n → F => f x + 1 = 1) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have h : ∀ a : F, a = 1 ∨ a + 1 = 1 := by decide
    exact h (f x)
  have hdisj : Disjoint (Finset.univ.filter (fun x : Fin n → F => f x = 1))
      (Finset.univ.filter (fun x : Fin n → F => f x + 1 = 1)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  unfold wt
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, card_fin_fun]

lemma sum_chi_eq_wt {n : ℕ} (f : (Fin n → F) → F) :
    (∑ x : Fin n → F, chi (f x)) = (2 ^ n : ℤ) - 2 * (wt f : ℤ) := by
  classical
  have h1 : ∀ x : Fin n → F, chi (f x) = (1 : ℤ) - if f x = 1 then 2 else 0 := by
    intro x
    have h : ∀ a : F, chi a = (1 : ℤ) - if a = 1 then 2 else 0 := by decide
    exact h (f x)
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_fin_fun]
  simp only [nsmul_eq_mul, mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  unfold wt
  push_cast
  ring

lemma exists_low_wt_shift {n : ℕ} (f : (Fin n → F) → F) :
    ∃ f₀ : (Fin n → F) → F, (f₀ = f ∨ f₀ = fun x => f x + 1) ∧
      2 * wt f₀ ≤ 2 ^ n ∧
      (∑ x : Fin n → F, chi (f x)).natAbs + 2 * wt f₀ = 2 ^ n := by
  have hsum := sum_chi_eq_wt f
  by_cases hle : 2 * wt f ≤ 2 ^ n
  · refine ⟨f, Or.inl rfl, hle, ?_⟩
    have hleZ : 2 * (wt f : ℤ) ≤ (2 ^ n : ℤ) := by exact_mod_cast hle
    have hnn : (0 : ℤ) ≤ (2 ^ n : ℤ) - 2 * (wt f : ℤ) := by linarith
    zify
    rw [hsum, abs_of_nonneg hnn]
    ring
  · refine ⟨fun x => f x + 1, Or.inr rfl, ?_, ?_⟩
    · have hcomp := wt_add_one f; omega
    · have hcomp := wt_add_one f
      have hgtZ : (2 ^ n : ℤ) < 2 * (wt f : ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hle)
      have hneg : (2 ^ n : ℤ) - 2 * (wt f : ℤ) ≤ 0 := by linarith
      have h2 : (wt f : ℤ) + (wt (fun x => f x + 1) : ℤ) = (2 ^ n : ℤ) := by exact_mod_cast hcomp
      zify
      rw [hsum, abs_of_nonpos hneg]
      linarith

lemma wt_dd_add_inter {n : ℕ} (f : (Fin n → F) → F) (u : Fin n → F) :
    wt (dd f u) + 2 * (Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1)).card =
      2 * wt f := by
  classical
  let A := Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 0)
  let B := Finset.univ.filter (fun x : Fin n → F => f x = 0 ∧ f (x + u) = 1)
  let C := Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1)
  have hdd : Finset.univ.filter (fun x : Fin n → F => dd f u x = 1) = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, dd_eq_add]
    rcases zmod2_eq_zero_or_one (f x) with h1 | h1 <;>
      rcases zmod2_eq_zero_or_one (f (x + u)) with h2 | h2 <;> simp [h1, h2]
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1.1] at h2; exact absurd h2.1 (by decide)
  have hAC : Finset.univ.filter (fun x : Fin n → F => f x = 1) = A ∪ C := by
    ext x
    simp only [A, C, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rcases zmod2_eq_zero_or_one (f (x + u)) with h2 | h2 <;> simp [h2]
  have hdisjAC : Disjoint A C := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)
  have hBC : Finset.univ.filter (fun x : Fin n → F => f (x + u) = 1) = B ∪ C := by
    ext x
    simp only [B, C, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rcases zmod2_eq_zero_or_one (f x) with h1 | h1 <;> simp [h1]
  have hdisjBC : Disjoint B C := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1.1] at h2; exact absurd h2.1 (by decide)
  have hshift : (Finset.univ.filter (fun x : Fin n → F => f (x + u) = 1)).card = wt f := by
    unfold wt
    refine Finset.card_nbij (fun x => x + u) ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro x _ y _ hxy; exact add_right_cancel hxy
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact ⟨y - u, by simp [hy], sub_add_cancel y u⟩
  have c1 : wt (dd f u) = A.card + B.card := by
    unfold wt; rw [hdd, Finset.card_union_of_disjoint hdisjAB]
  have c2 : wt f = A.card + C.card := by
    unfold wt; rw [hAC, Finset.card_union_of_disjoint hdisjAC]
  have c3 : wt f = B.card + C.card := by
    rw [← hshift, hBC, Finset.card_union_of_disjoint hdisjBC]
  change wt (dd f u) + 2 * C.card = 2 * wt f
  omega

lemma rm_min_wt {n d : ℕ} (f : (Fin n → F) → F) (hd : HasDeg d f) (hne : ∃ x, f x = 1) :
    2 ^ n ≤ 2 ^ d * wt f := by
  induction d generalizing f with
  | zero =>
    obtain ⟨x0, hx0⟩ := hne
    have hall : ∀ x, f x = 1 := fun x => ((hasDeg_zero_iff f).mp hd x x0).trans hx0
    have hwt : wt f = 2 ^ n := by
      unfold wt
      simp [hall, card_fin_fun]
    rw [hwt]; simp
  | succ d ih =>
    obtain ⟨x0, hx0⟩ := hne
    by_cases hall : ∀ x, f x = 1
    · have hwt : wt f = 2 ^ n := by
        unfold wt; simp [hall, card_fin_fun]
      rw [hwt]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    · push Not at hall
      obtain ⟨x1, hx1⟩ := hall
      have hx10 : f x1 = 0 := by
        rcases zmod2_eq_zero_or_one (f x1) with h | h
        · exact h
        · exact absurd h hx1
      let u := x1 - x0
      have hdd1 : dd f u x0 = 1 := by
        simp only [dd, u, add_sub_cancel, hx10, hx0]; decide
      have hih := ih (dd f u) (hd u) ⟨x0, hdd1⟩
      have hle : wt (dd f u) ≤ 2 * wt f := by
        have := wt_dd_add_inter f u; omega
      calc 2 ^ n ≤ 2 ^ d * wt (dd f u) := hih
        _ ≤ 2 ^ d * (2 * wt f) := Nat.mul_le_mul_left _ hle
        _ = 2 ^ (d + 1) * wt f := by ring

lemma rm_min_wt_coset {n d : ℕ} (hd1 : 1 ≤ d) (f : (Fin n → F) → F)
    (hd : HasDeg d f) (hne : ∃ x, f x = 1) (heq : 2 ^ d * wt f = 2 ^ n) :
    ∃ (x₀ : Fin n → F) (W : Submodule F (Fin n → F)),
      Module.finrank F W + d = n ∧ ∀ x, f x = 1 ↔ x - x₀ ∈ W := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hdich : ∀ u : Fin n → F,
      (∀ x, f (x + u) = f x) ∨ (∀ x, ¬ (f x = 1 ∧ f (x + u) = 1)) := by
    intro u
    by_cases h0 : ∃ x, dd f u x = 1
    · right
      have hd_prev : HasDeg (d - 1) (dd f u) := by
        rcases d with _ | d'
        · omega
        · exact hd u
      have hmin := rm_min_wt (dd f u) hd_prev h0
      have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
        rcases d with _ | d'
        · omega
        · simp [pow_succ]
      have hwt_ge : 2 * wt f ≤ wt (dd f u) := by
        have hmul : 2 ^ (d - 1) * (2 * wt f) ≤ 2 ^ (d - 1) * wt (dd f u) := by
          calc 2 ^ (d - 1) * (2 * wt f) = 2 ^ d * wt f := by rw [hpow]; ring
            _ = 2 ^ n := heq
            _ ≤ 2 ^ (d - 1) * wt (dd f u) := hmin
        exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos _)
      have hint0 : (Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1)).card = 0 := by
        have := wt_dd_add_inter f u; omega
      intro x hx
      have hmem : x ∈ Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      rw [Finset.card_eq_zero] at hint0
      rw [hint0] at hmem
      exact Finset.notMem_empty x hmem
    · left
      push Not at h0
      intro x
      have hzx : dd f u x = 0 := by
        rcases zmod2_eq_zero_or_one (dd f u x) with h | h
        · exact h
        · exact absurd h (h0 x)
      exact sub_eq_zero.mp hzx
  let W : Submodule F (Fin n → F) :=
    { carrier := { u : Fin n → F | f (x₀ + u) = 1 }
      zero_mem' := by simp [hx₀], add_mem' := by
        intro u v hu hv
        change f (x₀ + u) = 1 at hu
        change f (x₀ + v) = 1 at hv
        change f (x₀ + (u + v)) = 1
        rcases hdich u with hco | hdisj
        · rw [add_comm u v, ← add_assoc, hco (x₀ + v), hv]
        · exact absurd ⟨hx₀, hu⟩ (hdisj x₀)
      smul_mem' := by
        intro c u hu
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp [hx₀]
        · simpa using hu }
  have hmemW : ∀ x, f x = 1 ↔ x - x₀ ∈ W := by
    intro x
    show f x = 1 ↔ f (x₀ + (x - x₀)) = 1
    rw [add_sub_cancel]
  have hcardW : wt f = Fintype.card W := by
    unfold wt
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x hx => (⟨x - x₀, (hmemW x).mp (Finset.mem_filter.mp hx).2⟩ : W)) ?_ ?_ ?_
    · intro x _; exact Finset.mem_univ _
    · intro x _ y _ hxy
      have h1 : x - x₀ = y - x₀ := congrArg Subtype.val hxy
      exact sub_left_inj.mp h1
    · intro w _
      refine ⟨x₀ + w.1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact w.2
      · ext j; simp
  rw [hcardW, card_submodule, ← pow_add] at heq
  have hdim : d + Module.finrank F W = n := Nat.pow_right_injective (by norm_num) heq
  exact ⟨x₀, W, by omega, hmemW⟩

lemma rm3_coset_wedge {s : ℕ} (f : (Fin s → F) → F) (hd : HasDeg 3 f)
    (hne : ∃ x, f x = 1) (heq : 8 * wt f = 2 ^ s) :
    ∃ a b c : Fin s → F, ∀ u v w,
      dd (dd (dd f u) v) w 0 =
        dd (dd (dd (fun t => dotProduct a t * dotProduct b t * dotProduct c t) u) v) w 0 := by
  have heq' : 2 ^ 3 * wt f = 2 ^ s := by simpa using heq
  obtain ⟨x₀, W, hWdim, hWmem⟩ := rm_min_wt_coset (by omega) f hd hne heq'
  obtain ⟨a, b, c, habc⟩ := perp_basis_three W hWdim
  let α : F := dotProduct a x₀ + 1
  let β : F := dotProduct b x₀ + 1
  let γ : F := dotProduct c x₀ + 1
  have hf_eq : ∀ t : Fin s → F,
      f t = (dotProduct a t + α) * (dotProduct b t + β) * (dotProduct c t + γ) := by
    intro t
    have hiff : f t = 1 ↔
        dotProduct a t + α = 1 ∧ dotProduct b t + β = 1 ∧ dotProduct c t + γ = 1 := by
      rw [hWmem t, habc (t - x₀)]
      simp only [dotProduct_sub, α, β, γ]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have e1 : dotProduct a t = dotProduct a x₀ := sub_eq_zero.mp h1
        have e2 : dotProduct b t = dotProduct b x₀ := sub_eq_zero.mp h2
        have e3 : dotProduct c t = dotProduct c x₀ := sub_eq_zero.mp h3
        rw [e1, e2, e3, ← add_assoc, zmod2_add_self, zero_add,
          ← add_assoc, zmod2_add_self, zero_add, ← add_assoc, zmod2_add_self, zero_add]
        exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨h1, h2, h3⟩
        have k : ∀ p q : F, p + (q + 1) = 1 → p - q = 0 := by
          intro p q; fin_cases p <;> fin_cases q <;> decide
        exact ⟨k _ _ h1, k _ _ h2, k _ _ h3⟩
    have hprod : (dotProduct a t + α) * (dotProduct b t + β) * (dotProduct c t + γ) = 1 ↔
        dotProduct a t + α = 1 ∧ dotProduct b t + β = 1 ∧ dotProduct c t + γ = 1 := by
      rcases zmod2_eq_zero_or_one (dotProduct a t + α) with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (dotProduct b t + β) with h2 | h2 <;>
        rcases zmod2_eq_zero_or_one (dotProduct c t + γ) with h3 | h3 <;> simp [h1, h2, h3]
    rcases zmod2_eq_zero_or_one (f t) with hft | hft <;>
      rcases zmod2_eq_zero_or_one ((dotProduct a t + α) * (dotProduct b t + β) * (dotProduct c t + γ)) with hp | hp
    · rw [hft, hp]
    · exfalso; have := hiff.mpr (hprod.mp hp); rw [hft] at this; exact absurd this (by decide)
    · exfalso; have := hprod.mpr (hiff.mp hft); rw [hp] at this; exact absurd this (by decide)
    · rw [hft, hp]
  let h : (Fin s → F) → F := fun t => dotProduct a t * dotProduct b t * dotProduct c t
  let q : (Fin s → F) → F := fun t =>
    γ * (dotProduct a t * dotProduct b t) +
    β * (dotProduct a t * dotProduct c t) +
    α * (dotProduct b t * dotProduct c t) +
    (β * γ) * dotProduct a t +
    (α * γ) * dotProduct b t +
    (α * β) * dotProduct c t +
    α * β * γ
  have hfq : f = fun t => h t + q t := by
    funext t
    rw [hf_eq t]
    simp only [h, q]
    ring
  have hq2 : HasDeg 2 q := by
    have hL : ∀ v : Fin s → F, HasDeg 1 (fun t => dotProduct v t) := fun v => by
      simpa using hasDeg_dot v 0
    have hQ : ∀ v w : Fin s → F, HasDeg 2 (fun t => dotProduct v t * dotProduct w t) := fun v w =>
      hasDeg_mul_aff (hL v) (hL w)
    exact hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add
      (hasDeg_smul γ (hQ a b))
      (hasDeg_smul β (hQ a c)))
      (hasDeg_smul α (hQ b c)))
      (hasDeg_smul (β * γ) (hasDeg_mono (hL a))))
      (hasDeg_smul (α * γ) (hasDeg_mono (hL b))))
      (hasDeg_smul (α * β) (hasDeg_mono (hL c))))
      (hasDeg_const 2 (α * β * γ))
  refine ⟨a, b, c, fun u v w => ?_⟩
  rw [hfq, dd3_add, dd3_eq_zero_of_hasDeg2 hq2 u v w 0, add_zero]

lemma triple_hasDeg3 {s : ℕ} (a b c : Fin s → F) :
    HasDeg 3 (fun t : Fin s → F => dotProduct a t * dotProduct b t * dotProduct c t) := by
  have hL : ∀ v : Fin s → F, HasDeg 1 (fun t => dotProduct v t) := fun v => by
    simpa using hasDeg_dot v 0
  have h2 : HasDeg 2 (fun t => dotProduct a t * dotProduct b t) := hasDeg_mul_aff (hL a) (hL b)
  have heq : (fun t => dotProduct a t * dotProduct b t * dotProduct c t) =
      fun t => dotProduct c t * (dotProduct a t * dotProduct b t) := by
    funext t; ring
  rw [heq]
  exact hasDeg_mul_aff (hL c) h2

lemma triple_wt_or_zero {s : ℕ} (a b c : Fin s → F) :
    (∀ u v w, dd (dd (dd (fun t => dotProduct a t * dotProduct b t * dotProduct c t) u) v) w 0 = 0) ∨
    8 * wt (fun t => dotProduct a t * dotProduct b t * dotProduct c t) = 2 ^ s := by
  classical
  let h : (Fin s → F) → F := fun t => dotProduct a t * dotProduct b t * dotProduct c t
  let Φ : (Fin s → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fun t => ![dotProduct a t, dotProduct b t, dotProduct c t]
      map_add' := fun x y => by
        funext i; fin_cases i <;> simp [dotProduct_add]
      map_smul' := fun r x => by
        funext i; fin_cases i <;> simp [dotProduct_smul] }
  by_cases hsurj : LinearMap.range Φ = ⊤
  · right
    have hfr := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hfr
    have hex : ∃ t1 : Fin s → F, Φ t1 = ![1, 1, 1] := by
      have : (![1, 1, 1] : Fin 3 → F) ∈ LinearMap.range Φ := by rw [hsurj]; trivial
      exact this
    obtain ⟨t1, ht1⟩ := hex
    have hiff : ∀ t : Fin s → F, h t = 1 ↔ t - t1 ∈ LinearMap.ker Φ := by
      intro t
      have h1 : h t = 1 ↔ Φ t = ![1, 1, 1] := by
        simp only [h, Φ, LinearMap.coe_mk, AddHom.coe_mk]
        constructor
        · intro ht
          have ha : dotProduct a t = 1 := by
            rcases zmod2_eq_zero_or_one (dotProduct a t) with h0 | h0
            · rw [h0] at ht; simp at ht
            · exact h0
          have hb : dotProduct b t = 1 := by
            rcases zmod2_eq_zero_or_one (dotProduct b t) with h0 | h0
            · rw [h0] at ht; simp at ht
            · exact h0
          have hc : dotProduct c t = 1 := by
            rcases zmod2_eq_zero_or_one (dotProduct c t) with h0 | h0
            · rw [h0] at ht; simp at ht
            · exact h0
          funext i; fin_cases i <;> simp [ha, hb, hc]
        · intro hφ
          have ha : dotProduct a t = 1 := by simpa using congrFun hφ 0
          have hb : dotProduct b t = 1 := by simpa using congrFun hφ 1
          have hc : dotProduct c t = 1 := by simpa using congrFun hφ 2
          rw [ha, hb, hc]; decide
      rw [h1, LinearMap.mem_ker, map_sub, ht1, sub_eq_zero]
    have hcard : wt h = Fintype.card (LinearMap.ker Φ) := by
      unfold wt
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun t ht => (⟨t - t1, (hiff t).mp (Finset.mem_filter.mp ht).2⟩ : LinearMap.ker Φ)) ?_ ?_ ?_
      · intro t _; exact Finset.mem_univ _
      · intro t _ t' _ htt'
        exact sub_left_inj.mp (congrArg Subtype.val htt')
      · intro w _
        refine ⟨t1 + w.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hiff]; simpa using w.2
        · ext j; simp
    rw [hcard, card_submodule]
    calc 8 * 2 ^ Module.finrank F (LinearMap.ker Φ)
        = 2 ^ (3 + Module.finrank F (LinearMap.ker Φ)) := by rw [pow_add]; norm_num
      _ = 2 ^ s := by rw [hfr]
  · left
    have hlt : Module.finrank F (LinearMap.range Φ) < 3 := by
      have hle : Module.finrank F (LinearMap.range Φ) ≤ 3 := by
        have := Submodule.finrank_le (LinearMap.range Φ)
        rw [Module.finrank_fin_fun] at this
        exact this
      by_contra hge
      have heq : Module.finrank F (LinearMap.range Φ) = 3 := by omega
      apply hsurj
      exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact heq)
    have hppos : 0 < Module.finrank F (perp (LinearMap.range Φ)) := by
      have := finrank_perp (LinearMap.range Φ); omega
    have : Nontrivial (perp (LinearMap.range Φ)) := Module.finrank_pos_iff.mp hppos
    obtain ⟨⟨lam, hlam_mem⟩, hlam_ne⟩ := exists_ne (0 : perp (LinearMap.range Φ))
    have hlam0 : lam ≠ 0 := fun h => hlam_ne (Subtype.ext h)
    have hcomb : lam 0 • a + lam 1 • b + lam 2 • c = 0 := by
      funext j
      have h0 := (mem_perp (LinearMap.range Φ) lam).mp hlam_mem (Φ (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
      rw [dotProduct, Fin.sum_univ_three] at h0
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, dotProduct_single, mul_one] at h0
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h0
    have hdeg2 : HasDeg 2 h := by
      have hL : ∀ v : Fin s → F, HasDeg 1 (fun t => dotProduct v t) := fun v => by
        simpa using hasDeg_dot v 0
      have hQ : ∀ v w : Fin s → F, HasDeg 2 (fun t => dotProduct v t * dotProduct w t) := fun v w =>
        hasDeg_mul_aff (hL v) (hL w)
      rcases zmod2_eq_zero_or_one (lam 0) with l0 | l0 <;>
        rcases zmod2_eq_zero_or_one (lam 1) with l1 | l1 <;>
        rcases zmod2_eq_zero_or_one (lam 2) with l2 | l2
      · exfalso; apply hlam0; funext i; fin_cases i <;> assumption
      · have hc0 : c = 0 := by simpa [l0, l1, l2] using hcomb
        have : h = fun _ => 0 := by funext t; simp [h, hc0]
        rw [this]; exact hasDeg_zero_fn 2
      · have hb0 : b = 0 := by simpa [l0, l1, l2] using hcomb
        have : h = fun _ => 0 := by funext t; simp [h, hb0]
        rw [this]; exact hasDeg_zero_fn 2
      · have hbc : b = c := by
          have : b + c = 0 := by simpa [l0, l1, l2] using hcomb
          calc b = b + (b + c) := by rw [this, add_zero]
            _ = (b + b) + c := by rw [add_assoc]
            _ = c := by rw [vec_add_self, zero_add]
        have : h = fun t => dotProduct a t * dotProduct b t := by
          funext t; simp only [h, hbc, mul_assoc, zmod2_mul_self]
        rw [this]; exact hQ a b
      · have ha0 : a = 0 := by simpa [l0, l1, l2] using hcomb
        have : h = fun _ => 0 := by funext t; simp [h, ha0]
        rw [this]; exact hasDeg_zero_fn 2
      · have hac : a = c := by
          have : a + c = 0 := by simpa [l0, l1, l2] using hcomb
          calc a = a + (a + c) := by rw [this, add_zero]
            _ = (a + a) + c := by rw [add_assoc]
            _ = c := by rw [vec_add_self, zero_add]
        have : h = fun t => dotProduct a t * dotProduct b t := by
          funext t
          simp only [h, hac]
          rw [mul_comm (dotProduct c t * dotProduct b t), ← mul_assoc, zmod2_mul_self]
        rw [this]; exact hQ a b
      · have hab : a = b := by
          have : a + b = 0 := by simpa [l0, l1, l2] using hcomb
          calc a = a + (a + b) := by rw [this, add_zero]
            _ = (a + a) + b := by rw [add_assoc]
            _ = b := by rw [vec_add_self, zero_add]
        have : h = fun t => dotProduct a t * dotProduct c t := by
          funext t; simp only [h, hab, zmod2_mul_self]
        rw [this]; exact hQ a c
      · have hcab : c = a + b := by
          have : a + b + c = 0 := by simpa [l0, l1, l2] using hcomb
          calc c = c + (a + b + c) := by rw [this, add_zero]
            _ = (a + b) + (c + c) := by abel
            _ = a + b := by rw [vec_add_self, add_zero]
        have : h = fun _ => 0 := by
          funext t
          simp only [h, hcab, add_dotProduct]
          generalize dotProduct a t = A
          generalize dotProduct b t = B
          fin_cases A <;> fin_cases B <;> decide
        rw [this]; exact hasDeg_zero_fn 2
    intro u v w
    exact dd3_eq_zero_of_hasDeg2 hdeg2 u v w 0

def suppCard {s : ℕ} (t : Fin s → F) : ℕ :=
  (Finset.univ.filter (fun i : Fin s => t i = 1)).card

lemma quad_repr {s : ℕ} (f : (Fin s → F) → F) (hf : HasDeg 2 f) :
    ∃ (Q : Fin s → Fin s → F) (ℓ : Fin s → F) (c₀ : F),
      ∀ t : Fin s → F, f t = c₀ + ∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i) := by
  let c₀ : F := f 0
  let ℓ : Fin s → F := fun j => f (Pi.single j 1) + f 0
  let Q : Fin s → Fin s → F := fun i j =>
    if i < j then f (Pi.single i 1 + Pi.single j 1) + f (Pi.single i 1) + f (Pi.single j 1) + f 0
    else 0
  let q : (Fin s → F) → F := fun t =>
    c₀ + ∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i)
  have hq2 : HasDeg 2 q := by
    have hcoord : ∀ j : Fin s, HasDeg 1 (fun t : Fin s → F => t j) := fun j => by
      have : (fun t : Fin s → F => t j) = fun t => dotProduct (Pi.single j 1) t + 0 := by
        funext t; simp [single_dotProduct]
      rw [this]; exact hasDeg_dot _ 0
    refine hasDeg_add (hasDeg_const 2 c₀) (hasDeg_sum Finset.univ _ fun j _ => ?_)
    have hinner : HasDeg 1 (fun t : Fin s → F => ℓ j + ∑ i : Fin s, Q i j * t i) :=
      hasDeg_add (hasDeg_const 1 (ℓ j))
        (hasDeg_sum Finset.univ _ fun i _ => hasDeg_smul (Q i j) (hcoord i))
    exact hasDeg_mul_aff (hcoord j) hinner
  let r : (Fin s → F) → F := fun t => f t + q t
  have hr2 : HasDeg 2 r := hasDeg_add hf hq2
  have hq0 : q 0 = f 0 := by simp [q, c₀]
  have hq1 : ∀ a : Fin s, q (Pi.single a 1) = f (Pi.single a 1) := by
    intro a
    simp only [q, c₀, ℓ, Q]
    let ea : Fin s → F := Pi.single a 1
    have hs1 : (∑ j : Fin s, ea j *
        (f (Pi.single j 1) + f 0 + ∑ i : Fin s,
          (if i < j then f (Pi.single i 1 + Pi.single j 1) + f (Pi.single i 1) + f (Pi.single j 1) + f 0 else 0) *
          ea i)) = f (Pi.single a 1) + f 0 := by
      rw [Finset.sum_eq_single a]
      · simp only [ea, Pi.single_eq_same, one_mul]
        have hs2 : (∑ i : Fin s,
            (if i < a then f (Pi.single i 1 + Pi.single a 1) + f (Pi.single i 1) + f (Pi.single a 1) + f 0 else 0) *
            ((Pi.single a (1 : F) : Fin s → F) i)) = 0 := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro i _ hia; simp [Pi.single_eq_of_ne hia]
          · intro h; exact absurd (Finset.mem_univ a) h
        rw [hs2, add_zero]
      · intro j _ hja; simp [ea, Pi.single_eq_of_ne hja]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [hs1, ← add_assoc, add_comm (f 0) (f (Pi.single a 1)), add_assoc, zmod2_add_self, add_zero]
  have hq2pt : ∀ a b : Fin s, a < b → q (Pi.single a 1 + Pi.single b 1) = f (Pi.single a 1 + Pi.single b 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    have hne' : b ≠ a := ne_of_gt hab
    let t : Fin s → F := Pi.single a 1 + Pi.single b 1
    have ht_a : t a = 1 := by simp [t, Pi.single_eq_same, Pi.single_eq_of_ne hne]
    have ht_b : t b = 1 := by simp [t, Pi.single_eq_same, Pi.single_eq_of_ne hne']
    have ht_o : ∀ k, k ≠ a → k ≠ b → t k = 0 := fun k hka hkb => by
      simp [t, Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb]
    have hinner_a : (∑ i : Fin s, Q i a * t i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hia : i = a
      · subst hia; simp [Q]
      · by_cases hib : i = b
        · rw [hib]; have hnot : ¬ b < a := not_lt_of_gt hab; simp only [Q, hnot, ↓reduceIte, zero_mul]
        · rw [ht_o i hia hib, mul_zero]
    have hinner_b : (∑ i : Fin s, Q i b * t i) = Q a b := by
      rw [Finset.sum_eq_single a]
      · rw [ht_a, mul_one]
      · intro i _ hia
        by_cases hib : i = b
        · subst hib; simp [Q]
        · rw [ht_o i hia hib, mul_zero]
      · intro h; exact absurd (Finset.mem_univ a) h
    have houter : (∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i)) =
        (ℓ a + 0) + (ℓ b + Q a b) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ b⟩)]
      have hrest : (∑ j ∈ (Finset.univ.erase a).erase b, t j * (ℓ j + ∑ i : Fin s, Q i j * t i)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
        have hja : j ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        rw [ht_o j hja hjb, zero_mul]
      rw [hrest, add_zero, ht_a, ht_b, one_mul, one_mul, hinner_a, hinner_b]
    show c₀ + ∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i) = f t
    rw [houter]
    simp only [c₀, ℓ, Q, hab, if_true, t]
    have e1 := zmod2_add_self (f 0)
    have e2 := zmod2_add_self (f (Pi.single a 1))
    have e3 := zmod2_add_self (f (Pi.single b 1))
    calc f 0 + (f (Pi.single a 1) + f 0 + 0 +
          (f (Pi.single b 1) + f 0 + (f (Pi.single a 1 + Pi.single b 1) + f (Pi.single a 1) + f (Pi.single b 1) + f 0)))
        = f (Pi.single a 1 + Pi.single b 1) + (f 0 + f 0) + (f 0 + f 0) +
          (f (Pi.single a 1) + f (Pi.single a 1)) + (f (Pi.single b 1) + f (Pi.single b 1)) := by ring
      _ = f (Pi.single a 1 + Pi.single b 1) := by rw [e1, e2, e3]; ring
  have hr_zero : ∀ m : ℕ, ∀ t : Fin s → F, suppCard t = m → r t = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro t hm
      let S := Finset.univ.filter (fun i : Fin s => t i = 1)
      have hScard : S.card = m := hm
      by_cases h0 : m = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
        have ht0 : t = 0 := by
          funext i
          rcases zmod2_eq_zero_or_one (t i) with hi | hi
          · exact hi
          · exfalso
            have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
            rw [hS0] at this; exact Finset.notMem_empty i this
        subst ht0; simp only [r, hq0, zmod2_add_self]
      · by_cases h1 : m = 1
        · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
          have hta : t = Pi.single a 1 := by
            funext i
            by_cases hia : i = a
            · subst hia
              have : i ∈ S := by rw [ha]; simp
              simp only [Pi.single_eq_same]
              exact (Finset.mem_filter.mp this).2
            · simp only [Pi.single_eq_of_ne hia]
              rcases zmod2_eq_zero_or_one (t i) with hi | hi
              · exact hi
              · exfalso
                have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
                rw [ha] at this; exact hia (Finset.mem_singleton.mp this)
          subst hta; simp only [r, hq1 a, zmod2_add_self]
        · by_cases h2 : m = 2
          · obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp (show S.card = 2 by omega)
            have htab : t = Pi.single a 1 + Pi.single b 1 := by
              funext i
              by_cases hia : i = a
              · subst hia
                have : i ∈ S := by rw [hSab]; simp
                simp [Pi.single_eq_same, Pi.single_eq_of_ne hab, (Finset.mem_filter.mp this).2]
              · by_cases hib : i = b
                · subst hib
                  have : i ∈ S := by rw [hSab]; simp
                  simp [Pi.single_eq_same, Pi.single_eq_of_ne hia, (Finset.mem_filter.mp this).2]
                · simp only [Pi.add_apply, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, add_zero]
                  rcases zmod2_eq_zero_or_one (t i) with hi | hi
                  · exact hi
                  · exfalso
                    have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
                    rw [hSab] at this
                    rcases Finset.mem_insert.mp this with rfl | hmem
                    · exact hia rfl
                    · exact hib (Finset.mem_singleton.mp hmem)
            subst htab
            rcases lt_or_gt_of_ne hab with hlt | hgt
            · simp only [r, hq2pt a b hlt, zmod2_add_self]
            · rw [add_comm (Pi.single a 1) (Pi.single b 1)]
              simp only [r, hq2pt b a hgt, zmod2_add_self]
          · have hm3 : 3 ≤ m := by omega
            have hSpos1 : 0 < S.card := by omega
            obtain ⟨a, ha⟩ := Finset.card_pos.mp hSpos1
            have hSpos2 : 0 < (S.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
            obtain ⟨b, hb'⟩ := Finset.card_pos.mp hSpos2
            have hba : b ≠ a := (Finset.mem_erase.mp hb').1
            have hb : b ∈ S := (Finset.mem_erase.mp hb').2
            have hSpos3 : 0 < ((S.erase a).erase b).card := by
              rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
            obtain ⟨c, hc'⟩ := Finset.card_pos.mp hSpos3
            have hcb : c ≠ b := (Finset.mem_erase.mp hc').1
            have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc').2).1
            have hc : c ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hc').2).2
            let ea : Fin s → F := Pi.single a 1
            let eb : Fin s → F := Pi.single b 1
            let ec : Fin s → F := Pi.single c 1
            let t' : Fin s → F := t + ea + eb + ec
            have hdd0 : dd (dd (dd r ea) eb) ec t' = 0 := hr2 ea eb ec t'
            have hexp : dd (dd (dd r ea) eb) ec t' =
                r (t' + ec + eb + ea) + r (t' + ec + eb) + r (t' + ec + ea) + r (t' + ec) +
                r (t' + eb + ea) + r (t' + eb) + r (t' + ea) + r t' := by
              simp only [dd_eq_add]; ring
            have htop : t' + ec + eb + ea = t := by
              simp only [t']
              calc t + ea + eb + ec + ec + eb + ea
                  = t + (ea + ea) + (eb + eb) + (ec + ec) := by abel
                _ = t := by rw [vec_add_self, vec_add_self, vec_add_self, add_zero, add_zero, add_zero]
            have hsub : ∀ p q w : F, (p = 0 ∨ q = 0 ∨ w = 0) →
                suppCard (t' + p • ea + q • eb + w • ec) < m := by
              intro p q w h0
              let z := t' + p • ea + q • eb + w • ec
              have hta1 : t a = 1 := (Finset.mem_filter.mp ha).2
              have htb1 : t b = 1 := (Finset.mem_filter.mp hb).2
              have htc1 : t c = 1 := (Finset.mem_filter.mp hc).2
              have hss : Finset.univ.filter (fun i : Fin s => z i = 1) ⊂ S := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨?_, ?_⟩
                · intro i hi
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                  by_cases hia : i = a
                  · subst hia; exact ha
                  · by_cases hib : i = b
                    · subst hib; exact hb
                    · by_cases hic : i = c
                      · subst hic; exact hc
                      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
                        have hzi : z i = t i := by
                          simp [z, t', ea, eb, ec, Pi.single_eq_of_ne hia,
                            Pi.single_eq_of_ne hib, Pi.single_eq_of_ne hic]
                        rwa [← hzi]
                · intro heqS
                  rcases h0 with rfl | rfl | rfl
                  · have hmem : a ∈ Finset.univ.filter (fun i : Fin s => z i = 1) := heqS ▸ ha
                    have hza : z a = 0 := by
                      simp [z, t', ea, eb, ec, hta1, Pi.single_eq_same,
                        Pi.single_eq_of_ne hba.symm, Pi.single_eq_of_ne hca.symm, zmod2_add_self]
                    have := (Finset.mem_filter.mp hmem).2
                    rw [hza] at this; exact absurd this (by decide)
                  · have hmem : b ∈ Finset.univ.filter (fun i : Fin s => z i = 1) := heqS ▸ hb
                    have hzb : z b = 0 := by
                      simp [z, t', ea, eb, ec, htb1, Pi.single_eq_same,
                        Pi.single_eq_of_ne hba, Pi.single_eq_of_ne hcb.symm, zmod2_add_self]
                    have := (Finset.mem_filter.mp hmem).2
                    rw [hzb] at this; exact absurd this (by decide)
                  · have hmem : c ∈ Finset.univ.filter (fun i : Fin s => z i = 1) := heqS ▸ hc
                    have hzc : z c = 0 := by
                      simp [z, t', ea, eb, ec, htc1, Pi.single_eq_same,
                        Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb, zmod2_add_self]
                    have := (Finset.mem_filter.mp hmem).2
                    rw [hzc] at this; exact absurd this (by decide)
              exact lt_of_lt_of_eq (Finset.card_lt_card hss) hScard
            have hzero_pt : ∀ p q w : F, (p = 0 ∨ q = 0 ∨ w = 0) →
                r (t' + p • ea + q • eb + w • ec) = 0 := fun p q w h0 =>
              ih _ (hsub p q w h0) _ rfl
            have r1 : r (t' + ec + eb) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 1 1 (Or.inl rfl)
            have r2 : r (t' + ec + ea) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 1 0 1 (Or.inr (Or.inl rfl))
            have r3 : r (t' + ec) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 0 1 (Or.inl rfl)
            have r4 : r (t' + eb + ea) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 1 1 0 (Or.inr (Or.inr rfl))
            have r5 : r (t' + eb) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 1 0 (Or.inl rfl)
            have r6 : r (t' + ea) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 1 0 0 (Or.inr (Or.inl rfl))
            have r7 : r t' = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 0 0 (Or.inl rfl)
            rw [hexp, htop, r1, r2, r3, r4, r5, r6, r7] at hdd0
            simpa using hdd0
  refine ⟨Q, ℓ, c₀, fun t => ?_⟩
  have hrt : f t + q t = 0 := hr_zero (suppCard t) t rfl
  calc f t = f t + (f t + q t) := by rw [hrt, add_zero]
    _ = (f t + f t) + q t := by rw [add_assoc]
    _ = q t := by rw [zmod2_add_self, zero_add]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_length (gs : List Gate) :
    ∀ x : List Bool, (gs.foldl step x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x; simp only [List.foldl_cons, ih, step]; simp; omega

lemma foldl_step_getD (gs : List Gate) :
    ∀ (x : List Bool) (i : ℕ), i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro x i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp only [step, List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma foldl_step_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl step x = step (gs.foldl step x) g := by simp [List.foldl_append]

lemma step_getD_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

lemma step_getD_old (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ hi

def bitsN (n : ℕ) (v : Fin n → F) : List Bool := List.ofFn (fun j : Fin n => decide (v j = 1))

lemma bitsN_length (n : ℕ) (v : Fin n → F) : (bitsN n v).length = n := by simp [bitsN]

lemma bitsN_getD (n : ℕ) (v : Fin n → F) (j : ℕ) (hj : j < n) :
    (bitsN n v).getD j false = decide (v ⟨j, hj⟩ = 1) := by
  simp [bitsN, List.getD_eq_getElem?_getD, hj]

def GOk (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧ (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.mod 2 ∨
    (h.op = GateOp.not ∧ h.inputs.length = 1))

def LegalG (n : ℕ) (ds : List Gate) : Prop :=
  (∀ j < ds.length, ∀ i ∈ (ds.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧ ∀ h ∈ ds, GOk h

noncomputable def costG (ds : List Gate) : ℕ :=
  ds.countP (fun h => @decide ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2)
    (Classical.propDecidable _))

lemma costG_snoc_zero (ds : List Gate) (g : Gate)
    (h : ¬((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) :
    costG (ds ++ [g]) = costG ds := by
  unfold costG; rw [List.countP_append]; simp [h]

lemma costG_snoc_one (ds : List Gate) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    costG (ds ++ [g]) = costG ds + 1 := by
  unfold costG; rw [List.countP_append]; simp [h]

def lin {k : ℕ} (s u : Fin k → F) : Bool := decide (dotProduct s u = 1)

lemma lin_add_right {k : ℕ} (s u v : Fin k → F) : lin s (u + v) = xor (lin s u) (lin s v) := by
  simp only [lin, dotProduct_add, dec_add]

lemma lin_add_left {k : ℕ} (s s' u : Fin k → F) : lin (s + s') u = xor (lin s u) (lin s' u) := by
  simp only [lin, add_dotProduct, dec_add]

lemma lin_zero_left {k : ℕ} (u : Fin k → F) : lin (0 : Fin k → F) u = false := by simp [lin]

lemma lin_bit_smul {k : ℕ} (s d : Fin k → F) (b : Bool) :
    lin s ((if b then (1 : F) else 0) • d) = (b && lin s d) := by cases b <;> simp [lin]

lemma lin_single {k : ℕ} (j : Fin k) (u : Fin k → F) :
    lin (Pi.single j 1) u = decide (u j = 1) := by simp [lin, single_dotProduct]

lemma lin_sum {k : ℕ} (ins : List ℕ) (s : ℕ → Fin k → F) (u : Fin k → F) :
    lin (ins.map s).sum u = ins.foldr (fun i acc => xor (lin (s i) u) acc) false := by
  induction ins with
  | nil => simp [lin_zero_left]
  | cons a l ih => simp [List.sum_cons, lin_add_left, ih]

lemma aff_eval (op : GateOp) (ins : List ℕ) (hok : GOk ⟨op, ins⟩)
    (hn : ¬((op = GateOp.and ∨ op = GateOp.or) ∧ ins.length = 2)) (cs ls : ℕ → Bool) :
    op.eval (ins.map fun i => xor (cs i) (ls i)) =
      xor (op.eval (ins.map cs)) (ins.foldr (fun i acc => xor (ls i) acc) false) := by
  obtain ⟨hl, hop⟩ := hok
  simp only at hl hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩ <;> simp [GateOp.eval]
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    generalize cs a = A; generalize ls a = B
    rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩ <;> cases A <;> cases B <;> decide
  · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩
    · exact absurd ⟨Or.inl rfl, rfl⟩ hn
    · exact absurd ⟨Or.inr rfl, rfl⟩ hn
    · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      generalize cs a = A; generalize ls a = B; generalize cs b = C; generalize ls b = D
      cases A <;> cases B <;> cases C <;> cases D <;> decide
    · simp at h
  · simp at hl

def IsAff {t : ℕ} (f : (Fin t → F) → Bool) : Prop :=
  ∃ (v : Fin t → F) (b : Bool), ∀ z, f z = xor b (lin v z)

lemma isAff_const {t : ℕ} (b : Bool) : IsAff (fun _ : Fin t → F => b) :=
  ⟨0, b, fun z => by simp [lin_zero_left]⟩

lemma isAff_coord {t : ℕ} (j : Fin t) : IsAff (fun z : Fin t → F => decide (z j = 1)) :=
  ⟨Pi.single j 1, false, fun z => by simp [lin_single]⟩

lemma isAff_xor {t : ℕ} {f₁ f₂ : (Fin t → F) → Bool} (h1 : IsAff f₁) (h2 : IsAff f₂) :
    IsAff (fun z => xor (f₁ z) (f₂ z)) := by
  obtain ⟨v1, b1, h1⟩ := h1
  obtain ⟨v2, b2, h2⟩ := h2
  refine ⟨v1 + v2, xor b1 b2, fun z => ?_⟩
  dsimp only
  rw [h1 z, h2 z, lin_add_left]
  cases b1 <;> cases b2 <;> cases lin v1 z <;> cases lin v2 z <;> rfl

lemma isAff_congr {t : ℕ} {f₁ f₂ : (Fin t → F) → Bool} (h1 : IsAff f₁) (heq : ∀ z, f₁ z = f₂ z) :
    IsAff f₂ := by
  obtain ⟨v, b, hv⟩ := h1; exact ⟨v, b, fun z => (heq z).symm.trans (hv z)⟩

lemma isAff_gate {t : ℕ} (g : Gate) (hg : GOk g)
    (hnb : ¬((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2))
    (cs : ℕ → (Fin t → F) → Bool) (hcs : ∀ i ∈ g.inputs, IsAff (cs i)) :
    IsAff (fun z => g.op.eval (g.inputs.map fun i => cs i z)) := by
  classical
  have hpick : ∀ i : ℕ, ∃ p : (Fin t → F) × Bool, i ∈ g.inputs → ∀ z, cs i z = xor p.2 (lin p.1 z) := by
    intro i
    by_cases hi : i ∈ g.inputs
    · obtain ⟨v, b, hv⟩ := hcs i hi
      exact ⟨(v, b), fun _ => hv⟩
    · exact ⟨(0, false), fun h => absurd h hi⟩
  choose p hp using hpick
  refine ⟨(g.inputs.map fun i => (p i).1).sum, g.op.eval (g.inputs.map fun i => (p i).2), fun z => ?_⟩
  have hmap : (g.inputs.map fun i => cs i z) = g.inputs.map (fun i => xor (p i).2 (lin (p i).1 z)) :=
    List.map_congr_left (fun i hi => hp i hi z)
  dsimp only
  rw [hmap, aff_eval g.op g.inputs hg hnb (fun i => (p i).2) (fun i => lin (p i).1 z), lin_sum]

lemma isAff_hasDeg1 {t : ℕ} {f : (Fin t → F) → Bool} (hf : IsAff f) :
    HasDeg 1 (fun z => b2f (f z)) := by
  obtain ⟨v, b, hv⟩ := hf
  have heq : (fun z => b2f (f z)) = fun z => dotProduct v z + b2f b := by
    funext z
    rw [hv z, b2f_xor, lin, b2f_decide, add_comm]
  rw [heq]
  exact hasDeg_dot v (b2f b)

structure Piece (k t : ℕ) where
  U : Submodule F (Fin k → F)
  r : ℕ
  e : ℕ
  p : (Fin t → F) → (Fin k → F)
  c : ℕ → (Fin t → F) → Bool
  s : ℕ → (Fin k → F)

def PInv (k t : ℕ) (gs : List Gate) (P : Piece k t) : Prop :=
  Module.finrank F P.U + P.r = k ∧ P.e + P.r ≤ costG gs ∧
  (P.e = 0 → (∀ w < k + t + gs.length, IsAff (P.c w)) ∧
    ∀ j : Fin k, IsAff (fun z => decide (P.p z j = 1))) ∧
  ∀ z, ∀ u ∈ P.U, ∀ w < k + t + gs.length,
    (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD w false = xor (P.c w z) (lin (P.s w) u)

noncomputable def cnt {k t : ℕ} (L : List (Piece k t)) (z : Fin t → F) (x : Fin k → F) : ℕ :=
  L.countP (fun Q => @decide (x - Q.p z ∈ Q.U) (Classical.propDecidable _))

lemma xin_length (k t : ℕ) (v : Fin k → F) (z : Fin t → F) :
    (bitsN k v ++ bitsN t z).length = k + t := by simp [bitsN_length]

lemma cw_old (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ [g]).foldl step x).getD w false = (gs.foldl step x).getD w false := by
  rw [foldl_step_snoc, step_getD_old _ _ _ (by rw [foldl_step_length]; exact hw)]

lemma cw_new (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl step x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false) := by
  rw [foldl_step_snoc, ← foldl_step_length, step_getD_new]

lemma split_dim {k : ℕ} (U : Submodule F (Fin k → F)) (s d : Fin k → F) (hd : d ∈ U)
    (hsd : dotProduct s d = 1) :
    ∃ U' : Submodule F (Fin k → F), Module.finrank F U' + 1 = Module.finrank F U ∧
      ∀ v, v ∈ U' ↔ v ∈ U ∧ dotProduct s v = 0 := by
  let ψ := (dotLin s).comp U.subtype
  refine ⟨(LinearMap.ker ψ).map U.subtype, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have hr : LinearMap.range ψ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨y • ⟨d, hd⟩, ?_⟩
      simp [ψ, dotLin, dotProduct_smul, hsd]
    rw [hr, finrank_top, Module.finrank_self] at h1
    rw [Submodule.finrank_map_subtype_eq]
    omega
  · intro v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, ψ,
      LinearMap.comp_apply, dotLin, LinearMap.coe_mk, AddHom.coe_mk]
    exact ⟨fun ⟨y, hy, h⟩ => h ▸ ⟨y.2, hy⟩, fun ⟨hv, h0⟩ => ⟨⟨v, hv⟩, h0, rfl⟩⟩

lemma bit_cases (a : F) (b : Bool) : a - (if b then 1 else 0) = 0 ↔ decide (a = 1) = b := by
  fin_cases a <;> cases b <;> decide

lemma pbit_shift {k : ℕ} (v d : Fin k → F) (b : Bool) (j : Fin k) :
    decide ((v + (if b then (1 : F) else 0) • d) j = 1) =
      xor (decide (v j = 1)) (b && decide (d j = 1)) := by cases b <;> simp [dec_add]

lemma init_piece (k t : ℕ) : ∃ P : Piece k t, PInv k t [] P ∧ ∀ z x, x - P.p z ∈ P.U := by
  let P : Piece k t :=
    { U := ⊤, r := 0, e := 0, p := fun _ => 0,
      c := fun w z => if w < k then false else
        if h : w - k < t then decide (z ⟨w - k, h⟩ = 1) else false,
      s := fun w => if h : w < k then Pi.single ⟨w, h⟩ 1 else 0 }
  refine ⟨P, ⟨by simp [P], by simp [P, costG], ?_, ?_⟩, fun _ _ => Submodule.mem_top⟩
  · intro _
    refine ⟨fun w hw => ?_, fun j => isAff_congr (isAff_const false) (fun z => by simp [P])⟩
    by_cases hwk : w < k
    · exact isAff_congr (isAff_const false) (fun z => by simp [P, hwk])
    · have hwt : w - k < t := by simp at hw; omega
      exact isAff_congr (isAff_coord ⟨w - k, hwt⟩) (fun z => by simp [P, hwk, hwt])
  · intro z u _ w hw
    simp only [List.length_nil, add_zero] at hw
    simp only [List.foldl_nil, P, zero_add]
    by_cases hwk : w < k
    · rw [List.getD_append _ _ _ _ (by rw [bitsN_length]; exact hwk), bitsN_getD _ _ _ hwk]
      simp [hwk, lin_single]
    · have hwt : w - k < t := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [bitsN_length]; omega), bitsN_length,
        bitsN_getD _ _ _ hwt]
      simp [hwk, hwt, lin_zero_left]

lemma cnt_single_mem {k t : ℕ} (Q : Piece k t) (z : Fin t → F) (x : Fin k → F)
    (h : x - Q.p z ∈ Q.U) : cnt [Q] z x = 1 := by simp [cnt, h]

lemma cnt_single_not {k t : ℕ} (Q : Piece k t) (z : Fin t → F) (x : Fin k → F)
    (h : x - Q.p z ∉ Q.U) : cnt [Q] z x = 0 := by simp [cnt, h]

lemma step_piece {k t : ℕ} (gs : List Gate) (g : Gate) (hg : GOk g)
    (hin : ∀ i ∈ g.inputs, i < k + t + gs.length) (P : Piece k t) (hP : PInv k t gs P) :
    ∃ L : List (Piece k t), (∀ Q ∈ L, PInv k t (gs ++ [g]) Q) ∧
      ∀ z x, (x - P.p z ∈ P.U → cnt L z x = 1) ∧ (x - P.p z ∉ P.U → cnt L z x = 0) := by
  classical
  obtain ⟨hrank, hcost, haff, hval⟩ := hP
  set m := k + t + gs.length with hm
  have hlen1 : k + t + (gs ++ [g]).length = m + 1 := by simp [hm]; omega
  have Cold : ∀ v z w, w < m → ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD w false =
      (gs.foldl step (bitsN k v ++ bitsN t z)).getD w false := fun v z w hw =>
    cw_old gs g _ w (by rw [xin_length]; omega)
  have Cnew : ∀ v z, ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD m false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step (bitsN k v ++ bitsN t z)).getD i false) := by
    intro v z; have h := cw_new gs g (bitsN k v ++ bitsN t z); rw [xin_length] at h; exact h
  by_cases hbin : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  · obtain ⟨hop, hl2⟩ := hbin
    obtain ⟨i1, i2, hgi⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs, hl2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hi1 : i1 < m := hin i1 (by rw [hgi]; simp)
    have hi2 : i2 < m := hin i2 (by rw [hgi]; simp)
    have hcostC : costG (gs ++ [g]) = costG gs + 1 := costG_snoc_one _ _ ⟨hop, hl2⟩
    obtain ⟨A, hA⟩ : ∃ A : Bool, ∀ X Y : Bool,
        g.op.eval [X, Y] = (if A then (X && Y) else (X || Y)) := by
      rcases hop with h | h
      · exact ⟨true, fun X Y => by rw [h]; cases X <;> cases Y <;> rfl⟩
      · exact ⟨false, fun X Y => by rw [h]; cases X <;> cases Y <;> rfl⟩
    by_cases hz : ∀ u ∈ P.U, lin (P.s i1) u = false ∧ lin (P.s i2) u = false
    · let Q : Piece k t :=
        { U := P.U, r := P.r, e := P.e + 1, p := P.p,
          c := fun w => if w = m then (fun z => g.op.eval [P.c i1 z, P.c i2 z]) else P.c w,
          s := fun w => if w = m then 0 else P.s w }
      refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
        fun h => cnt_single_not Q z x h⟩⟩
      intro Q' hQ'
      simp only [List.mem_singleton] at hQ'
      subst hQ'
      refine ⟨hrank, by simp only [Q]; rw [hcostC]; omega, by intro h; simp only [Q] at h; omega, ?_⟩
      intro z u hu w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        simp only [Q, if_true]
        rw [Cnew, hgi]
        simp only [List.map_cons, List.map_nil]
        rw [hval z u hu i1 hi1, hval z u hu i2 hi2, (hz u hu).1, (hz u hu).2, lin_zero_left]
        simp
      · simp only [Q, hwm, if_false]
        rw [Cold _ _ _ (by omega), hval z u hu w (by omega)]
    · push Not at hz
      obtain ⟨u0, hu0, hne⟩ := hz
      have key : ∀ ia ib, ia < m → ib < m →
          (∀ v z, ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD m false =
            (if A then ((gs.foldl step (bitsN k v ++ bitsN t z)).getD ia false &&
              (gs.foldl step (bitsN k v ++ bitsN t z)).getD ib false)
             else ((gs.foldl step (bitsN k v ++ bitsN t z)).getD ia false ||
              (gs.foldl step (bitsN k v ++ bitsN t z)).getD ib false))) →
          ∀ d ∈ P.U, lin (P.s ia) d = true →
          ∃ L : List (Piece k t), (∀ Q ∈ L, PInv k t (gs ++ [g]) Q) ∧
            ∀ z x, (x - P.p z ∈ P.U → cnt L z x = 1) ∧ (x - P.p z ∉ P.U → cnt L z x = 0) := by
        intro ia ib hia hib hCval d hd hdl
        have hsd : dotProduct (P.s ia) d = 1 := of_decide_eq_true hdl
        obtain ⟨U', hU'rank, hU'mem⟩ := split_dim P.U (P.s ia) d hd hsd
        have hU'U : ∀ v, v ∈ U' → v ∈ P.U := fun v hv => ((hU'mem v).1 hv).1
        have hU'lin : ∀ v, v ∈ U' → lin (P.s ia) v = false := fun v hv => by
          simp [lin, ((hU'mem v).1 hv).2]
        let bf : Bool → (Fin t → F) → Bool := fun β z => xor β (P.c ia z)
        let pass : Bool → Bool := fun β => if A then β else !β
        let child : Bool → Piece k t := fun β =>
          { U := U', r := P.r + 1, e := P.e,
            p := fun z => P.p z + (if bf β z then (1 : F) else 0) • d,
            c := fun w z => if w = m then
                (if pass β then xor (P.c ib z) (bf β z && lin (P.s ib) d) else β)
              else xor (P.c w z) (bf β z && lin (P.s w) d),
            s := fun w => if w = m then (if pass β then P.s ib else 0) else P.s w }
        have hmem : ∀ β z x, (x - (child β).p z ∈ (child β).U ↔
            (x - P.p z ∈ P.U ∧ lin (P.s ia) (x - P.p z) = bf β z)) := by
          intro β z x
          show x - (P.p z + (if bf β z then (1 : F) else 0) • d) ∈ U' ↔ _
          rw [hU'mem, sub_add_eq_sub_sub]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨by simpa using P.U.add_mem h1 (P.U.smul_mem (if bf β z then (1 : F) else 0) hd), ?_⟩
            rw [dotProduct_sub, dotProduct_smul, hsd, smul_eq_mul, mul_one] at h2
            exact (bit_cases _ _).1 h2
          · rintro ⟨h1, h2⟩
            refine ⟨P.U.sub_mem h1 (P.U.smul_mem _ hd), ?_⟩
            rw [dotProduct_sub, dotProduct_smul, hsd, smul_eq_mul, mul_one]
            exact (bit_cases _ _).2 h2
        have hchild : ∀ β, PInv k t (gs ++ [g]) (child β) := by
          intro β
          refine ⟨by show Module.finrank F U' + (P.r + 1) = k; omega,
            by show P.e + (P.r + 1) ≤ costG (gs ++ [g]); rw [hcostC]; omega, ?_, ?_⟩
          · intro he0
            obtain ⟨hcw, hpb⟩ := haff he0
            have hbf : IsAff (bf β) := isAff_xor (isAff_const β) (hcw ia hia)
            have hold : ∀ w, w < m → IsAff (fun z => xor (P.c w z) (bf β z && lin (P.s w) d)) := by
              intro w hw
              cases hlw : lin (P.s w) d
              · exact isAff_congr (hcw w hw) (fun z => by simp)
              · exact isAff_congr (isAff_xor (hcw w hw) hbf) (fun z => by simp)
            refine ⟨fun w hw => ?_, fun j => ?_⟩
            · rw [hlen1] at hw
              by_cases hwm : w = m
              · subst hwm
                cases hp : pass β
                · exact isAff_congr (isAff_const β) (fun z => by simp [child, hp])
                · exact isAff_congr (hold ib hib) (fun z => by simp [child, hp])
              · exact isAff_congr (hold w (by omega)) (fun z => by simp [child, hwm])
            · cases hdj : decide (d j = 1)
              · exact isAff_congr (hpb j) (fun z => by dsimp only [child]; rw [pbit_shift, hdj]; simp)
              · exact isAff_congr (isAff_xor (hpb j) hbf) (fun z => by dsimp only [child]; rw [pbit_shift, hdj]; simp)
          · intro z u' hu' w hw
            rw [hlen1] at hw
            have hu : (if bf β z then (1 : F) else 0) • d + u' ∈ P.U :=
              P.U.add_mem (P.U.smul_mem _ hd) (hU'U u' hu')
            have hpt : (child β).p z + u' = P.p z + ((if bf β z then (1 : F) else 0) • d + u') := by
              show P.p z + _ + u' = _; rw [add_assoc]
            have hold : ∀ w, w < m →
                (gs.foldl step (bitsN k ((child β).p z + u') ++ bitsN t z)).getD w false
                  = xor (xor (P.c w z) (bf β z && lin (P.s w) d)) (lin (P.s w) u') := fun w hw => by
              rw [hpt, hval z _ hu w hw, lin_add_right, lin_bit_smul, Bool.xor_assoc]
            by_cases hwm : w = m
            · subst hwm
              rw [hCval, hold ia hia, hold ib hib, hdl, hU'lin u' hu']
              show _ = xor (if m = m then (if pass β then _ else β) else _)
                (lin (if m = m then (if pass β then P.s ib else 0) else P.s m) u')
              simp only [if_true]
              have hli : lin (if pass β then P.s ib else 0) u' = (pass β && lin (P.s ib) u') := by
                cases pass β <;> simp [lin_zero_left]
              rw [hli]
              simp only [pass, bf]
              generalize P.c ia z = C1; generalize P.c ib z = C2
              generalize lin (P.s ib) d = L1; generalize lin (P.s ib) u' = L2
              cases A <;> cases β <;> cases C1 <;> cases C2 <;> cases L1 <;> cases L2 <;>
                simp [lin_zero_left]
            · rw [Cold _ _ _ (by omega), hold w (by omega)]
              show _ = xor (if w = m then _ else _) (lin (if w = m then _ else P.s w) u')
              simp [hwm]
        refine ⟨[child false, child true], ?_, fun z x => ⟨fun h => ?_, fun h => ?_⟩⟩
        · intro Q hQ
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
          rcases hQ with rfl | rfl <;> exact hchild _
        · by_cases hl : lin (P.s ia) (x - P.p z) = bf false z
          · have m0 : x - (child false).p z ∈ (child false).U := (hmem false z x).2 ⟨h, hl⟩
            have m1 : x - (child true).p z ∉ (child true).U := by
              rw [hmem]; rintro ⟨_, h2⟩; rw [hl] at h2; simp [bf] at h2
            simp [cnt, List.countP_cons, m0, m1]
          · have m0 : x - (child false).p z ∉ (child false).U := by
              rw [hmem]; exact fun hh => hl hh.2
            have m1 : x - (child true).p z ∈ (child true).U := by
              rw [hmem]
              refine ⟨h, ?_⟩
              revert hl; simp only [bf]
              cases lin (P.s ia) (x - P.p z) <;> cases P.c ia z <;> simp
            simp [cnt, List.countP_cons, m0, m1]
        · have m0 : x - (child false).p z ∉ (child false).U := by rw [hmem]; exact fun hh => h hh.1
          have m1 : x - (child true).p z ∉ (child true).U := by rw [hmem]; exact fun hh => h hh.1
          simp [cnt, List.countP_cons, m0, m1]
      by_cases h1 : lin (P.s i1) u0 = true
      · refine key i1 i2 hi1 hi2 (fun v z => ?_) u0 hu0 h1
        rw [Cnew, hgi]; exact hA _ _
      · have h2 : lin (P.s i2) u0 = true := by
          cases hb : lin (P.s i1) u0
          · exact Bool.eq_true_of_not_eq_false (hne hb)
          · exact absurd hb h1
        refine key i2 i1 hi2 hi1 (fun v z => ?_) u0 hu0 h2
        rw [Cnew, hgi]; simp only [List.map_cons, List.map_nil]
        rw [hA]; cases A <;> simp [Bool.and_comm, Bool.or_comm]
  · let Q : Piece k t :=
      { U := P.U, r := P.r, e := P.e, p := P.p,
        c := fun w => if w = m then (fun z => g.op.eval (g.inputs.map fun i => P.c i z)) else P.c w,
        s := fun w => if w = m then (g.inputs.map P.s).sum else P.s w }
    refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
      fun h => cnt_single_not Q z x h⟩⟩
    intro Q' hQ'
    simp only [List.mem_singleton] at hQ'
    subst hQ'
    refine ⟨hrank, by simp only [Q]; rw [costG_snoc_zero _ _ hbin]; exact hcost, ?_, ?_⟩
    · intro he0
      obtain ⟨hcw, hpb⟩ := haff he0
      refine ⟨fun w hw => ?_, hpb⟩
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        have hg_aff := isAff_gate g hg hbin P.c (fun i hi => hcw i (hin i hi))
        exact isAff_congr hg_aff (fun z => by simp [Q])
      · exact isAff_congr (hcw w (by omega)) (fun z => by simp [Q, hwm])
    · intro z u hu w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        simp only [Q, if_true]
        rw [Cnew]
        have e1 : (g.inputs.map fun i => (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD i false)
            = g.inputs.map fun i => xor (P.c i z) (lin (P.s i) u) :=
          List.map_congr_left (fun i hi => hval z u hu i (hin i hi))
        rw [e1, aff_eval g.op g.inputs hg hbin (fun i => P.c i z) (fun i => lin (P.s i) u), lin_sum]
      · simp only [Q, hwm, if_false]
        rw [Cold _ _ _ (by omega), hval z u hu w (by omega)]

lemma step_list {k t : ℕ} (gs : List Gate) (g : Gate) (hg : GOk g)
    (hin : ∀ i ∈ g.inputs, i < k + t + gs.length) :
    ∀ L : List (Piece k t), (∀ P ∈ L, PInv k t gs P) →
      ∃ L' : List (Piece k t), (∀ Q ∈ L', PInv k t (gs ++ [g]) Q) ∧
        ∀ z x, cnt L' z x = cnt L z x := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, fun _ _ => rfl⟩
  | cons P L ih =>
    intro hL
    obtain ⟨LP, hLP, hcP⟩ := step_piece gs g hg hin P (hL P (List.mem_cons_self ..))
    obtain ⟨L', hL', hc'⟩ := ih (fun Q hQ => hL Q (List.mem_cons_of_mem _ hQ))
    refine ⟨LP ++ L', fun Q hQ => (List.mem_append.1 hQ).elim (hLP Q) (hL' Q), fun z x => ?_⟩
    have e1 : cnt (LP ++ L') z x = cnt LP z x + cnt L' z x := by simp only [cnt, List.countP_append]
    rw [e1, hc' z x]
    by_cases hm : x - P.p z ∈ P.U
    · rw [(hcP z x).1 hm]; simp only [cnt, List.countP_cons, hm, decide_true, ↓reduceIte]; omega
    · rw [(hcP z x).2 hm]; simp only [cnt, List.countP_cons, hm, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

lemma all_gates {k t : ℕ} (C : Circuit) (hC : ∀ h ∈ C.gates, GOk h)
    (hRB : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < k + t + j) :
    ∀ n, n ≤ C.gates.length → ∃ L : List (Piece k t),
      (∀ P ∈ L, PInv k t (C.gates.take n) P) ∧ ∀ z x, cnt L z x = 1 := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨P, hP, hm⟩ := init_piece k t
    exact ⟨[P], by simpa using hP, fun z x => cnt_single_mem P z x (hm z x)⟩
  | succ n ih =>
    intro hn
    obtain ⟨L, hL, hc⟩ := ih (by omega)
    have hlt : n < C.gates.length := by omega
    have htake : C.gates.take (n + 1) = C.gates.take n ++ [C.gates[n]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]; rfl
    have e : C.gates.getD n ⟨GateOp.or, []⟩ = C.gates[n] := by
      simp [List.getD_eq_getElem?_getD, hlt]
    obtain ⟨L', hL', hc'⟩ := step_list (C.gates.take n) (C.gates[n]) (hC _ (List.getElem_mem hlt))
      (fun i hi => by have h := hRB n hlt i (by rw [e]; exact hi); rw [List.length_take]; omega) L hL
    exact ⟨L', by rw [htake]; exact hL', fun z x => (hc' z x).trans (hc z x)⟩

lemma exists_unique_of_count {α : Type*} (q : α → Prop) :
    ∀ l : List α, l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 1 →
      ∃! i : Fin l.length, q (l.get i) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    rw [List.countP_cons] at h
    by_cases ha : q a
    · have h0 : l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 0 := by
        have e : (@decide (q a) (Classical.propDecidable _)) = true :=
          @decide_eq_true _ (Classical.propDecidable _) ha
        rw [e, if_pos rfl] at h; omega
      rw [List.countP_eq_zero] at h0
      refine ⟨⟨0, by simp⟩, by simpa using ha, ?_⟩
      intro j hj
      rcases j with ⟨_ | j, hjl⟩
      · rfl
      · exfalso
        have hj' : q (l.get ⟨j, by simpa using hjl⟩) := by simpa using hj
        have := h0 (l.get ⟨j, by simpa using hjl⟩) (List.get_mem _ _)
        simp only [decide_eq_true_eq] at this
        exact this hj'
    · have h1 : l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 1 := by
        have e : (@decide (q a) (Classical.propDecidable _)) = false :=
          @decide_eq_false _ (Classical.propDecidable _) ha
        rw [e, if_neg Bool.false_ne_true] at h; omega
      obtain ⟨i, hi, huniq⟩ := ih h1
      refine ⟨i.succ, by simpa using hi, ?_⟩
      intro j hj
      rcases j with ⟨_ | j, hjl⟩
      · exfalso; exact ha (by simpa using hj)
      · have := huniq ⟨j, by simpa using hjl⟩ (by simpa using hj)
        exact Fin.ext (by simp [← this])

lemma circuit_decomp (k s : ℕ) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * k) C)
    (hG : ∀ h ∈ C.gates, GOk h) (hcost : costG C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F (Fin k → F))
      (a : Fin N → (Fin k → F)) (p : Fin N → (Fin k → F) → (Fin k → F))
      (c : Fin N → (Fin k → F) → Bool),
      0 < N ∧
      (∀ i, Module.finrank F (U i) + r i = k ∧ r i ≤ s) ∧
      (∀ i, r i = s → IsAff (c i) ∧ ∀ j : Fin k, IsAff (fun z => decide (p i z j = 1))) ∧
      (∀ y x, ∃! i : Fin N, x - p i y ∈ U i) ∧
      (∀ i y u, u ∈ U i →
        C.eval (bitsN k (p i y + u) ++ bitsN k y) = xor (c i y) (lin (a i) u)) := by
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < k + k + j := by
    intro j hj i hi
    have h := hRB j hj i hi
    omega
  obtain ⟨L, hL, hc⟩ := all_gates (k := k) (t := k) C hG hRB' C.gates.length le_rfl
  rw [List.take_length] at hL
  set M := k + k + C.gates.length with hM
  refine ⟨L.length, fun i => (L.get i).r, fun i => (L.get i).U,
    fun i => if C.output < M then (L.get i).s C.output else 0,
    fun i => (L.get i).p,
    fun i y => if C.output < M then (L.get i).c C.output y else false,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := hc 0 0
    rcases L with _ | ⟨P, L⟩
    · simp [cnt] at h
    · simp
  · intro i
    obtain ⟨hrank, hce, _, _⟩ := hL (L.get i) (List.get_mem _ _)
    dsimp only
    exact ⟨hrank, by omega⟩
  · intro i hris
    dsimp only at hris ⊢
    obtain ⟨_, hce, haff, _⟩ := hL (L.get i) (List.get_mem _ _)
    have he0 : (L.get i).e = 0 := by omega
    obtain ⟨hcw, hpb⟩ := haff he0
    refine ⟨?_, hpb⟩
    by_cases ho : C.output < M
    · exact isAff_congr (hcw C.output ho) (fun y => by simp [ho])
    · exact isAff_congr (isAff_const false) (fun y => by simp [ho])
  · intro y x
    exact exists_unique_of_count (fun Q : Piece k k => x - Q.p y ∈ Q.U) L (hc y x)
  · intro i y u hu
    obtain ⟨_, _, _, hval⟩ := hL (L.get i) (List.get_mem _ _)
    dsimp only
    show (C.gates.foldl step (bitsN k ((L.get i).p y + u) ++ bitsN k y)).getD C.output false = _
    by_cases ho : C.output < M
    · rw [hval y u hu C.output ho]
      simp only [ho, ↓reduceIte]
    · simp only [ho, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by rw [foldl_step_length, xin_length]; omega)]
      simp [lin_zero_left]

end PEqualNP.Outside.L_meta_33611.Weighted

namespace PEqualNP.Outside.L_meta_33611
namespace SelectorBranches

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_33611.Weighted
open scoped Classical

lemma weightedCircuitBranches (k s : ℕ) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * k) C)
    (hG : ∀ g ∈ C.gates, GOk g) (hcost : costG C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F (Fin k → F))
      (a : Fin N → (Fin k → F)) (p : Fin N → (Fin k → F) → (Fin k → F))
      (c : Fin N → (Fin k → F) → Bool) (w : Fin N → ℝ),
      (∀ i, Module.finrank F (U i) + r i = k ∧ r i ≤ s) ∧
      (∀ i, r i = s → IsAff (c i) ∧ ∀ j, IsAff (fun y => decide (p i y j = 1))) ∧
      (∀ i, w i = (2:ℝ)^(k - r i) / 2^k) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      ∀ (t : ℕ) (Y : (Fin t → F) → (Fin k → F)) (g : (Fin k → F) → F),
        (∑ x : Fin k → F, ∑ b : Fin t → F,
          if C.eval (bitsN k x ++ bitsN k (Y b)) = decide (dotProduct x (Y b) + g (Y b) = 1)
          then (1 : ℝ) else -1) / 2^(k+t) =
        ∑ i, w i * ((∑ b : Fin t → F, if Y b + a i ∈ perp (U i)
          then (chi (b2f (c i (Y b)) + dotProduct (p i (Y b)) (Y b) + g (Y b)) : ℝ)
          else 0) / 2^t) := by
  classical
  obtain ⟨N, r, U, a, p, c, _, hrk, haff, hpart, heval⟩ := circuit_decomp k s C hRB hG hcost
  have hbij : ∀ y : Fin k → F, Function.Bijective (fun z : Σ i : Fin N, U i => p z.1 y + z.2.1) := by
    intro y
    constructor
    · rintro ⟨i1, u1⟩ ⟨i2, u2⟩ hEq
      dsimp only at hEq
      let x := p i1 y + u1.1
      have h1 : x - p i1 y ∈ U i1 := by simp [x, u1.2]
      have h2 : x - p i2 y ∈ U i2 := by rw [show x = p i2 y + u2.1 from hEq]; simp [u2.2]
      obtain ⟨i0, _, huniq⟩ := hpart y x
      have hi : i1 = i2 := (huniq i1 h1).trans (huniq i2 h2).symm
      subst hi
      have hu : u1.1 = u2.1 := add_left_cancel hEq
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hu))
    · intro x
      obtain ⟨i, hi, _⟩ := hpart y x
      exact ⟨⟨i, ⟨x - p i y, hi⟩⟩, add_sub_cancel (p i y) x⟩

  have hcardU : ∀ i : Fin N, Fintype.card (U i) = 2 ^ (k - r i) := fun i => by
    rw [card_submodule]; have := (hrk i).1; congr 1; omega
  have hsum_card : (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k := by
    have h1 := Fintype.card_congr (Equiv.ofBijective _ (hbij 0))
    rw [Fintype.card_sigma, card_fin_fun] at h1
    simp_rw [hcardU] at h1
    exact h1
  refine ⟨N, r, U, a, p, c, fun i => (2 : ℝ)^(k - r i) / 2^k, hrk, haff, fun _ => rfl,
    fun _ => by positivity, ?_, ?_⟩
  · rw [← Finset.sum_div]
    have h : (∑ i, (2 : ℝ) ^ (k - r i)) = 2^k := by exact_mod_cast hsum_card
    rw [h, div_self (by positivity)]
  intro t Y g
  have hinner (y : Fin k → F) :
      (∑ x : Fin k → F,
        if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
      ∑ i : Fin N, chi (b2f (c i y) + dotProduct (p i y) y + g y) *
        (if y + a i ∈ perp (U i) then (2 ^ (k - r i) : ℤ) else 0) := by
    rw [← Fintype.sum_equiv (Equiv.ofBijective _ (hbij y))
      (fun z => if C.eval (bitsN k (p z.1 y + z.2.1) ++ bitsN k y) =
          decide (dotProduct (p z.1 y + z.2.1) y + g y = 1)
        then (1 : ℤ) else -1) _ (fun _ => rfl)]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ∀ u : U i,
        (if C.eval (bitsN k (p i y + u.1) ++ bitsN k y) =
            decide (dotProduct (p i y + u.1) y + g y = 1)
          then (1 : ℤ) else -1) =
        chi (b2f (c i y) + dotProduct (p i y) y + g y) * chi (dotProduct (y + a i) u.1) := by
      intro u
      rw [agree_eq_sg_chi, heval i y u.1 u.2, lin, sg_xor, sg_eq_chi_b2f, add_dotProduct,
        dotProduct_comm u.1 y, add_dotProduct]
      simp only [chi_add]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_chi_dot_subspace, hcardU i]
    push_cast; rfl

  have hreal (y : Fin k → F) :
      (∑ x : Fin k → F, if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℝ) else -1) =
      ∑ i : Fin N, (2 : ℝ)^(k - r i) *
        (if y + a i ∈ perp (U i) then (chi (b2f (c i y) + dotProduct (p i y) y + g y) : ℝ)
          else 0) := by
    calc
      _ = ∑ i : Fin N, (chi (b2f (c i y) + dotProduct (p i y) y + g y) : ℝ) *
          (if y + a i ∈ perp (U i) then (2:ℝ)^(k - r i) else 0) := by
            exact_mod_cast hinner y
      _ = _ := Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
  rw [Finset.sum_comm]
  simp_rw [hreal]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end SelectorBranches
end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611
namespace SelectorBranches

open scoped Classical

lemma missingVerticalDirection {k t : ℕ} (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (B : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (d : Fin t → ZMod 2)
    (hd : B d ∉ K) (u : Fin k → ZMod 2) (f : (Fin t → ZMod 2) → ℝ)
    (hf : ∀ b, f b ≤ 1) :
    (∑ b : Fin t → ZMod 2, if u + B b ∈ K then f b else 0) / 2 ^ t ≤ 1 / 2 := by
  classical
  let g (b : Fin t → ZMod 2) : ℝ := if u + B b ∈ K then f b else 0
  have hm (b : Fin t → ZMod 2) (h1 : u + B b ∈ K) : u + B (b + d) ∉ K := by
    intro h2
    apply hd
    have h := K.sub_mem h2 h1
    rwa [show u + B (b + d) - (u + B b) = B d by rw [map_add]; abel] at h
  have hpair (b) : g b + g (b+d) ≤ 1 := by
    by_cases h1 : u + B b ∈ K
    · simpa only [g, if_pos h1, if_neg (hm b h1), add_zero] using hf b
    · by_cases h2 : u + B (b+d) ∈ K
      · simpa only [g, if_neg h1, if_pos h2, zero_add] using hf (b+d)
      · simp only [g, if_neg h1, if_neg h2, zero_add, zero_le_one]
  have he : ∑ b, g (b+d) = ∑ b, g b :=
    Fintype.sum_equiv (Equiv.addRight d) (fun b => g (b+d)) g (fun _ => rfl)
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpair b)
  rw [Finset.sum_add_distrib, he] at hle
  have htwo : (∑ b, g b) + (∑ b, g b) ≤ 2 ^ t := by
    simpa [Fintype.card_fun, ZMod.card] using hle
  change (∑ b, g b) / 2^t ≤ 1 / 2
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

lemma missingSelectorSide {k t n : ℕ} (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (H : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (B : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (u : Fin n → ZMod 2) (s₀ s₁ : Fin k → ZMod 2)
    (hB : ∀ d, B d ∈ K) (h₀ : u + H s₀ ∈ K) (h₁ : u + H s₁ ∉ K) :
    ∃ (a : Fin k → ZMod 2) (v : ZMod 2),
      dotProduct a s₀ = v ∧ dotProduct a s₁ ≠ v ∧
      ∀ s, dotProduct a s ≠ v → ∀ d, u + H s + B d ∉ K := by
  classical
  obtain ⟨f, hbad, hker⟩ := Submodule.exists_le_ker_of_notMem h₁
  let ψ := f.comp H
  let a := fun j : Fin k => ψ (Pi.single j 1)
  have hd (s : Fin k → ZMod 2) : dotProduct a s = f (H s) := by
    have he : s = ∑ j : Fin k, s j • Pi.single j (1 : ZMod 2) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    change dotProduct a s = ψ s
    conv_rhs => rw [he, map_sum]
    simp only [a, dotProduct, map_smul, smul_eq_mul, mul_comm]
  refine ⟨a, -f u, ?_, ?_, ?_⟩
  · have hh : f (u + H s₀) = 0 := hker h₀
    rw [map_add] at hh
    rw [hd]
    linear_combination hh
  · intro hb
    apply hbad
    rw [hd] at hb
    rw [map_add, hb, add_neg_cancel]
  · intro s hs d hin
    have hh : f (u + H s + B d) = 0 := hker hin
    have hb : f (B d) = 0 := hker (hB d)
    simp only [map_add, hb, add_zero] at hh
    apply hs
    rw [hd]
    linear_combination hh

end SelectorBranches
end PEqualNP.Outside.L_meta_33611

namespace PEqualNP.Outside.L_meta_33611.SelectorBranches

lemma mixedBranchCover {I S : Type*} [Fintype I] (E : Finset S)
    (z : S → ℝ) (v : I → ℝ) (score : I → S → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i = 1)
    (h : ∀ i, 1 ≤ ∑ s ∈ E, (1 - score i s) * z s) :
    1 ≤ ∑ s ∈ E, (1 - ∑ i, v i * score i s) * z s := by
  calc
    1 = ∑ i, v i * 1 := by simpa using hv1.symm
    _ ≤ ∑ i, v i * ∑ s ∈ E, (1 - score i s) * z s :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hv i)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      calc
        _ = (∑ i, (v i - v i * score i s)) * z s := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        _ = _ := by rw [Finset.sum_sub_distrib, hv1]

lemma halfBranchCover {S : Type*} (E : Finset S) (z f : S → ℝ)
    (hz : ∀ s ∈ E, 0 ≤ z s) (hm : 2 ≤ ∑ s ∈ E, z s) (hf : ∀ s ∈ E, f s ≤ 1/2) :
    1 ≤ ∑ s ∈ E, (1 - f s) * z s := by
  calc
    1 ≤ (1/2:ℝ) * ∑ s ∈ E, z s := by linarith
    _ = ∑ s ∈ E, (1/2:ℝ) * z s := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_right (by linarith [hf s hs]) (hz s hs)

lemma sideBranchCover {S : Type*} (E A : Finset S) (z f : S → ℝ)
    (hAE : A ⊆ E) (hz : ∀ s ∈ E, 0 ≤ z s) (hm : 1 ≤ ∑ s ∈ A, z s)
    (hf : ∀ s ∈ E, f s ≤ 1) (hA : ∀ s ∈ A, f s ≤ 0) :
    1 ≤ ∑ s ∈ E, (1 - f s) * z s := by
  calc
    1 ≤ ∑ s ∈ A, z s := hm
    _ ≤ ∑ s ∈ A, (1 - f s) * z s := Finset.sum_le_sum fun s hs => by
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ 1 - f s by linarith [hA s hs])
        (hz s (hAE hs))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hAE fun s hs _ =>
      mul_nonneg (sub_nonneg.mpr (hf s hs)) (hz s hs)

lemma allRepairsCovered {S : Type*} (E : Finset S) (z : S → ℝ) (R : Finset S → Prop)
    (hz : ∀ s ∈ E, 0 ≤ z s) (hR : ∀ T, R T → T ⊆ E)
    (hmin : ∀ T, R T → (∀ U : Finset S, U ⊂ T → ¬R U) → 1 ≤ 2 * ∑ s ∈ T, z s)
    (T : Finset S) (hT : R T) : 1 ≤ 2 * ∑ s ∈ T, z s := by
  classical
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases hm : ∀ U : Finset S, U ⊂ T → ¬R U
    · exact hmin T hT hm
    · push_neg at hm
      obtain ⟨U, hU, hr⟩ := hm
      exact (ih U hU hr).trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hU.1 fun s hs _ => hz s (hR T hT hs)) (by norm_num))

lemma exactRepairLoss {S : Type*} [DecidableEq S] (E T : Finset S) (z : S → ℝ)
    (hT : T ⊆ E) :
    ∑ s ∈ E, (1 - (if s ∈ T then (-1 : ℝ) else 1)) * z s = 2 * ∑ s ∈ T, z s := by
  have he : E.filter (fun s => s ∈ T) = T := by
    ext s
    exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨hT h, h⟩⟩
  calc
    _ = ∑ s ∈ E, if s ∈ T then 2 * z s else 0 :=
      Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
    _ = ∑ s ∈ E.filter (fun s => s ∈ T), 2 * z s := (Finset.sum_filter ..).symm
    _ = _ := by rw [he, Finset.mul_sum]

end PEqualNP.Outside.L_meta_33611.SelectorBranches

namespace PEqualNP.Outside.L_meta_33611.SelectorBranches

open scoped Classical

lemma branchCoverGeometry {k t n : ℕ} (E : Finset (Fin k → ZMod 2))
    (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (H : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (B : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (u : Fin n → ZMod 2) (f : (Fin k → ZMod 2) → (Fin t → ZMod 2) → ℝ)
    (z : (Fin k → ZMod 2) → ℝ) (hf : ∀ s b, f s b ≤ 1)
    (hz : ∀ s ∈ E, 0 ≤ z s) (htotal : 2 ≤ ∑ s ∈ E, z s)
    (hside : ∀ (a : Fin k → ZMod 2) (v : ZMod 2),
      let A := E.filter (fun s => dotProduct a s ≠ v)
      A.Nonempty → A ≠ E → 1 ≤ ∑ s ∈ A, z s)
    (hfull : (∀ s ∈ E, ∀ b, u + H s + B b ∈ K) →
      1 ≤ ∑ s ∈ E, (1 - (∑ b, f s b) / 2^t) * z s) :
    1 ≤ ∑ s ∈ E, (1 - (∑ b, if u + H s + B b ∈ K then f s b else 0) / 2^t) * z s := by
  classical
  let g (s : Fin k → ZMod 2) := (∑ b, if u + H s + B b ∈ K then f s b else 0) / 2^t
  change 1 ≤ ∑ s ∈ E, (1 - g s) * z s
  by_cases hv : ∀ b, B b ∈ K
  · by_cases hall : ∀ s ∈ E, u + H s ∈ K
    · have hs (s) (h : s ∈ E) (b) : u + H s + B b ∈ K := K.add_mem (hall s h) (hv b)
      convert hfull hs using 1
      exact Finset.sum_congr rfl fun s h => by simp [g, hs s h]
    · obtain ⟨s₁, hs₁, h₁⟩ : ∃ s ∈ E, u + H s ∉ K := by simpa using hall
      by_cases existsGood : ∃ s ∈ E, u + H s ∈ K
      · obtain ⟨s₀, hs₀, h₀⟩ := existsGood
        obtain ⟨a,v,h₀',h₁',hsep⟩ := missingSelectorSide K H B u s₀ s₁ hv h₀ h₁
        let A := E.filter (fun s => dotProduct a s ≠ v)
        have hn : A.Nonempty := ⟨s₁, Finset.mem_filter.mpr ⟨hs₁, h₁'⟩⟩
        have hp : A ≠ E := by
          intro h
          have : s₀ ∈ A := h ▸ hs₀
          exact (Finset.mem_filter.mp this).2 h₀'
        apply sideBranchCover E A z g (Finset.filter_subset ..) hz (hside a v hn hp)
        · intro s _
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^t)).mpr
          calc
            _ ≤ ∑ _b : Fin t → ZMod 2, (1 : ℝ) := Finset.sum_le_sum fun b _ => by
              split_ifs <;> first | exact hf s b | norm_num
            _ = _ := by simp [Fintype.card_fun, ZMod.card]
        · intro s hs
          simp [g, hsep s (Finset.mem_filter.mp hs).2]
      · apply halfBranchCover E z g hz htotal
        intro s hs
        have hn (b) : u + H s + B b ∉ K := by
          intro hb
          have hm := K.sub_mem hb (hv b)
          exact existsGood ⟨s, hs, by simpa using hm⟩
        simp [g, hn]
  · obtain ⟨d, hd⟩ : ∃ d, B d ∉ K := by simpa using hv
    exact halfBranchCover E z g hz htotal (fun s _ =>
      missingVerticalDirection K B d hd (u + H s) (f s) (hf s))

lemma oppositeSidesMass {k : ℕ} (E : Finset (Fin k → ZMod 2)) (z : (Fin k → ZMod 2) → ℝ)
    (s₀ s₁ : Fin k → ZMod 2) (h₀ : s₀ ∈ E) (h₁ : s₁ ∈ E) (hne : s₀ ≠ s₁)
    (side : ∀ (a : Fin k → ZMod 2) (v : ZMod 2),
      let A := E.filter (fun s => dotProduct a s ≠ v)
      A.Nonempty → A ≠ E → 1 ≤ ∑ s ∈ A, z s) :
    2 ≤ ∑ s ∈ E, z s := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, s₀ i ≠ s₁ i := by
    by_contra! hh
    exact hne (funext hh)
  let a : Fin k → ZMod 2 := Pi.single i 1
  have dot (s : Fin k → ZMod 2) : dotProduct a s = s i := by simp [a, dotProduct, Pi.single_apply]
  have hit (x y : Fin k → ZMod 2) (hx : x ∈ E) (hy : y ∈ E) (hxy : x i ≠ y i) :
      1 ≤ ∑ s ∈ E.filter (fun s => dotProduct a s ≠ x i), z s := by
    apply side a (x i)
    · exact ⟨y, Finset.mem_filter.mpr ⟨hy, by simpa only [dot] using hxy.symm⟩⟩
    · intro he
      have hm : x ∈ E.filter (fun s => dotProduct a s ≠ x i) := by rw [he]; exact hx
      exact (Finset.mem_filter.mp hm).2 (dot x)
  have ha := hit s₀ s₁ h₀ h₁ hi
  have hb := hit s₁ s₀ h₁ h₀ hi.symm
  rw [Finset.sum_filter] at ha hb
  have hpair : ∀ (x y : ZMod 2), x ≠ y → ∀ b : ZMod 2, b = x ∨ b = y := by decide
  have he : (∑ x ∈ E, ((if dotProduct a x ≠ s₀ i then z x else 0) +
      (if dotProduct a x ≠ s₁ i then z x else 0))) = ∑ x ∈ E, z x :=
    Finset.sum_congr rfl fun x _ => by
      rcases hpair _ _ hi (dotProduct a x) with h | h <;> simp [h, hi, hi.symm]
  rw [Finset.sum_add_distrib] at he
  linarith

end PEqualNP.Outside.L_meta_33611.SelectorBranches

namespace PEqualNP.Outside.L_meta_33611.SelectorBranches

open PEqualNP.Outside.L_meta_33611.Weighted

lemma maximalBranchQuadratic {k n : ℕ} (B : (Fin k → F) →ₗ[F] (Fin n → F))
    (u : Fin n → F) (P : (Fin n → F) → (Fin n → F)) (c : (Fin n → F) → Bool)
    (Q : (Fin n → F) → F)
    (hP : ∀ j, IsAff (fun y => decide (P y j = 1))) (hc : IsAff c)
    (hQ : ∃ (b : F) (l : Fin n → F) (M : Fin n → Fin n → F),
      ∀ y, Q y = b + dotProduct l y + ∑ i, ∑ j, M i j * y i * y j) :
    ∃ (d : F) (a : Fin k → F) (A : Fin k → Fin k → F), ∀ s,
      let y := u + B s
      b2f (c y) + dotProduct (P y) y + Q y =
        d + dotProduct a s + ∑ i, ∑ j, A i j * s i * s j := by
  classical
  have coord (i : Fin n) : HasDeg 1 (fun y : Fin n → F => y i) := by
    simpa only [b2f_decide] using isAff_hasDeg1 (isAff_coord i)
  obtain ⟨b,l,M,hq⟩ := hQ
  have Hq : HasDeg 2 Q := by
    rw [show Q = (fun y => b + dotProduct l y + ∑ i, ∑ j, M i j * y i * y j) from funext hq]
    apply hasDeg_add
    · simpa only [add_comm] using hasDeg_mono (hasDeg_dot l b)
    · apply hasDeg_sum
      intro i _
      apply hasDeg_sum
      intro j _
      simpa only [mul_assoc] using hasDeg_smul (M i j) (hasDeg_mul_aff (coord i) (coord j))
  have Hp : HasDeg 2 (fun y => dotProduct (P y) y) := by
    apply hasDeg_sum
    intro j _
    have hi : HasDeg 1 (fun y => P y j) := by
      simpa only [b2f_decide] using isAff_hasDeg1 (hP j)
    exact hasDeg_mul_aff hi (coord j)
  have H := hasDeg_comp_aff B u (hasDeg_add (hasDeg_add (hasDeg_mono (isAff_hasDeg1 hc)) Hp) Hq)
  obtain ⟨A,a,d,ha⟩ := quad_repr _ H
  refine ⟨d, a, fun i j => A j i, ?_⟩
  intro s
  dsimp only
  rw [ha s]
  simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
  apply congrArg (fun v => d + v)
  apply congrArg₂ (·+·)
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end PEqualNP.Outside.L_meta_33611.SelectorBranches

namespace PEqualNP.Outside.L_meta_33611.SelectorBranches

def leafQuadratic {k : ℕ} (q : (Fin k → ZMod 2) → ZMod 2) : Prop :=
  ∃ (d : ZMod 2) (a : Fin k → ZMod 2) (M : Fin k → Fin k → ZMod 2), ∀ s,
    q s = d + dotProduct a s + ∑ i, ∑ j, M i j * s i * s j

def leafRepairs {k : ℕ} (E : Finset (Fin k → ZMod 2)) (h : (Fin k → ZMod 2) → ZMod 2)
    (T : Finset (Fin k → ZMod 2)) : Prop :=
  T ⊆ E ∧ ∃ q, leafQuadratic q ∧ ∀ s ∈ E, h s = q s + (if s ∈ T then 1 else 0)

def leafSign (a : ZMod 2) : ℝ := ((if a = 1 then (-1 : ℤ) else 1) : ℤ)

theorem fullLeafRepairLoss {k t : ℕ} (E : Finset (Fin k → ZMod 2))
    (h : (Fin k → ZMod 2) → ZMod 2) (z : (Fin k → ZMod 2) → ℝ)
    (phase : (Fin k → ZMod 2) → (Fin t → ZMod 2) → ZMod 2)
    (hz : ∀ s ∈ E, 0 ≤ z s)
    (hit : ∀ T, leafRepairs E h T → (∀ U, U ⊂ T → ¬leafRepairs E h U) →
      1 ≤ 2 * ∑ s ∈ T, z s)
    (quad : ∀ b, leafQuadratic (fun s => phase s b)) :
    1 ≤ ∑ s ∈ E, (1 - (∑ b : Fin t → ZMod 2, leafSign (phase s b + h s)) / 2^t) * z s := by
  classical
  have bitRepair : ∀ p d : ZMod 2, d = p + (if p ≠ d then 1 else 0) := by decide
  have bitSign : ∀ p d : ZMod 2, p+d = 1 ↔ p ≠ d := by decide
  have single (b : Fin t → ZMod 2) :
      1 ≤ ∑ s ∈ E, (1 - leafSign (phase s b + h s)) * z s := by
    let T := E.filter (fun s => phase s b ≠ h s)
    have sub : T ⊆ E := Finset.filter_subset _ _
    have repair : leafRepairs E h T :=
      ⟨sub, fun s => phase s b, quad b, fun s hs => by simpa [T,hs] using bitRepair (phase s b) (h s)⟩
    have mass := allRepairsCovered E z (leafRepairs E h) hz (fun _ hT => hT.1) hit T repair
    rw [← exactRepairLoss E T z sub] at mass
    convert mass using 1
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hd : phase s b = h s <;> simp [leafSign, bitSign, T, hs, hd]
  let w : (Fin t → ZMod 2) → ℝ := fun _ => ((2 : ℝ)^t)⁻¹
  have wn (b : Fin t → ZMod 2) : 0 ≤ w b := by dsimp [w]; positivity
  have ws : ∑ b, w b = 1 := by
    simp [w, Fintype.card_fun, ZMod.card]
  have mixed := mixedBranchCover E z w (fun b s => leafSign (phase s b + h s)) wn ws single
  convert mixed using 1
  apply Finset.sum_congr rfl
  intro s hs
  simp only [w, ← Finset.mul_sum, div_eq_mul_inv]
  ring

end PEqualNP.Outside.L_meta_33611.SelectorBranches

namespace PEqualNP.Outside.L_meta_33611.SelectorBranches

open PEqualNP.Outside.L_meta_33611.Weighted
open scoped Classical

theorem fullSupportRepairCover {k t n : ℕ}
    (e : (Fin n → F) ≃ₗ[F] (Fin k → F) × (Fin t → F))
    (E : Finset (Fin k → F)) (h : (Fin k → F) → F) (z : (Fin k → F) → ℝ)
    (K : Submodule F (Fin n → F)) (a : Fin n → F)
    (P : (Fin n → F) → (Fin n → F)) (c : (Fin n → F) → Bool) (Q : (Fin n → F) → F)
    (support : ∀ s ∈ E, ∀ b, e.symm (s,b) + a ∈ K)
    (hP : ∀ j, IsAff (fun y => decide (P y j = 1))) (hc : IsAff c) (hQ : leafQuadratic Q)
    (hz : ∀ s ∈ E, 0 ≤ z s)
    (hit : ∀ T, leafRepairs E h T → (∀ U, U ⊂ T → ¬leafRepairs E h U) →
      1 ≤ 2 * ∑ s ∈ T, z s) :
    1 ≤ ∑ s ∈ E, (1 - (∑ b : Fin t → F, let y := e.symm (s,b)
      if y + a ∈ K then (chi (b2f (c y) + dotProduct (P y) y + (Q y + h s)) : ℝ)
      else 0) / 2^t) * z s := by
  classical
  let B := e.symm.toLinearMap.comp (LinearMap.inl F (Fin k → F) (Fin t → F))
  let u (b : Fin t → F) := e.symm (0,b)
  have hy (s : Fin k → F) (b : Fin t → F) : u b + B s = e.symm (s,b) := by
    change e.symm (0,b) + e.symm (s,0) = _
    rw [← map_add]
    simp
  let phase (s : Fin k → F) (b : Fin t → F) :=
    let y := e.symm (s,b)
    b2f (c y) + dotProduct (P y) y + Q y
  have sq (b : Fin t → F) : leafQuadratic (fun s => phase s b) := by
    obtain ⟨d,l,M,H⟩ := maximalBranchQuadratic B (u b) P c Q hP hc hQ
    refine ⟨d,l,M,?_⟩
    intro s
    simpa only [hy, phase] using H s
  have lower := fullLeafRepairLoss E h z phase hz hit sq
  convert lower using 1
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply congrArg (fun v : ℝ => 1 - v / 2^t)
  apply Finset.sum_congr rfl
  intro b _
  simp only [support s hs b, if_true, phase, ← add_assoc]
  rfl

end PEqualNP.Outside.L_meta_33611.SelectorBranches

namespace PEqualNP.Outside.L_meta_33611.SelectorBranches

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_33611.Weighted
open scoped Classical

theorem circuitCoverInequality {k t n : ℕ}
    (e : (Fin n → F) ≃ₗ[F] (Fin k → F) × (Fin t → F)) (Q : (Fin n → F) → F)
    (h : (Fin k → F) → F) (E : Finset (Fin k → F)) (o : Fin k → F) (ho : o ∈ E)
    (C : Circuit) (z : (Fin k → F) → ℝ)
    (hQ : leafQuadratic Q) (none : ¬leafRepairs E h ∅) (hz : ∀ s ∈ E, 0 ≤ z s)
    (side : ∀ (a : Fin k → F) (v : F),
      let A := E.filter (fun s => dotProduct a s ≠ v)
      A.Nonempty → A ≠ E → 1 ≤ ∑ s ∈ A, z s)
    (hit : ∀ T, leafRepairs E h T → (∀ U, U ⊂ T → ¬leafRepairs E h U) →
      1 ≤ 2 * ∑ s ∈ T, z s)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C)
    (hg : ∀ g ∈ C.gates, GOk g)
    (hcost : costG C.gates ≤ t + Module.finrank F
      (Submodule.span F ((fun s => s-o) '' (↑E : Set (Fin k → F))))) :
    1 ≤ ∑ s ∈ E, (1 - (∑ x : Fin n → F, ∑ b : Fin t → F, let y := e.symm (s,b)
      if C.eval (bitsN n x ++ bitsN n y) = decide (dotProduct x y + Q y + h s = 1)
      then (1 : ℝ) else -1) / 2^(n+t)) * z s := by
  classical
  let m := t + Module.finrank F (Submodule.span F ((fun s => s-o) '' (↑E : Set (Fin k → F))))
  obtain ⟨s', hs', hne⟩ : ∃ s ∈ E, o ≠ s := by
    by_contra! hall
    apply none
    refine ⟨Finset.empty_subset E, fun _ => h o, ⟨h o,0,0, by simp⟩, ?_⟩
    intro s hs
    simp [hall s hs]
  have hm := oppositeSidesMass E z o s' ho hs' hne side
  obtain ⟨N,r,U,a,P,c,w,hrank,haff,_,hw,hw1,hscore⟩ :=
    weightedCircuitBranches n m C hrb hg hcost
  let H := e.symm.toLinearMap.comp (LinearMap.inl F (Fin k → F) (Fin t → F))
  let B := e.symm.toLinearMap.comp (LinearMap.inr F (Fin k → F) (Fin t → F))
  have hy (s : Fin k → F) (b : Fin t → F) : H s + B b = e.symm (s,b) := by
    change e.symm (s,0) + e.symm (0,b) = _
    rw [← map_add]
    simp
  have hmem (i : Fin N) (s : Fin k → F) (b : Fin t → F) :
      a i + H s + B b = e.symm (s,b) + a i := by rw [add_assoc, hy, add_comm]
  let f (i : Fin N) (s : Fin k → F) (b : Fin t → F) : ℝ :=
    let y := e.symm (s,b)
    chi (b2f (c i y) + dotProduct (P i y) y + (Q y + h s))
  let L (i : Fin N) (s : Fin k → F) :=
    (∑ b : Fin t → F, if e.symm (s,b) + a i ∈ perp (U i) then f i s b else 0) / 2^t
  have hL (i : Fin N) : 1 ≤ ∑ s ∈ E, (1 - L i s) * z s := by
    have hf (s b) : f i s b ≤ 1 := by
      dsimp only [f, chi]
      split_ifs <;> norm_num
    have full : (∀ s ∈ E, ∀ b, a i + H s + B b ∈ perp (U i)) →
        1 ≤ ∑ s ∈ E, (1 - (∑ b, f i s b) / 2^t) * z s := by
      intro supp
      have supp' (s) (hs : s ∈ E) (b) : e.symm (s,b) + a i ∈ perp (U i) := by
        simpa only [hmem] using supp s hs b
      have bound := promiseHullDimension e E o ho (perp (U i)) (-a i)
        (fun s hs b => by simpa only [sub_neg_eq_add] using supp' s hs b)
      obtain ⟨hr,hbudget⟩ := hrank i
      have hp := finrank_perp (U i)
      change m ≤ Module.finrank F (perp (U i)) at bound
      have heq : r i = m := Nat.le_antisymm hbudget (bound.trans_eq (by omega))
      obtain ⟨hc,hP⟩ := haff i heq
      have hfull := fullSupportRepairCover e E h z (perp (U i)) (a i) (P i) (c i) Q
        supp' hP hc hQ hz hit
      convert hfull using 1
      exact Finset.sum_congr rfl fun s hs => by simp only [f, supp' s hs, ite_true]
    simpa only [L, hmem] using branchCoverGeometry E (perp (U i)) H B (a i) (f i) z
      hf hz hm side full
  have combined := mixedBranchCover E z w L (fun i => (hw i).le) hw1 hL
  convert combined using 1
  apply Finset.sum_congr rfl
  intro s _
  have eq := hscore t (fun b => e.symm (s,b)) (fun y => Q y + h s)
  have eq' : (∑ x : Fin n → F, ∑ b : Fin t → F, let y := e.symm (s,b)
      if C.eval (bitsN n x ++ bitsN n y) = decide (dotProduct x y + Q y + h s = 1)
      then (1 : ℝ) else -1) / 2^(n+t) = ∑ i, w i * L i s := by
    simpa only [L, f, add_assoc] using eq
  rw [eq']

end PEqualNP.Outside.L_meta_33611.SelectorBranches

open PEqualNP.Outside.L_meta_33611 in
theorem PEqualNP.Outside.L_meta_33611 : (∀ k t : ℕ,
  let n := k+t
  let F := ZMod 2
  let S := Fin k → F
  let D := Fin t → F
  let V := Fin n → F
  let quad := fun (j : ℕ) (f : (Fin j → F) → F) =>
    ∃ (b : F) (l : Fin j → F) (M : Fin j → Fin j → F), ∀ u,
      f u = b + dotProduct l u + ∑ i, ∑ v, M i v * u i * u v
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let fits := fun (p : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ p
  let bits := fun (u : V) => List.ofFn (fun i => decide (u i = 1))
  ∀ (e : V ≃ₗ[F] S × D) (Q : V → F) (h : S → F), quad n Q →
    let score := fun (C : Circ) (s : S) =>
      (∑ x : V, ∑ b : D, let y := e.symm (s,b)
        if C.eval (bits x ++ bits y) = decide (dotProduct x y + Q y + h s = 1)
        then (1 : ℝ) else -1) / 2^(n+t)
    ∀ (E : Finset S) (o : S), o ∈ E →
      let W := Submodule.span F (Set.image (fun s : S => s-o) (↑E : Set S))
      let p := t + Module.finrank F W
      let perfect := fun (b : ℕ) => ∃ C : Circ, fits b C ∧ ∀ s ∈ E, score C s = 1
      let repairs := fun (T : Finset S) => T ⊆ E ∧ ∃ f : S → F, quad k f ∧
        ∀ s ∈ E, h s = f s + (if s ∈ T then 1 else 0)
      let one := ∃ (a b c : S) (f : S → F), quad k f ∧ ∀ s ∈ E,
        h s = f s + dotProduct a s * dotProduct b s * dotProduct c s
      (∀ b : ℕ, perfect b → p ≤ b) ∧ (perfect p ↔ repairs ∅) ∧
      (perfect (p+1) ↔ one) ∧
      (one → ¬repairs ∅ → ∀ w : S → ℝ, (∀ s ∈ E, 0 < w s) →
        let mass := fun (z : S → ℝ) (T : Finset S) => ∑ s ∈ T, z s
        let side := fun (a : S) (v : F) => E.filter (fun s => dotProduct a s ≠ v)
        let cover := fun (z : S → ℝ) => (∀ s ∈ E, 0 ≤ z s) ∧
          (∀ (a : S) (v : F), (side a v).Nonempty → side a v ≠ E → 1 ≤ mass z (side a v)) ∧
          ∀ T : Finset S, repairs T → (∀ U : Finset S, U ⊂ T → ¬repairs U) → 1 ≤ 2 * mass z T
        let total := fun (z : S → ℝ) => ∑ s ∈ E, w s * z s
        let feasible := fun (q : ℝ) =>
          ∃ (N : ℕ) (Cs : Fin N → Circ) (v : Fin N → ℝ),
            (∀ i, fits p (Cs i) ∧ 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
            ∀ s ∈ E, 1-(∑ i, v i * score (Cs i) s) ≤ q*w s
        ∃ z : S → ℝ, cover z ∧ (∀ y : S → ℝ, cover y → total z ≤ total y) ∧
          0 < total z ∧ ∀ q : ℝ, feasible q ↔ 1 ≤ q * total z)) := by
  classical
  intro k t
  dsimp only
  intro e Q h hQ E o ho
  let perfect (b : ℕ) := ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    Upper.Fits (k+t) b C ∧ ∀ s ∈ E, Upper.Score e Q h C s = 1
  let repairs (T : Finset (Upper.V k)) := T ⊆ E ∧ ∃ f : Upper.V k → Upper.F,
    Upper.Quad f ∧ ∀ s ∈ E, h s = f s + if s ∈ T then 1 else 0
  let one := ∃ (a b c : Upper.V k) (f : Upper.V k → Upper.F), Upper.Quad f ∧ ∀ s ∈ E,
    h s = f s + dotProduct a s * dotProduct b s * dotProduct c s
  let p := Upper.budget t E o
  have scoreOne (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Upper.V k) :
      Upper.Score e Q h C s = 1 ↔ ∀ x b, let y := e.symm (s,b)
        C.eval (Upper.Input (x,y)) = Upper.GateDecode.bit (dotProduct x y + Q y + h s) :=
    normalizedScore_eq_one_iff (k+t) t _
  have normal (C : PEqualNP.CircuitLowerBounds.Circuit)
      (good : ∀ g ∈ C.gates, Upper.GateDecode.legal g)
      (perfectOn : ∀ s ∈ E, Upper.Score e Q h C s = 1) :=
    Normal.selectorNecessary e Q hQ h E o ho C good (fun s hs => (scoreOne C s).mp (perfectOn s hs))
  refine ⟨hullLowerFirstConjunct k t e Q h hQ E o ho, ?_, ?_, ?_⟩
  · change perfect p ↔ repairs ∅
    constructor
    · rintro ⟨C,hc,hs⟩
      obtain ⟨f,hf,he⟩ := (normal C hc.2.1 hs).1 hc.2.2
      exact ⟨Finset.empty_subset _, f, hf, fun s hsel => by simpa using he s hsel⟩
    · rintro ⟨_, f, hf, he⟩
      obtain ⟨C,hc,hv⟩ := Upper.realizeQuad e Q hQ f hf E o
      refine ⟨C,hc,fun s hs => (scoreOne C s).mpr ?_⟩
      intro x b
      have hs' : h s = f s := by simpa using he s hs
      simpa only [hs'] using hv s hs x b
  · change perfect (p+1) ↔ one
    constructor
    · rintro ⟨C,hc,hs⟩
      exact (normal C hc.2.1 hs).2 hc.2.2
    · intro h1
      obtain ⟨C,hc,hv⟩ := Upper.realizeOne e Q hQ h E o h1
      exact ⟨C,hc,fun s hs => (scoreOne C s).mpr (hv s hs)⟩
  · intro hone hnone w hw
    apply SelectorLP.exactOptimization e Q hQ h E o ho hnone w hw
    · intro a v hn hp
      obtain ⟨C,bk,gd,cost,ev⟩ := CutAttainment.attainedCut e Q h hQ E o a v hone hn hp
      exact ⟨C,⟨bk,gd,cost⟩,ev⟩
    · intro C hc z hz
      exact SelectorBranches.circuitCoverInequality e Q h E o ho C z hQ hnone hz.1 hz.2.1 hz.2.2
        hc.1 hc.2.1 hc.2.2
