import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_27811_aux

abbrev F2 := ZMod 2

abbrev Vec (k : ℕ) := Fin k → F2

def dot {k : ℕ} (x y : Vec k) : F2 := ∑ i : Fin k, x i * y i

lemma card_vec (k : ℕ) : Fintype.card (Vec k) = 2 ^ k := by
  simp [Vec]

lemma dot_add_left {k : ℕ} (x y z : Vec k) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {k : ℕ} (x y z : Vec k) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul_left {k : ℕ} (c : F2) (x y : Vec k) : dot (c • x) y = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

lemma dot_smul_right {k : ℕ} (c : F2) (x y : Vec k) : dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma dot_zero_left {k : ℕ} (y : Vec k) : dot 0 y = 0 := by
  simp [dot]

lemma dot_zero_right {k : ℕ} (x : Vec k) : dot x 0 = 0 := by
  simp [dot]

lemma dot_comm {k : ℕ} (x y : Vec k) : dot x y = dot y x := by
  simp only [dot]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma dot_sum_right {k : ℕ} {α : Type*} (s : Finset α) (x : Vec k) (f : α → Vec k) :
    dot x (∑ j ∈ s, f j) = ∑ j ∈ s, dot x (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, dot_add_right, ih, Finset.sum_insert ha]

def orth {k : ℕ} (S : Submodule F2 (Vec k)) : Submodule F2 (Vec k) :=
  { carrier := {w | ∀ x ∈ S, dot x w = 0}, zero_mem' := fun x _ => dot_zero_right x,
    smul_mem' := fun c _ ha x hx => by rw [dot_smul_right, ha x hx, mul_zero], add_mem' := fun ha hb x hx => by rw [dot_add_right, ha x hx, hb x hx, add_zero] }

lemma le_orth_orth {k : ℕ} (S : Submodule F2 (Vec k)) : S ≤ orth (orth S) := by
  intro x hx w hw
  rw [dot_comm]
  exact hw x hx

lemma finrank_orth_add {k : ℕ} (S : Submodule F2 (Vec k)) :
    Module.finrank F2 (orth S) + Module.finrank F2 S = k := by
  let b := Module.finBasis F2 S
  let d := Module.finrank F2 S
  let ev : Vec k →ₗ[F2] (Fin d → F2) :=
    { toFun := fun w i => dot (b i).1 w
      map_add' := fun w1 w2 => by funext i; exact dot_add_right _ w1 w2
      map_smul' := fun c w => by funext i; exact dot_smul_right c _ w }
  have hker : LinearMap.ker ev = orth S := by
    ext w
    simp only [LinearMap.mem_ker, orth, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    constructor
    · intro hw x hx
      have hx' : (⟨x, hx⟩ : S) ∈ Submodule.span F2 (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      let f : S →ₗ[F2] F2 :=
        { toFun := fun u => dot u.1 w
          map_add' := fun u1 u2 => dot_add_left u1.1 u2.1 w
          map_smul' := fun c u => dot_smul_left c u.1 w }
      have hle : Submodule.span F2 (Set.range b) ≤ LinearMap.ker f := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact congrFun hw i
      exact hle hx'
    · intro hw
      funext i
      exact hw (b i).1 (b i).2
  have hsurj : LinearMap.range ev = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨T, hST⟩ := Submodule.exists_isCompl S
    let g : S →ₗ[F2] F2 := b.constr F2 y
    let ψ : Vec k →ₗ[F2] F2 := g.comp (Submodule.projectionOnto S T hST)
    let w : Vec k := fun r => ψ (Pi.single r 1)
    refine ⟨w, ?_⟩
    funext i
    have hdot_psi : ∀ v : Vec k, dot v w = ψ v := by
      intro v
      have hv : v = ∑ r : Fin k, v r • Pi.single r (1 : F2) := by
        funext j
        simp [Pi.single_apply]
      conv_rhs => rw [hv]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dot, w]
    change dot (b i).1 w = y i
    rw [hdot_psi (b i).1]
    change g (Submodule.projectionOnto S T hST (b i).1) = y i
    rw [Submodule.projectionOnto_apply_left hST (b i)]
    exact Module.Basis.constr_basis b F2 y i
  have hrn := ev.finrank_range_add_finrank_ker
  rw [hsurj, finrank_top, hker, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fin] at hrn
  omega

lemma orth_orth {k : ℕ} (S : Submodule F2 (Vec k)) : orth (orth S) = S := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orth_orth S)
  have h1 := finrank_orth_add S
  have h2 := finrank_orth_add (orth S)
  omega

def sgn (z : F2) : ℤ := if z = 0 then 1 else -1

lemma sgn_sq (z : F2) : sgn z * sgn z = 1 := by
  unfold sgn
  by_cases h : z = 0 <;> simp [h]

lemma sgn_add (x y : F2) : sgn (x + y) = sgn x * sgn y := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hx_cases : x = 0 ∨ x = 1 := by
    by_cases h0 : x.val = 0
    · left; exact ZMod.val_injective 2 (by simpa using h0)
    · right; have h1 : (1 : F2).val = 1 := rfl; exact ZMod.val_injective 2 (by omega)
  have hy_cases : y = 0 ∨ y = 1 := by
    by_cases h0 : y.val = 0
    · left; exact ZMod.val_injective 2 (by simpa using h0)
    · right; have h1 : (1 : F2).val = 1 := rfl; exact ZMod.val_injective 2 (by omega)
  rcases hx_cases with rfl | rfl <;> rcases hy_cases with rfl | rfl <;> decide

lemma sgn_sum {α : Type*} (s : Finset α) (f : α → F2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

lemma sgn_eq_iff_hit (x y : F2) :
    (if x = y then (1 : ℤ) else -1) = sgn x * sgn y := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hx_cases : x = 0 ∨ x = 1 := by
    by_cases h0 : x.val = 0
    · left; exact ZMod.val_injective 2 (by simpa using h0)
    · right; have h1 : (1 : F2).val = 1 := rfl; exact ZMod.val_injective 2 (by omega)
  have hy_cases : y = 0 ∨ y = 1 := by
    by_cases h0 : y.val = 0
    · left; exact ZMod.val_injective 2 (by simpa using h0)
    · right; have h1 : (1 : F2).val = 1 := rfl; exact ZMod.val_injective 2 (by omega)
  rcases hx_cases with rfl | rfl <;> rcases hy_cases with rfl | rfl <;> decide

lemma f2_add_self (x : F2) : x + x = 0 := by
  have hx := ZMod.val_lt x
  by_cases h0 : x.val = 0
  · have : x = 0 := ZMod.val_injective 2 (by simpa using h0)
    subst this; decide
  · have h1 : (1 : F2).val = 1 := rfl
    have : x = 1 := ZMod.val_injective 2 (by omega)
    subst this; decide

lemma vec_add_self {k : ℕ} (x : Vec k) : x + x = 0 := by
  funext i; exact f2_add_self (x i)

lemma f2_ne_zero_eq_one (x : F2) (hx : x ≠ 0) : x = 1 := by
  have hlt := ZMod.val_lt x
  have hne : x.val ≠ 0 := fun h => hx (ZMod.val_injective 2 (by simpa using h))
  have h1 : (1 : F2).val = 1 := rfl
  exact ZMod.val_injective 2 (by omega)

lemma sum_sgn_coset_eq_zero {k : ℕ} (K : Submodule F2 (Vec k)) [DecidablePred (· ∈ K)]
    (x0 w : Vec k) (hw : w ∉ orth K) :
    ∑ z ∈ (Finset.univ.filter (fun z : Vec k => z ∈ K)), sgn (dot (x0 + z) w) = 0 := by
  have hex : ∃ z0 ∈ K, dot z0 w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw hall
  rcases hex with ⟨z0, hz0K, hdz0⟩
  have hdz1 : dot z0 w = 1 := f2_ne_zero_eq_one _ hdz0
  let FK : Finset (Vec k) := Finset.univ.filter (fun z : Vec k => z ∈ K)
  have hsum_neg : ∑ z ∈ FK, sgn (dot (x0 + z) w) = -(∑ z ∈ FK, sgn (dot (x0 + z) w)) := by
    have hbij : ∑ z ∈ FK, sgn (dot (x0 + (z + z0)) w) = ∑ z ∈ FK, sgn (dot (x0 + z) w) := by
      refine Finset.sum_nbij (fun z => z + z0) ?_ ?_ ?_ ?_
      · intro z hz
        simp only [FK, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact K.add_mem hz hz0K
      · intro z1 _ z2 _ heq
        have := congrArg (· + z0) heq
        simpa [add_assoc, vec_add_self] using this
      · intro z hz
        refine ⟨z + z0, ?_, by simp [add_assoc, vec_add_self]⟩
        simp only [Finset.mem_coe, FK, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact K.add_mem hz hz0K
      · intro z _; rfl
    conv_lhs => rw [← hbij]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    have hsgn1 : sgn (1 : F2) = -1 := by decide
    rw [← add_assoc, dot_add_left, hdz1, sgn_add, hsgn1, mul_neg_one]
  linarith

lemma sum_filter_sgn_eq_two_mul_sub {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ x : α, if P x then (1 : ℤ) else -1) =
    2 * ((Finset.univ.filter P).card : ℤ) - (Fintype.card α : ℤ) := by
  have hsplit : ∑ x : α, (if P x then (1 : ℤ) else -1) =
      ∑ x ∈ Finset.univ.filter P, (1 : ℤ) + ∑ x ∈ Finset.univ.filter (fun x => ¬P x), (-1 : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun x => if P x then (1 : ℤ) else -1)]
    congr 1
    · apply Finset.sum_congr rfl; intro x hx; simp [(Finset.mem_filter.mp hx).2]
    · apply Finset.sum_congr rfl; intro x hx; simp [(Finset.mem_filter.mp hx).2]
  rw [hsplit, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg_one]
  have hcard : (Finset.univ.filter P).card + (Finset.univ.filter (fun x => ¬P x)).card =
      Fintype.card α := by
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset α)) P (fun _ => (1 : ℕ))
    simpa using this
  have hcardZ : ((Finset.univ.filter P).card : ℤ) + ((Finset.univ.filter (fun x => ¬P x)).card : ℤ) =
      (Fintype.card α : ℤ) := by exact_mod_cast hcard
  linarith

lemma chebyshev_pow_le {α : Type*} (s : Finset α) (f : α → ℤ) (hf : ∀ x ∈ s, 0 ≤ f x) (n : ℕ) :
    (∑ x ∈ s, f x) * (∑ x ∈ s, f x ^ n) ≤ (s.card : ℤ) * (∑ x ∈ s, f x ^ (n + 1)) := by
  have hnn : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) * (f x ^ n - f y ^ n) := by
    apply Finset.sum_nonneg; intro x hx
    apply Finset.sum_nonneg; intro y hy
    rcases le_total (f x) (f y) with hxy | hyx
    · have hp : f x ^ n ≤ f y ^ n := pow_le_pow_left₀ (hf x hx) hxy n
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy) (sub_nonpos.mpr hp)
    · have hp : f y ^ n ≤ f x ^ n := pow_le_pow_left₀ (hf y hy) hyx n
      exact mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hp)
  have hexp : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) * (f x ^ n - f y ^ n) =
      2 * ((s.card : ℤ) * (∑ x ∈ s, f x ^ (n + 1)) - (∑ x ∈ s, f x) * (∑ x ∈ s, f x ^ n)) := by
    have hterm : ∀ x y : α, (f x - f y) * (f x ^ n - f y ^ n) =
        f x ^ (n + 1) - f x * f y ^ n - f y * f x ^ n + f y ^ (n + 1) := by
      intro x y; rw [pow_succ', pow_succ']; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Finset.mul_sum]
    ring
  linarith

lemma pow_sum_le_card_pow_mul_sum_pow {α : Type*} (s : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ s, 0 ≤ f x) : ∀ n : ℕ, 1 ≤ n →
    (∑ x ∈ s, f x) ^ n ≤ (s.card : ℤ) ^ (n - 1) * (∑ x ∈ s, f x ^ n) := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ t =>
      have hih := ih (by omega)
      have hsf : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg hf
      have hsc : 0 ≤ (s.card : ℤ) ^ t := by positivity
      have hcheb := chebyshev_pow_le s f hf (t + 1)
      have hstep : (∑ x ∈ s, f x) ^ (t + 2) = (∑ x ∈ s, f x) * (∑ x ∈ s, f x) ^ (t + 1) := by
        rw [pow_succ']
      rw [hstep]
      calc (∑ x ∈ s, f x) * (∑ x ∈ s, f x) ^ (t + 1)
          ≤ (∑ x ∈ s, f x) * ((s.card : ℤ) ^ t * (∑ x ∈ s, f x ^ (t + 1))) :=
            mul_le_mul_of_nonneg_left hih hsf
        _ = (s.card : ℤ) ^ t * ((∑ x ∈ s, f x) * (∑ x ∈ s, f x ^ (t + 1))) := by ring
        _ ≤ (s.card : ℤ) ^ t * ((s.card : ℤ) * (∑ x ∈ s, f x ^ (t + 2))) :=
            mul_le_mul_of_nonneg_left hcheb hsc
        _ = (s.card : ℤ) ^ (t + 1) * (∑ x ∈ s, f x ^ (t + 2)) := by rw [pow_succ']; ring

lemma short_relation_pivot {k m a r : ℕ} (v : Fin m → Vec k)
    (P : Submodule F2 (Vec k)) (hP : Module.finrank F2 P ≤ a)
    (hindep : ∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a + 1) * r →
      (∑ j ∈ S, v j) ≠ 0) :
    ∃ D : Finset (Fin m), D.card ≤ a ∧
      ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ r → Disjoint T D →
        (∑ j ∈ T, v j) ∉ P := by
  classical
  by_contra hno
  push Not at hno
  have hstep : ∀ D : Finset (Fin m), D.card ≤ a →
      ∃ T : Finset (Fin m), T.Nonempty ∧ T.card ≤ r ∧ Disjoint T D ∧ (∑ j ∈ T, v j) ∈ P := by
    intro D hD
    obtain ⟨T, hTne, hTle, hTdisj, hTin⟩ := hno D hD
    exact ⟨T, hTne, hTle, hTdisj, hTin⟩
  have hbuild : ∀ s : ℕ, s ≤ a + 1 →
      ∃ (d : Fin s → Fin m) (T : Fin s → Finset (Fin m)),
        (∀ i : Fin s, d i ∈ T i) ∧
        (∀ i : Fin s, (T i).card ≤ r) ∧
        (∀ i : Fin s, (∑ j ∈ T i, v j) ∈ P) ∧
        (∀ i j : Fin s, j < i → d j ∉ T i) := by
    intro s hs
    induction s with
    | zero =>
      exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ t ih =>
      obtain ⟨d, T, hd, hTle, hTP, hdisj⟩ := ih (by omega)
      let D : Finset (Fin m) := Finset.univ.image d
      have hDcard : D.card ≤ a := (Finset.card_image_le).trans (by simp; omega)
      obtain ⟨Tnew, hTne, hTnew_le, hTnew_disj, hTnew_P⟩ := hstep D hDcard
      obtain ⟨dnew, hdnew⟩ := hTne
      refine ⟨Fin.snoc d dnew, Fin.snoc T Tnew, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last, hdnew]
        · intro j; simp [Fin.snoc_castSucc, hd j]
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last, hTnew_le]
        · intro j; simp [Fin.snoc_castSucc, hTle j]
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last, hTnew_P]
        · intro j; simp [Fin.snoc_castSucc, hTP j]
      · intro i j hji
        refine Fin.lastCases ?_ ?_ i hji
        · intro hjlast
          have hjt : j.1 < t := hjlast
          let j' : Fin t := ⟨j.1, hjt⟩
          have hjeq : j = j'.castSucc := by ext; rfl
          rw [hjeq, Fin.snoc_last, Fin.snoc_castSucc]
          have hmemD : d j' ∈ D := Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩
          exact Finset.disjoint_right.mp hTnew_disj hmemD
        · intro i' hji'
          have hjt : j.1 < t := lt_trans hji' i'.2
          let j' : Fin t := ⟨j.1, hjt⟩
          have hjeq : j = j'.castSucc := by ext; rfl
          rw [hjeq, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hdisj i' j' hji'
  obtain ⟨d, T, hd, hTle, hTP, hdisj⟩ := hbuild (a + 1) le_rfl
  let w : Fin (a + 1) → P := fun i => ⟨∑ j ∈ T i, v j, hTP i⟩
  let φ : (Fin (a + 1) → F2) →ₗ[F2] P :=
    { toFun := fun α => ∑ i : Fin (a + 1), α i • w i
      map_add' := fun α1 α2 => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c α => by simp [Finset.smul_sum, mul_smul] }
  have hker_nontriv : ∃ α : Fin (a + 1) → F2, α ≠ 0 ∧ φ α = 0 := by
    have hrn := φ.finrank_range_add_finrank_ker
    have hdom : Module.finrank F2 (Fin (a + 1) → F2) = a + 1 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hrg : Module.finrank F2 (LinearMap.range φ) ≤ a :=
      (Submodule.finrank_le _).trans hP
    have hker_pos : 0 < Module.finrank F2 (LinearMap.ker φ) := by omega
    have hne_bot : LinearMap.ker φ ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hker_pos
      omega
    obtain ⟨α, hαker, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    exact ⟨α, hα0, hαker⟩
  obtain ⟨α, hα0, hφα⟩ := hker_nontriv
  let I : Finset (Fin (a + 1)) := Finset.univ.filter (fun i => α i ≠ 0)
  have hIne : I.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hα0
    funext i
    by_contra hi
    have : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hemp] at this
    exact Finset.notMem_empty i this
  have hsum_I : ∑ i ∈ I, ∑ j ∈ T i, v j = 0 := by
    have hval : (φ α).1 = 0 := congrArg Subtype.val hφα
    have hφ_eq : (φ α).1 = ∑ i : Fin (a + 1), α i • ∑ j ∈ T i, v j := by
      simp [φ, w]
    rw [hφ_eq] at hval
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => α i ≠ 0)] at hval
    have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬α i ≠ 0), α i • ∑ j ∈ T i, v j = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have hαi : α i = 0 := by simpa using (Finset.mem_filter.mp hi).2
      simp [hαi]
    rw [hzero, add_zero] at hval
    have hone : ∑ i ∈ I, α i • ∑ j ∈ T i, v j = ∑ i ∈ I, ∑ j ∈ T i, v j := by
      apply Finset.sum_congr rfl; intro i hi
      have hαi : α i = 1 := f2_ne_zero_eq_one _ (Finset.mem_filter.mp hi).2
      simp [hαi]
    rw [← hone]
    exact hval
  let S : Finset (Fin m) :=
    Finset.univ.filter (fun x : Fin m => Odd (I.filter (fun i => x ∈ T i)).card)
  have hSne : S.Nonempty := by
    let i0 := I.min' hIne
    have hi0I : i0 ∈ I := Finset.min'_mem I hIne
    refine ⟨d i0, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfilt : I.filter (fun i => d i0 ∈ T i) = {i0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hiI, hdi⟩
        by_contra hne
        have hlt : i0 < i := lt_of_le_of_ne (Finset.min'_le I i hiI) (Ne.symm hne)
        exact hdisj i i0 hlt hdi
      · rintro rfl
        exact ⟨hi0I, hd i0⟩
    rw [hfilt, Finset.card_singleton]
    exact odd_one
  have hScard : S.card ≤ (a + 1) * r := by
    have hsub : S ⊆ I.biUnion T := by
      intro x hx
      have hodd : Odd (I.filter (fun i => x ∈ T i)).card := (Finset.mem_filter.mp hx).2
      have hpos : 0 < (I.filter (fun i => x ∈ T i)).card := by
        rcases hodd with ⟨t, ht⟩; omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact Finset.mem_biUnion.mpr ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    calc S.card ≤ (I.biUnion T).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ I, (T i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I, r := Finset.sum_le_sum (fun i _ => hTle i)
      _ = I.card * r := by simp
      _ ≤ (a + 1) * r := Nat.mul_le_mul_right r ((Finset.card_le_univ I).trans (by simp))
  have hSsum : ∑ x ∈ S, v x = 0 := by
    have hsw : ∑ i ∈ I, ∑ x ∈ T i, v x =
        ∑ x : Fin m, ((I.filter (fun i => x ∈ T i)).card : F2) • v x := by
      calc ∑ i ∈ I, ∑ x ∈ T i, v x
          = ∑ i ∈ I, ∑ x : Fin m, if x ∈ T i then v x else 0 := by
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.sum_filter]
            congr 1; ext x; simp
        _ = ∑ x : Fin m, ∑ i ∈ I, if x ∈ T i then v x else 0 := Finset.sum_comm
        _ = ∑ x : Fin m, ((I.filter (fun i => x ∈ T i)).card : F2) • v x := by
            apply Finset.sum_congr rfl; intro x _
            rw [← Finset.sum_filter, Finset.sum_const]
            funext r; simp
    have hcast : ∀ n : ℕ, (n : F2) = if Odd n then 1 else 0 := by
      intro n
      have hmod : (n : F2).val = n % 2 := ZMod.val_natCast 2 n
      by_cases hodd : Odd n
      · simp only [hodd, ↓reduceIte]
        have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
        exact ZMod.val_injective 2 (by rw [hmod, h1]; rfl)
      · simp only [hodd, ↓reduceIte]
        have h0 : n % 2 = 0 := by
          have := Nat.mod_two_eq_zero_or_one n
          rcases this with h | h
          · exact h
          · exact absurd (Nat.odd_iff.mpr h) hodd
        exact ZMod.val_injective 2 (by rw [hmod, h0]; rfl)
    rw [hsw] at hsum_I
    rw [← hsum_I]
    symm
    calc ∑ x : Fin m, ((I.filter (fun i => x ∈ T i)).card : F2) • v x
        = ∑ x : Fin m, if Odd (I.filter (fun i => x ∈ T i)).card then v x else 0 := by
          apply Finset.sum_congr rfl; intro x _
          rw [hcast]
          by_cases ho : Odd (I.filter (fun i => x ∈ T i)).card <;> simp [ho]
      _ = ∑ x ∈ S, v x := by rw [← Finset.sum_filter]
  exact hindep S hSne hScard hSsum

def evenTuples {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (R : Finset α) :
    Finset (Fin (2 * n) → α) :=
  Finset.univ.filter (fun f => (∀ i, f i ∈ R) ∧
    ∀ j ∈ R, Even (Finset.univ.filter (fun i => f i = j)).card)

lemma card_evenTuples_le {α : Type*} [Fintype α] [DecidableEq α] (R : Finset α) :
    ∀ n : ℕ, (evenTuples n R).card ≤ (2 * n) ^ n * R.card ^ n := by
  have hstrong : ∀ n : ℕ, (evenTuples n R).card ≤ (∏ t ∈ Finset.range n, (2 * t + 1)) * R.card ^ n := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero, mul_one]
      exact (Finset.card_le_univ _).trans (by simp)
    | succ m ih =>
      let del : Fin (2 * m + 1) → Fin (2 * m) → Fin (2 * (m + 1)) := fun p i =>
        if i.1 < p.1 then ⟨i.1 + 1, by omega⟩ else ⟨i.1 + 2, by omega⟩
      have hdel_inj : ∀ p : Fin (2 * m + 1), Function.Injective (del p) := by
        intro p i1 i2 heq
        simp only [del] at heq
        by_cases h1 : i1.1 < p.1 <;> by_cases h2 : i2.1 < p.1 <;> simp [h1, h2] at heq
        · ext; omega
        · omega
        · omega
        · ext; omega
      have hdel_ne0 : ∀ p i, del p i ≠ 0 := by
        intro p i h0
        simp only [del] at h0
        split_ifs at h0 <;> simp [Fin.ext_iff] at h0
      have hdel_nep : ∀ p i, del p i ≠ p.succ := by
        intro p i hp
        simp only [del] at hp
        split_ifs at hp with h <;> simp [Fin.ext_iff] at hp <;> omega
      have hdel_surj : ∀ (p : Fin (2 * m + 1)) (q : Fin (2 * (m + 1))),
          q ≠ 0 → q ≠ p.succ → ∃ i : Fin (2 * m), del p i = q := by
        intro p q hq0 hqp
        have hq0' : q.1 ≠ 0 := fun h => hq0 (Fin.ext h)
        have hqp' : q.1 ≠ p.1 + 1 := fun h => hqp (Fin.ext h)
        by_cases hlt : q.1 < p.1 + 1
        · refine ⟨⟨q.1 - 1, by omega⟩, ?_⟩
          simp only [del]
          have h1 : q.1 - 1 < p.1 := by omega
          simp only [h1, ↓reduceIte]
          ext; simp; omega
        · refine ⟨⟨q.1 - 2, by omega⟩, ?_⟩
          simp only [del]
          have h1 : ¬ (q.1 - 2 < p.1) := by omega
          simp only [h1, ↓reduceIte]
          ext; simp; omega
      have hex_p : ∀ f ∈ evenTuples (m + 1) R, ∃ p : Fin (2 * m + 1), f p.succ = f 0 := by
        intro f hf
        have hmem0 : f 0 ∈ R := (Finset.mem_filter.mp hf).2.1 0
        have heven0 : Even (Finset.univ.filter (fun i : Fin (2 * (m + 1)) => f i = f 0)).card :=
          (Finset.mem_filter.mp hf).2.2 (f 0) hmem0
        have h0in : (0 : Fin (2 * (m + 1))) ∈ Finset.univ.filter (fun i => f i = f 0) := by simp
        have hge1 : 1 ≤ (Finset.univ.filter (fun i => f i = f 0)).card :=
          Finset.card_pos.mpr ⟨0, h0in⟩
        have hge2 : 2 ≤ (Finset.univ.filter (fun i => f i = f 0)).card := by
          rcases heven0 with ⟨t, ht⟩; omega
        have herase_pos : 0 < ((Finset.univ.filter (fun i => f i = f 0)).erase 0).card := by
          rw [Finset.card_erase_of_mem h0in]; omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp herase_pos
        have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
        have hqeq : f q = f 0 := (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).2
        have hqpos : 0 < q.1 := Nat.pos_of_ne_zero (fun h => hq0 (Fin.ext h))
        refine ⟨⟨q.1 - 1, by omega⟩, ?_⟩
        have : (⟨q.1 - 1, by omega⟩ : Fin (2 * m + 1)).succ = q := by ext; simp; omega
        rw [this]; exact hqeq
      let chooseP : (Fin (2 * (m + 1)) → α) → Fin (2 * m + 1) := fun f =>
        if h : ∃ p : Fin (2 * m + 1), f p.succ = f 0 then Classical.choose h else ⟨0, by omega⟩
      let encF : (Fin (2 * (m + 1)) → α) → α × Fin (2 * m + 1) × (Fin (2 * m) → α) :=
        fun f => (f 0, chooseP f, fun i => f (del (chooseP f) i))
      have hcard_le : (evenTuples (m + 1) R).card ≤
          (R ×ˢ ((Finset.univ : Finset (Fin (2 * m + 1))) ×ˢ evenTuples m R)).card := by
        apply Finset.card_le_card_of_injOn encF
        · intro f hf
          have hp_ex := hex_p f hf
          have hp_eq : f (chooseP f).succ = f 0 := by
            simp only [chooseP, hp_ex, ↓reduceDIte]
            exact Classical.choose_spec hp_ex
          simp only [Finset.mem_coe, encF, Finset.mem_product, Finset.mem_univ, true_and]
          refine ⟨(Finset.mem_filter.mp hf).2.1 0, ?_⟩
          simp only [evenTuples, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun i => (Finset.mem_filter.mp hf).2.1 _, fun j hjR => ?_⟩
          have hfev := (Finset.mem_filter.mp hf).2.2 j hjR
          let p := chooseP f
          let Sfull := Finset.univ.filter (fun q : Fin (2 * (m + 1)) => f q = j)
          let Ssub := Finset.univ.filter (fun i : Fin (2 * m) => f (del p i) = j)
          have himg : Ssub.image (del p) = (Sfull.erase 0).erase p.succ := by
            ext q
            simp only [Finset.mem_image, Ssub, Sfull, Finset.mem_erase, Finset.mem_filter,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨i, hi, rfl⟩
              exact ⟨hdel_nep p i, hdel_ne0 p i, hi⟩
            · rintro ⟨hqp, hq0, hfq⟩
              obtain ⟨i, hi⟩ := hdel_surj p q hq0 hqp
              exact ⟨i, by rw [hi]; exact hfq, hi⟩
          have hcard_sub : Ssub.card = ((Sfull.erase 0).erase p.succ).card := by
            rw [← himg, Finset.card_image_of_injective _ (hdel_inj p)]
          change Even Ssub.card
          rw [hcard_sub]
          have hp_eq' : f p.succ = f 0 := hp_eq
          by_cases hj0 : f 0 = j
          · have h0in : (0 : Fin (2 * (m + 1))) ∈ Sfull := by simp [Sfull, hj0]
            have hpin : p.succ ∈ Sfull.erase 0 := Finset.mem_erase.mpr
              ⟨Fin.succ_ne_zero p, by simp [Sfull, hp_eq', hj0]⟩
            rw [Finset.card_erase_of_mem hpin, Finset.card_erase_of_mem h0in]
            rcases hfev with ⟨t, ht⟩
            change Sfull.card = t + t at ht
            have hge2 : 2 ≤ Sfull.card := by
              have h1 : 1 ≤ (Sfull.erase 0).card := Finset.card_pos.mpr ⟨p.succ, hpin⟩
              rw [Finset.card_erase_of_mem h0in] at h1; omega
            exact ⟨t - 1, by omega⟩
          · have h0out : (0 : Fin (2 * (m + 1))) ∉ Sfull := by simp [Sfull, hj0]
            have hpout : p.succ ∉ Sfull.erase 0 := by
              simp [Sfull, hp_eq', hj0]
            rw [Finset.erase_eq_of_notMem hpout, Finset.erase_eq_of_notMem h0out]
            exact hfev
        · intro f1 hf1 f2 hf2 heq
          have hp1 : f1 (chooseP f1).succ = f1 0 := by
            have h := hex_p f1 hf1; simp only [chooseP, h, ↓reduceDIte]; exact Classical.choose_spec h
          have hp2 : f2 (chooseP f2).succ = f2 0 := by
            have h := hex_p f2 hf2; simp only [chooseP, h, ↓reduceDIte]; exact Classical.choose_spec h
          have hf0 : f1 0 = f2 0 := congrArg Prod.fst heq
          have hpeq : chooseP f1 = chooseP f2 := congrArg (fun x => x.2.1) heq
          have hrest : (fun i => f1 (del (chooseP f1) i)) = (fun i => f2 (del (chooseP f2) i)) :=
            congrArg (fun x => x.2.2) heq
          funext q
          by_cases hq0 : q = 0
          · subst hq0; exact hf0
          · by_cases hqp : q = (chooseP f1).succ
            · subst hqp; rw [hp1, hf0, hpeq, hp2]
            · obtain ⟨i, hi⟩ := hdel_surj (chooseP f1) q hq0 hqp
              rw [← hi]
              have := congrFun hrest i
              rwa [← hpeq] at this
      calc (evenTuples (m + 1) R).card
          ≤ (R ×ˢ (Finset.univ ×ˢ evenTuples m R)).card := hcard_le
        _ = R.card * ((2 * m + 1) * (evenTuples m R).card) := by
            simp [Finset.card_product]
        _ ≤ R.card * ((2 * m + 1) * ((∏ t ∈ Finset.range m, (2 * t + 1)) * R.card ^ m)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)
        _ = (∏ t ∈ Finset.range (m + 1), (2 * t + 1)) * R.card ^ (m + 1) := by
            rw [Finset.prod_range_succ, pow_succ]; ring
  intro n
  refine (hstrong n).trans (Nat.mul_le_mul_right _ ?_)
  have hle : ∀ t ∈ Finset.range n, 2 * t + 1 ≤ 2 * n := by
    intro t ht
    have := Finset.mem_range.mp ht
    omega
  calc ∏ t ∈ Finset.range n, (2 * t + 1)
      ≤ ∏ _t ∈ Finset.range n, (2 * n) := Finset.prod_le_prod hle
    _ = (2 * n) ^ n := by simp

lemma fiber_moment_bound {k m b : ℕ} (hb : 1 ≤ b)
    (v : Fin m → Vec k) (c : Fin m → F2)
    (K : Submodule F2 (Vec k)) [DecidablePred (· ∈ K)] (x0 : Vec k)
    (R : Finset (Fin m))
    (hR_orth : ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ 2 * b → T ⊆ R →
      (∑ j ∈ T, v j) ∉ orth K)
    (σ : Fin m → F2) :
    let FK : Finset (Vec k) := Finset.univ.filter (fun z : Vec k => z ∈ K)
    (∑ z ∈ FK, (∑ j ∈ R, sgn (σ j) * sgn (dot (x0 + z) (v j) + c j)) ^ (2 * b)) ≤
      (FK.card : ℤ) * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b) := by
  classical
  dsimp only
  let FK : Finset (Vec k) := Finset.univ.filter (fun z : Vec k => z ∈ K)
  let g : Vec k → Fin m → ℤ := fun z j => sgn (σ j) * sgn (dot (x0 + z) (v j) + c j)
  have hexp : ∀ z : Vec k, (∑ j ∈ R, sgn (σ j) * sgn (dot (x0 + z) (v j) + c j)) ^ (2 * b) =
      ∑ f ∈ (Fintype.piFinset (fun _ : Fin (2 * b) => R)), ∏ i : Fin (2 * b), g z (f i) := by
    intro z
    rw [Finset.sum_pow']
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hterm : ∀ f ∈ Fintype.piFinset (fun _ : Fin (2 * b) => R),
      ∑ z ∈ FK, ∏ i : Fin (2 * b), g z (f i) =
      if f ∈ evenTuples b R then (FK.card : ℤ) else 0 := by
    intro f hf
    have hfR : ∀ i : Fin (2 * b), f i ∈ R := fun i => Fintype.mem_piFinset.mp hf i
    let T : Finset (Fin m) := R.filter (fun j => Odd (Finset.univ.filter (fun i => f i = j)).card)
    have hprod_eq : ∀ z : Vec k, (∏ i : Fin (2 * b), g z (f i)) =
        (∏ j ∈ T, sgn (σ j) * sgn (c j)) * sgn (dot (x0 + z) (∑ j ∈ T, v j)) := by
      intro z
      have hgroup : ∏ i : Fin (2 * b), g z (f i) =
          ∏ j ∈ R, (g z j) ^ (Finset.univ.filter (fun i : Fin (2 * b) => f i = j)).card := by
        rw [← Finset.prod_fiberwise_of_maps_to (g := f) (fun i _ => hfR i)]
        apply Finset.prod_congr rfl; intro j _
        have hconst : ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * b) => f i = j), g z (f i) =
            ∏ _i ∈ Finset.univ.filter (fun i : Fin (2 * b) => f i = j), g z j :=
          Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
        rw [hconst, Finset.prod_const]
      have hpow_sgn : ∀ (a : ℤ) (n : ℕ), a * a = 1 → a ^ n = if Odd n then a else 1 := by
        intro a n ha
        induction n with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, ih]
          by_cases ho : Odd t
          · have hno : ¬Odd (t + 1) := by rcases ho with ⟨u, hu⟩; rintro ⟨w, hw⟩; omega
            simp [ho, hno, ha]
          · have hyo : Odd (t + 1) := by
              rcases Nat.even_or_odd t with ⟨u, hu⟩ | h
              · exact ⟨u, by omega⟩
              · exact absurd h ho
            simp [ho, hyo]
      have hgz_sq : ∀ j : Fin m, g z j * g z j = 1 := by
        intro j
        calc g z j * g z j = (sgn (σ j) * sgn (σ j)) * (sgn (dot (x0 + z) (v j) + c j) *
              sgn (dot (x0 + z) (v j) + c j)) := by simp only [g]; ring
          _ = 1 := by rw [sgn_sq, sgn_sq, mul_one]
      rw [hgroup]
      have hfilt : ∏ j ∈ R, g z j ^ (Finset.univ.filter (fun i => f i = j)).card =
          ∏ j ∈ T, g z j := by
        calc ∏ j ∈ R, g z j ^ (Finset.univ.filter (fun i => f i = j)).card
            = ∏ j ∈ R, if Odd (Finset.univ.filter (fun i => f i = j)).card then g z j else 1 := by
              apply Finset.prod_congr rfl; intro j _
              exact hpow_sgn (g z j) _ (hgz_sq j)
          _ = ∏ j ∈ T, g z j := by rw [← Finset.prod_filter]
      rw [hfilt, dot_sum_right, sgn_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro j _
      simp only [g, sgn_add]
      ring
    have hmem_ev : f ∈ evenTuples b R ↔
        (∀ i : Fin (2 * b), f i ∈ R) ∧ ∀ j ∈ R, Even (Finset.univ.filter (fun i : Fin (2 * b) => f i = j)).card := by
      simp [evenTuples]
    by_cases hfev : f ∈ evenTuples b R
    · simp only [hfev, ↓reduceIte]
      have hTempty : T = ∅ := by
        ext j
        simp only [T, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hjR
        have hev := (hmem_ev.mp hfev).2 j hjR
        exact Nat.not_odd_iff_even.mpr hev
      have h1 : ∀ z ∈ FK, (∏ i : Fin (2 * b), g z (f i)) = 1 := by
        intro z _
        rw [hprod_eq z, hTempty]
        simp [dot_zero_right, sgn]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    · simp only [hfev, ↓reduceIte]
      have hTne : T.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        apply hfev
        rw [hmem_ev]
        refine ⟨hfR, fun j hjR => ?_⟩
        by_contra hnot
        have hodd : Odd (Finset.univ.filter (fun i => f i = j)).card :=
          Nat.not_even_iff_odd.mp hnot
        have : j ∈ T := Finset.mem_filter.mpr ⟨hjR, hodd⟩
        rw [hemp] at this
        exact Finset.notMem_empty j this
      have hTsub : T ⊆ R := Finset.filter_subset _ R
      have hTcard : T.card ≤ 2 * b := by
        have hsub : T ⊆ Finset.univ.image f := by
          intro j hj
          have hodd := (Finset.mem_filter.mp hj).2
          have hpos : 0 < (Finset.univ.filter (fun i => f i = j)).card := by
            rcases hodd with ⟨t, ht⟩; omega
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
        exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
      have hnot_orth : (∑ j ∈ T, v j) ∉ orth K := hR_orth T hTne hTcard hTsub
      have hsum0 := sum_sgn_coset_eq_zero K x0 (∑ j ∈ T, v j) hnot_orth
      simp_rw [hprod_eq, ← Finset.mul_sum]
      rw [hsum0, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsub_ev : (Fintype.piFinset (fun _ : Fin (2 * b) => R)).filter (fun f => f ∈ evenTuples b R) ⊆
      evenTuples b R := fun _ hf => (Finset.mem_filter.mp hf).2
  have hcard_ev : ((Fintype.piFinset (fun _ : Fin (2 * b) => R)).filter (fun f => f ∈ evenTuples b R)).card ≤
      (2 * b) ^ b * R.card ^ b := (Finset.card_le_card hsub_ev).trans (card_evenTuples_le R b)
  have hcard_evZ : (((Fintype.piFinset (fun _ : Fin (2 * b) => R)).filter (fun f => f ∈ evenTuples b R)).card : ℤ) ≤
      (2 * b : ℤ) ^ b * (R.card : ℤ) ^ b := by exact_mod_cast hcard_ev
  have hFKnn : (0 : ℤ) ≤ (FK.card : ℤ) := by positivity
  calc (((Fintype.piFinset (fun _ : Fin (2 * b) => R)).filter (fun f => f ∈ evenTuples b R)).card : ℤ) * (FK.card : ℤ)
      ≤ ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b) * (FK.card : ℤ) := mul_le_mul_of_nonneg_right hcard_evZ hFKnn
    _ = (FK.card : ℤ) * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b) := by ring

lemma part1_upper {k m a b : ℕ}
    (v : Fin m → Vec k) (c : Fin m → F2)
    (hindep : ∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a + 1) * max 1 (2 * b) →
      (∑ j ∈ S, v j) ≠ 0)
    (t : Vec k → (Fin a → F2))
    (hflat : ∀ x : Vec k, ∃ p : Fin a → Vec k, ∀ y : Vec k,
      t y = t x ↔ ∀ i : Fin a, dot y (p i) = dot x (p i))
    (enc : Vec k → (Fin b → Bool))
    (dec : (Fin a → F2) → (Fin b → Bool) → Fin m → F2) :
    let N := 2 ^ k
    let gain := 2 * ((Finset.univ : Finset (Vec k × Fin m)).filter (fun q =>
      dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)).card - N * m
    (gain - a * N) ^ 2 ≤ 4 * b * m * N ^ 2 := by
  classical
  dsimp only
  let N := 2 ^ k
  let C := ((Finset.univ : Finset (Vec k × Fin m)).filter (fun q =>
    dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)).card
  let G : ℤ := ∑ x : Vec k, ∑ j : Fin m,
    if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1
  have hG_eq : G = 2 * (C : ℤ) - (N : ℤ) * (m : ℤ) := by
    have h1 := sum_filter_sgn_eq_two_mul_sub (α := Vec k × Fin m)
      (fun q => dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)
    have hsum : G = ∑ q : Vec k × Fin m,
        if dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2 then (1 : ℤ) else -1 := by
      rw [Fintype.sum_prod_type]
    rw [hsum, h1]
    have hcard : Fintype.card (Vec k × Fin m) = N * m := by
      rw [Fintype.card_prod, card_vec, Fintype.card_fin]
    rw [hcard]
    push_cast
    rfl
  by_cases hsmall : 2 * C - N * m ≤ a * N
  · have h0 : (2 * C - N * m) - a * N = 0 := Nat.sub_eq_zero_of_le hsmall
    rw [h0]; simp
  · have hG_pos : (0 : ℤ) ≤ G - (a : ℤ) * (N : ℤ) := by
      have hgt : N * m + a * N < 2 * C := by omega
      have hgtZ : (N : ℤ) * (m : ℤ) + (a : ℤ) * (N : ℤ) < 2 * (C : ℤ) := by exact_mod_cast hgt
      linarith
    have hnat_eq : (((2 * C - N * m) - a * N : ℕ) : ℤ) = G - (a : ℤ) * (N : ℤ) := by
      have hge1 : N * m ≤ 2 * C := by omega
      have hge2 : a * N ≤ 2 * C - N * m := by omega
      rw [Nat.cast_sub hge2, Nat.cast_sub hge1, hG_eq]
      push_cast; rfl
    let img : Finset (Fin a → F2) := Finset.univ.image t
    let fib : (Fin a → F2) → Finset (Vec k) := fun u => Finset.univ.filter (fun x => t x = u)
    have hsum_card : ∑ u ∈ img, (fib u).card = N := by
      have := Finset.sum_card_fiberwise_eq_card_filter (s := (Finset.univ : Finset (Vec k)))
        (t := img) (g := t)
      have hfilt : (Finset.univ.filter (fun x : Vec k => t x ∈ img)) = Finset.univ := by
        ext x; simp [img]
      rw [hfilt, Finset.card_univ, card_vec] at this
      exact this
    have hsum_G : G = ∑ u ∈ img, ∑ x ∈ fib u, ∑ j : Fin m,
        if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1 := by
      have h1 := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Vec k)))
        (t := img) (g := t) (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
        (f := fun x => ∑ j : Fin m, if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1)
      change (∑ x : Vec k, ∑ j : Fin m,
        if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) = _
      rw [← h1]
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro x hx
      have htx : t x = u := (Finset.mem_filter.mp hx).2
      simp [htx]
    have hfiber : ∀ u ∈ img,
        ∃ H : ℤ, 0 ≤ H ∧ H ^ 2 ≤ 4 * (b : ℤ) * (m : ℤ) * ((fib u).card : ℤ) ^ 2 ∧
          (∑ x ∈ fib u, ∑ j : Fin m, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) ≤
            (a : ℤ) * ((fib u).card : ℤ) + H := by
      intro u hu
      obtain ⟨x0, _, hx0u⟩ := Finset.mem_image.mp hu
      obtain ⟨p, hp⟩ := hflat x0
      let P : Submodule F2 (Vec k) := Submodule.span F2 (Set.range p)
      let K : Submodule F2 (Vec k) := orth P
      have hP_fin : Module.finrank F2 P ≤ a := by
        let φ : (Fin a → F2) →ₗ[F2] Vec k :=
          { toFun := fun α => ∑ i : Fin a, α i • p i
            map_add' := fun α1 α2 => by simp [add_smul, Finset.sum_add_distrib]
            map_smul' := fun c α => by simp [Finset.smul_sum, mul_smul] }
        have hrg : LinearMap.range φ = P := by
          apply le_antisymm
          · rintro _ ⟨α, rfl⟩
            change ∑ i : Fin a, α i • p i ∈ P
            exact Submodule.sum_mem P (fun i _ => Submodule.smul_mem P _
              (Submodule.subset_span (Set.mem_range.mpr ⟨i, rfl⟩)))
          · rw [Submodule.span_le]
            rintro _ ⟨i, rfl⟩
            change p i ∈ LinearMap.range φ
            refine ⟨fun j => if j = i then 1 else 0, ?_⟩
            change ∑ j : Fin a, (if j = i then (1 : F2) else 0) • p j = p i
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hj; simp [hj]
            · intro h'; exact False.elim (h' (Finset.mem_univ i))
        rw [← hrg]
        have hrn := φ.finrank_range_add_finrank_ker
        have hdom : Module.finrank F2 (Fin a → F2) = a := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
        omega
      have horthK : orth K = P := orth_orth P
      obtain ⟨D, hDcard, hDgood⟩ := short_relation_pivot v P hP_fin hindep
      let R : Finset (Fin m) := Finset.univ \ D
      let FK : Finset (Vec k) := Finset.univ.filter (fun z : Vec k => z ∈ K)
      have hfib_eq : fib u = FK.image (fun z => x0 + z) := by
        ext y
        simp only [fib, FK, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hyu
          refine ⟨y + x0, ?_, by rw [add_comm y x0, ← add_assoc, vec_add_self, zero_add]⟩
          intro w hw
          have hker : w ∈ Submodule.span F2 (Set.range p) := hw
          let f : Vec k →ₗ[F2] F2 :=
            { toFun := fun w' => dot w' (y + x0)
              map_add' := fun w1 w2 => dot_add_left w1 w2 _
              map_smul' := fun s w' => dot_smul_left s w' _ }
          have hle : Submodule.span F2 (Set.range p) ≤ LinearMap.ker f := by
            rw [Submodule.span_le]
            rintro _ ⟨i, rfl⟩
            change dot (p i) (y + x0) = 0
            rw [dot_comm, dot_add_left]
            have hty : t y = t x0 := hyu.trans hx0u.symm
            have hpi : dot y (p i) = dot x0 (p i) := (hp y).mp hty i
            rw [hpi, f2_add_self]
          exact hle hker
        · rintro ⟨z, hzK, rfl⟩
          rw [← hx0u, hp (x0 + z)]
          intro i
          rw [dot_add_left]
          have hzi : dot z (p i) = 0 := by
            rw [dot_comm]
            exact hzK (p i) (Submodule.subset_span ⟨i, rfl⟩)
          rw [hzi, add_zero]
      have hcard_fib : (fib u).card = FK.card := by
        rw [hfib_eq, Finset.card_image_of_injective]
        intro z1 z2 heq
        have := congrArg (x0 + ·) heq
        simpa [← add_assoc, vec_add_self] using this
      have hsplit_u : (∑ x ∈ fib u, ∑ j : Fin m,
            if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) =
          (∑ x ∈ fib u, ∑ j ∈ D, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) +
          (∑ z ∈ FK, ∑ j ∈ R, sgn (dec u (enc (x0 + z)) j) * sgn (dot (x0 + z) (v j) + c j)) := by
        have hDR : ∀ x : Vec k, (∑ j : Fin m, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) =
            (∑ j ∈ D, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) +
            (∑ j ∈ R, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) := by
          intro x
          rw [← Finset.sum_union Finset.disjoint_sdiff]
          congr 1; ext j; simp
        simp_rw [hDR, Finset.sum_add_distrib]
        congr 1
        rw [hfib_eq, Finset.sum_image]
        · apply Finset.sum_congr rfl; intro z _
          apply Finset.sum_congr rfl; intro j _
          exact sgn_eq_iff_hit _ _
        · intro z1 _ z2 _ heq
          have := congrArg (x0 + ·) heq
          simpa [← add_assoc, vec_add_self] using this
      have hD_le : (∑ x ∈ fib u, ∑ j ∈ D,
            if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) ≤
          (a : ℤ) * ((fib u).card : ℤ) := by
        have h1 : ∀ x ∈ fib u, (∑ j ∈ D,
            if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) ≤ (D.card : ℤ) := by
          intro x _
          calc (∑ j ∈ D, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1)
              ≤ ∑ _j ∈ D, (1 : ℤ) := Finset.sum_le_sum (fun j _ => by split_ifs <;> norm_num)
            _ = (D.card : ℤ) := by simp
        calc (∑ x ∈ fib u, ∑ j ∈ D, if dec u (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1)
            ≤ ∑ _x ∈ fib u, (D.card : ℤ) := Finset.sum_le_sum h1
          _ = ((fib u).card : ℤ) * (D.card : ℤ) := by simp
          _ ≤ ((fib u).card : ℤ) * (a : ℤ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hDcard) (by positivity)
          _ = (a : ℤ) * ((fib u).card : ℤ) := by ring
      by_cases hb0 : b = 0
      · subst hb0
        refine ⟨0, le_rfl, by simp, ?_⟩
        rw [hsplit_u, add_zero]
        have hR0 : ∑ z ∈ FK, ∑ j ∈ R, sgn (dec u (enc (x0 + z)) j) * sgn (dot (x0 + z) (v j) + c j) = 0 := by
          let w0 : Fin 0 → Bool := Fin.elim0
          have hw0 : ∀ z : Vec k, enc (x0 + z) = w0 := fun z => funext (fun i => Fin.elim0 i)
          simp_rw [hw0]
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro j hjR
          have hdisj : Disjoint ({j} : Finset (Fin m)) D := by
            rw [Finset.disjoint_singleton_left]
            exact (Finset.mem_sdiff.mp hjR).2
          have hnotP : v j ∉ P := by
            have := hDgood {j} (Finset.singleton_nonempty j) (by simp) hdisj
            simpa using this
          have hnot_orth : v j ∉ orth K := by rwa [horthK]
          have hsz := sum_sgn_coset_eq_zero K x0 (v j) hnot_orth
          have hfac : ∑ z ∈ FK, sgn (dec u w0 j) * sgn (dot (x0 + z) (v j) + c j) =
              (sgn (dec u w0 j) * sgn (c j)) * ∑ z ∈ FK, sgn (dot (x0 + z) (v j)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro z _
            rw [sgn_add]; ring
          rw [hfac, hsz, mul_zero]
        rw [hR0, add_zero]
        exact hD_le
      · have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
        let Hsum : ℤ := ∑ z ∈ FK, ∑ j ∈ R, sgn (dec u (enc (x0 + z)) j) * sgn (dot (x0 + z) (v j) + c j)
        refine ⟨|Hsum|, abs_nonneg _, ?_, ?_⟩
        · have hR_orth : ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ 2 * b → T ⊆ R →
              (∑ j ∈ T, v j) ∉ orth K := by
            intro T hTne hTle hTsub
            rw [horthK]
            have hmax : max 1 (2 * b) = 2 * b := max_eq_right (by omega)
            have hTdisj : Disjoint T D :=
              Finset.disjoint_of_subset_left hTsub Finset.sdiff_disjoint
            exact hDgood T hTne (by omega) hTdisj
          let Sfun : (Fin b → Bool) → Vec k → ℤ := fun w z =>
            ∑ j ∈ R, sgn (dec u w j) * sgn (dot (x0 + z) (v j) + c j)
          have hH_le : |Hsum| ≤ ∑ z ∈ FK, |Sfun (enc (x0 + z)) z| := Finset.abs_sum_le_sum_abs _ _
          have hpow1 : |Hsum| ^ (2 * b) ≤ (∑ z ∈ FK, |Sfun (enc (x0 + z)) z|) ^ (2 * b) :=
            pow_le_pow_left₀ (abs_nonneg _) hH_le (2 * b)
          have hpow2 : (∑ z ∈ FK, |Sfun (enc (x0 + z)) z|) ^ (2 * b) ≤
              (FK.card : ℤ) ^ (2 * b - 1) * ∑ z ∈ FK, |Sfun (enc (x0 + z)) z| ^ (2 * b) :=
            pow_sum_le_card_pow_mul_sum_pow FK (fun z => |Sfun (enc (x0 + z)) z|)
              (fun _ _ => abs_nonneg _) (2 * b) (by omega)
          have hpow_even : ∀ (y : ℤ), |y| ^ (2 * b) = y ^ (2 * b) := by
            intro y
            rw [pow_mul, pow_mul, sq_abs]
          have hsum_w : ∑ z ∈ FK, |Sfun (enc (x0 + z)) z| ^ (2 * b) ≤
              ∑ w : Fin b → Bool, ∑ z ∈ FK, Sfun w z ^ (2 * b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_le_sum
            intro z _
            rw [hpow_even]
            exact Finset.single_le_sum (f := fun w : Fin b → Bool => Sfun w z ^ (2 * b))
              (fun w _ => by rw [pow_mul]; positivity) (Finset.mem_univ (enc (x0 + z)))
          have hmom_w : ∀ w : Fin b → Bool, ∑ z ∈ FK, Sfun w z ^ (2 * b) ≤
              (FK.card : ℤ) * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b) :=
            fun w => fiber_moment_bound hb1 v c K x0 R hR_orth (dec u w)
          have hR_le_m : (R.card : ℤ) ≤ (m : ℤ) := by
            have : R.card ≤ m := (Finset.card_le_univ R).trans (by simp)
            exact_mod_cast this
          have hbound_pow : (|Hsum| ^ 2) ^ b ≤ (4 * (b : ℤ) * (m : ℤ) * (FK.card : ℤ) ^ 2) ^ b := by
            calc (|Hsum| ^ 2) ^ b = |Hsum| ^ (2 * b) := (pow_mul _ 2 b).symm
              _ ≤ (FK.card : ℤ) ^ (2 * b - 1) * ∑ z ∈ FK, |Sfun (enc (x0 + z)) z| ^ (2 * b) :=
                  hpow1.trans hpow2
              _ ≤ (FK.card : ℤ) ^ (2 * b - 1) * ∑ w : Fin b → Bool, ∑ z ∈ FK, Sfun w z ^ (2 * b) :=
                  mul_le_mul_of_nonneg_left hsum_w (by positivity)
              _ ≤ (FK.card : ℤ) ^ (2 * b - 1) *
                    ∑ _w : Fin b → Bool, (FK.card : ℤ) * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b) :=
                  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ => hmom_w w)) (by positivity)
              _ = (FK.card : ℤ) ^ (2 * b - 1) * ((2 : ℤ) ^ b * ((FK.card : ℤ) * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b))) := by
                  simp [Finset.sum_const, zsmul_eq_mul]
              _ = (FK.card : ℤ) ^ (2 * b) * ((4 * (b : ℤ) * (R.card : ℤ)) ^ b) := by
                  have hpow_fk : (FK.card : ℤ) ^ (2 * b - 1) * (FK.card : ℤ) = (FK.card : ℤ) ^ (2 * b) := by
                    have h2b : 2 * b - 1 + 1 = 2 * b := by omega
                    rw [← pow_succ, h2b]
                  have h4b : (2 : ℤ) ^ b * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b) =
                      (4 * (b : ℤ) * (R.card : ℤ)) ^ b := by
                    rw [← mul_pow, ← mul_pow]; congr 1; ring
                  calc (FK.card : ℤ) ^ (2 * b - 1) * ((2 : ℤ) ^ b * ((FK.card : ℤ) * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b)))
                      = ((FK.card : ℤ) ^ (2 * b - 1) * (FK.card : ℤ)) *
                          ((2 : ℤ) ^ b * ((2 * b : ℤ) ^ b * (R.card : ℤ) ^ b)) := by ring
                    _ = (FK.card : ℤ) ^ (2 * b) * (4 * (b : ℤ) * (R.card : ℤ)) ^ b := by rw [hpow_fk, h4b]
              _ = (4 * (b : ℤ) * (R.card : ℤ) * (FK.card : ℤ) ^ 2) ^ b := by
                  rw [mul_pow, pow_mul]; ring
              _ ≤ (4 * (b : ℤ) * (m : ℤ) * (FK.card : ℤ) ^ 2) ^ b := by
                  apply pow_le_pow_left₀ (by positivity)
                  have : 0 ≤ 4 * (b : ℤ) * (FK.card : ℤ) ^ 2 := by positivity
                  nlinarith
          rw [hcard_fib]
          by_contra hlt
          push Not at hlt
          have hstrict : (4 * (b : ℤ) * (m : ℤ) * (FK.card : ℤ) ^ 2) ^ b < (|Hsum| ^ 2) ^ b :=
            pow_lt_pow_left₀ hlt (by positivity) hb0
          omega
        · rw [hsplit_u]
          have hle := le_abs_self Hsum
          linarith
    choose Hfn hHnn hHsq hHub using hfiber
    have hG_le : G - (a : ℤ) * (N : ℤ) ≤ ∑ u ∈ img, if hu : u ∈ img then Hfn u hu else 0 := by
      have h1 : G ≤ ∑ u ∈ img, ((a : ℤ) * ((fib u).card : ℤ) + (if hu : u ∈ img then Hfn u hu else 0)) := by
        rw [hsum_G]
        apply Finset.sum_le_sum
        intro u hu
        simp only [hu, ↓reduceDIte]
        exact hHub u hu
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
      have hscZ : (∑ u ∈ img, ((fib u).card : ℤ)) = (N : ℤ) := by exact_mod_cast hsum_card
      rw [hscZ] at h1
      linarith
    let Hval : (Fin a → F2) → ℤ := fun u => if hu : u ∈ img then Hfn u hu else 0
    have hHval_nn : ∀ u ∈ img, 0 ≤ Hval u := fun u hu => by simp [Hval, hu, hHnn u hu]
    have hHval_sq : ∀ u ∈ img, Hval u ^ 2 ≤ 4 * (b : ℤ) * (m : ℤ) * ((fib u).card : ℤ) ^ 2 :=
      fun u hu => by simp [Hval, hu, hHsq u hu]
    have hpair : ∀ u1 ∈ img, ∀ u2 ∈ img,
        Hval u1 * Hval u2 ≤ 4 * (b : ℤ) * (m : ℤ) * ((fib u1).card : ℤ) * ((fib u2).card : ℤ) := by
      intro u1 hu1 u2 hu2
      have hsq : (Hval u1 * Hval u2) ^ 2 ≤
          (4 * (b : ℤ) * (m : ℤ) * ((fib u1).card : ℤ) * ((fib u2).card : ℤ)) ^ 2 := by
        calc (Hval u1 * Hval u2) ^ 2 = Hval u1 ^ 2 * Hval u2 ^ 2 := mul_pow _ _ 2
          _ ≤ (4 * (b : ℤ) * (m : ℤ) * ((fib u1).card : ℤ) ^ 2) *
                (4 * (b : ℤ) * (m : ℤ) * ((fib u2).card : ℤ) ^ 2) :=
              mul_le_mul (hHval_sq u1 hu1) (hHval_sq u2 hu2) (sq_nonneg _) (by positivity)
          _ = (4 * (b : ℤ) * (m : ℤ) * ((fib u1).card : ℤ) * ((fib u2).card : ℤ)) ^ 2 := by ring
      by_contra hlt
      push Not at hlt
      have hstrict : (4 * (b : ℤ) * (m : ℤ) * ((fib u1).card : ℤ) * ((fib u2).card : ℤ)) ^ 2 <
          (Hval u1 * Hval u2) ^ 2 :=
        pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      omega
    have hsum_sq : (∑ u ∈ img, Hval u) ^ 2 ≤ 4 * (b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2 := by
      calc (∑ u ∈ img, Hval u) ^ 2
          = (∑ u ∈ img, Hval u) * (∑ u ∈ img, Hval u) := sq _
        _ = ∑ u1 ∈ img, ∑ u2 ∈ img, Hval u1 * Hval u2 := by
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro u1 _; rw [Finset.mul_sum]
        _ ≤ ∑ u1 ∈ img, ∑ u2 ∈ img,
              4 * (b : ℤ) * (m : ℤ) * ((fib u1).card : ℤ) * ((fib u2).card : ℤ) :=
            Finset.sum_le_sum (fun u1 hu1 => Finset.sum_le_sum (fun u2 hu2 => hpair u1 hu1 u2 hu2))
        _ = 4 * (b : ℤ) * (m : ℤ) * ((∑ u ∈ img, ((fib u).card : ℤ)) * (∑ u ∈ img, ((fib u).card : ℤ))) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro u1 _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro u2 _; ring
        _ = 4 * (b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2 := by
            have hscZ : (∑ u ∈ img, ((fib u).card : ℤ)) = (N : ℤ) := by exact_mod_cast hsum_card
            rw [hscZ, sq]
    have hZ : (G - (a : ℤ) * (N : ℤ)) ^ 2 ≤ 4 * (b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2 :=
      (pow_le_pow_left₀ hG_pos hG_le 2).trans hsum_sq
    rw [← hnat_eq] at hZ
    exact_mod_cast hZ

def radSum (s : ℕ) (σ : Fin s → Bool) : ℤ :=
  ∑ i : Fin s, if σ i then (1 : ℤ) else -1

lemma rad_moments (s : ℕ) :
    (∑ σ : Fin s → Bool, radSum s σ ^ 2 = (s : ℤ) * (2 : ℤ) ^ s) ∧
    (∑ σ : Fin s → Bool, radSum s σ ^ 4 = (3 * (s : ℤ) ^ 2 - 2 * (s : ℤ)) * (2 : ℤ) ^ s) := by
  induction s with
  | zero =>
    have h1 : ∀ σ : Fin 0 → Bool, radSum 0 σ = 0 := fun _ => by simp [radSum]
    simp [h1]
  | succ n ih =>
    rcases ih with ⟨ih2, ih4⟩
    let e : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) :=
      { toFun := fun σ => (σ 0, fun i => σ i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun σ => by
          funext i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j; rfl
        right_inv := fun ⟨b, τ⟩ => by
          ext
          · rfl
          · rfl }
    have hrad : ∀ (b : Bool) (τ : Fin n → Bool),
        radSum (n + 1) (e.symm (b, τ)) = (if b then (1 : ℤ) else -1) + radSum n τ := by
      intro b τ
      simp [radSum, e, Fin.sum_univ_succ]
    have h2 : ∑ σ : Fin (n + 1) → Bool, radSum (n + 1) σ ^ 2 =
        (n + 1 : ℤ) * (2 : ℤ) ^ (n + 1) := by
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
      simp_rw [hrad, Fintype.sum_bool]
      rw [← Finset.sum_add_distrib]
      trans (∑ τ : Fin n → Bool, (2 * radSum n τ ^ 2 + 2))
      · apply Finset.sum_congr rfl; intro τ _
        change ((1 : ℤ) + radSum n τ) ^ 2 + (-1 + radSum n τ) ^ 2 = 2 * radSum n τ ^ 2 + 2
        ring
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih2, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [pow_succ]
      ring
    have h4 : ∑ σ : Fin (n + 1) → Bool, radSum (n + 1) σ ^ 4 =
        (3 * ((n + 1 : ℤ)) ^ 2 - 2 * (n + 1 : ℤ)) * (2 : ℤ) ^ (n + 1) := by
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
      simp_rw [hrad, Fintype.sum_bool]
      rw [← Finset.sum_add_distrib]
      trans (∑ τ : Fin n → Bool, (2 * radSum n τ ^ 4 + 12 * radSum n τ ^ 2 + 2))
      · apply Finset.sum_congr rfl; intro τ _
        change ((1 : ℤ) + radSum n τ) ^ 4 + (-1 + radSum n τ) ^ 4 =
          2 * radSum n τ ^ 4 + 12 * radSum n τ ^ 2 + 2
        ring
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih4, ih2, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [pow_succ]
      ring
    exact ⟨by simpa using h2, by simpa using h4⟩

lemma khintchine_l1 (s : ℕ) (hs : 1 ≤ s) :
    (s : ℤ) * ((2 : ℤ) ^ s) ^ 2 ≤ 3 * (∑ σ : Fin s → Bool, |radSum s σ|) ^ 2 := by
  let S1 : ℤ := ∑ σ : Fin s → Bool, |radSum s σ|
  let S2 : ℤ := ∑ σ : Fin s → Bool, |radSum s σ| ^ 2
  let S3 : ℤ := ∑ σ : Fin s → Bool, |radSum s σ| ^ 3
  let S4 : ℤ := ∑ σ : Fin s → Bool, |radSum s σ| ^ 4
  have hS2_eq : S2 = (s : ℤ) * (2 : ℤ) ^ s := by
    have := (rad_moments s).1
    simp only [S2, sq_abs]
    exact this
  have hS4_eq : S4 = (3 * (s : ℤ) ^ 2 - 2 * (s : ℤ)) * (2 : ℤ) ^ s := by
    have := (rad_moments s).2
    have h4 : ∀ σ, |radSum s σ| ^ 4 = radSum s σ ^ 4 := fun σ => by
      have : (4 : ℕ) = 2 * 2 := rfl
      rw [this, pow_mul, pow_mul, sq_abs]
    simp only [S4, h4]
    exact this
  have hcs1 : S2 ^ 2 ≤ S1 * S3 := by
    have hnn : 0 ≤ ∑ σ : Fin s → Bool, ∑ τ : Fin s → Bool,
        (|radSum s σ| - |radSum s τ|) ^ 2 * |radSum s σ| * |radSum s τ| := by
      apply Finset.sum_nonneg; intro σ _
      apply Finset.sum_nonneg; intro τ _
      positivity
    have hexp : ∑ σ : Fin s → Bool, ∑ τ : Fin s → Bool,
        (|radSum s σ| - |radSum s τ|) ^ 2 * |radSum s σ| * |radSum s τ| =
        2 * (S1 * S3 - S2 ^ 2) := by
      have hterm : ∀ σ τ : Fin s → Bool,
          (|radSum s σ| - |radSum s τ|) ^ 2 * |radSum s σ| * |radSum s τ| =
          |radSum s σ| ^ 3 * |radSum s τ| - 2 * (|radSum s σ| ^ 2 * |radSum s τ| ^ 2) +
          |radSum s σ| * |radSum s τ| ^ 3 := fun _ _ => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      change S3 * S1 - 2 * (S2 * S2) + S1 * S3 = 2 * (S1 * S3 - S2 ^ 2)
      ring
    linarith
  have hcs2 : S3 ^ 2 ≤ S2 * S4 := by
    have hnn : 0 ≤ ∑ σ : Fin s → Bool, ∑ τ : Fin s → Bool,
        (|radSum s σ| * |radSum s τ| ^ 2 - |radSum s τ| * |radSum s σ| ^ 2) ^ 2 := by
      apply Finset.sum_nonneg; intro σ _
      apply Finset.sum_nonneg; intro τ _
      positivity
    have hexp : ∑ σ : Fin s → Bool, ∑ τ : Fin s → Bool,
        (|radSum s σ| * |radSum s τ| ^ 2 - |radSum s τ| * |radSum s σ| ^ 2) ^ 2 =
        2 * (S2 * S4 - S3 ^ 2) := by
      have hterm : ∀ σ τ : Fin s → Bool,
          (|radSum s σ| * |radSum s τ| ^ 2 - |radSum s τ| * |radSum s σ| ^ 2) ^ 2 =
          |radSum s σ| ^ 2 * |radSum s τ| ^ 4 - 2 * (|radSum s σ| ^ 3 * |radSum s τ| ^ 3) +
          |radSum s σ| ^ 4 * |radSum s τ| ^ 2 := fun _ _ => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      change S2 * S4 - 2 * (S3 * S3) + S4 * S2 = 2 * (S2 * S4 - S3 ^ 2)
      ring
    linarith
  have hS2_pos : (0 : ℤ) < S2 := by rw [hS2_eq]; positivity
  have hS1_nn : (0 : ℤ) ≤ S1 := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hS3_nn : (0 : ℤ) ≤ S3 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hS4_le : S4 ≤ 3 * (s : ℤ) ^ 2 * (2 : ℤ) ^ s := by
    rw [hS4_eq]
    have hnn : (0 : ℤ) ≤ 2 * (s : ℤ) * (2 : ℤ) ^ s := by positivity
    linarith
  have h4 : S2 ^ 4 ≤ S1 ^ 2 * (S2 * S4) := by
    calc S2 ^ 4 = (S2 ^ 2) ^ 2 := by ring
      _ ≤ (S1 * S3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hcs1 2
      _ = S1 ^ 2 * S3 ^ 2 := mul_pow S1 S3 2
      _ ≤ S1 ^ 2 * (S2 * S4) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
  have h3 : S2 ^ 3 ≤ S1 ^ 2 * S4 := by
    have : S2 * S2 ^ 3 ≤ S2 * (S1 ^ 2 * S4) := by
      calc S2 * S2 ^ 3 = S2 ^ 4 := by ring
        _ ≤ S1 ^ 2 * (S2 * S4) := h4
        _ = S2 * (S1 ^ 2 * S4) := by ring
    exact le_of_mul_le_mul_left this hS2_pos
  have h3' : ((s : ℤ) * (2 : ℤ) ^ s) ^ 3 ≤ S1 ^ 2 * (3 * (s : ℤ) ^ 2 * (2 : ℤ) ^ s) := by
    rw [← hS2_eq]
    exact h3.trans (mul_le_mul_of_nonneg_left hS4_le (sq_nonneg _))
  have hfac_pos : (0 : ℤ) < (s : ℤ) ^ 2 * (2 : ℤ) ^ s := by positivity
  have hmul : ((s : ℤ) ^ 2 * (2 : ℤ) ^ s) * ((s : ℤ) * ((2 : ℤ) ^ s) ^ 2) ≤
      ((s : ℤ) ^ 2 * (2 : ℤ) ^ s) * (3 * S1 ^ 2) := by
    calc ((s : ℤ) ^ 2 * (2 : ℤ) ^ s) * ((s : ℤ) * ((2 : ℤ) ^ s) ^ 2)
        = ((s : ℤ) * (2 : ℤ) ^ s) ^ 3 := by ring
      _ ≤ S1 ^ 2 * (3 * (s : ℤ) ^ 2 * (2 : ℤ) ^ s) := h3'
      _ = ((s : ℤ) ^ 2 * (2 : ℤ) ^ s) * (3 * S1 ^ 2) := by ring
  exact le_of_mul_le_mul_left hmul hfac_pos

lemma exists_good_signs {k m : ℕ} (v : Fin m → Vec k) (c : Fin m → F2)
    (B : Finset (Fin m)) (hB : 1 ≤ B.card) :
    ∃ s : Fin m → F2,
      (B.card : ℤ) * ((2 ^ k : ℕ) : ℤ) ^ 2 ≤
        3 * (∑ x : Vec k, |∑ j ∈ B, sgn (s j) * sgn (dot x (v j) + c j)|) ^ 2 := by
  classical
  let d := B.card
  let e : Fin d ≃ B := (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
  let val : (Fin d → Bool) → ℤ := fun σ =>
    ∑ x : Vec k, |∑ i : Fin d, (if σ i then (1 : ℤ) else -1) * sgn (dot x (v (e i).1) + c (e i).1)|
  have havg : ∑ σ : Fin d → Bool, val σ =
      ((2 ^ k : ℕ) : ℤ) * ∑ σ : Fin d → Bool, |radSum d σ| := by
    simp only [val]
    rw [Finset.sum_comm]
    have hx_eq : ∀ x : Vec k,
        (∑ σ : Fin d → Bool, |∑ i : Fin d, (if σ i then (1 : ℤ) else -1) * sgn (dot x (v (e i).1) + c (e i).1)|) =
        ∑ σ : Fin d → Bool, |radSum d σ| := by
      intro x
      let flip : (Fin d → Bool) ≃ (Fin d → Bool) :=
        { toFun := fun σ i => if dot x (v (e i).1) + c (e i).1 = 0 then σ i else !σ i
          invFun := fun σ i => if dot x (v (e i).1) + c (e i).1 = 0 then σ i else !σ i
          left_inv := fun σ => by funext i; by_cases h : dot x (v (e i).1) + c (e i).1 = 0 <;> simp [h]
          right_inv := fun σ => by funext i; by_cases h : dot x (v (e i).1) + c (e i).1 = 0 <;> simp [h] }
      rw [← flip.sum_comp]
      apply Finset.sum_congr rfl; intro σ _
      congr 1
      simp only [radSum]
      apply Finset.sum_congr rfl; intro i _
      simp only [flip, Equiv.coe_fn_mk, sgn]
      by_cases h : dot x (v (e i).1) + c (e i).1 = 0
      · simp only [h, ↓reduceIte, mul_one]
      · simp only [h, ↓reduceIte]; cases σ i <;> decide
    simp_rw [hx_eq]
    rw [Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul]
  have hne : (Finset.univ : Finset (Fin d → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨σ0, _, hσ0⟩ := Finset.exists_max_image Finset.univ val hne
  have hmax : ∑ σ : Fin d → Bool, val σ ≤ ((2 : ℤ) ^ d) * val σ0 := by
    calc ∑ σ : Fin d → Bool, val σ
        ≤ ∑ _σ : Fin d → Bool, val σ0 := Finset.sum_le_sum (fun σ _ => hσ0 σ (Finset.mem_univ σ))
      _ = ((2 : ℤ) ^ d) * val σ0 := by
          simp [Finset.sum_const, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, zsmul_eq_mul]
  rw [havg] at hmax
  let s : Fin m → F2 := fun j =>
    if h : j ∈ B then if σ0 (e.symm ⟨j, h⟩) then 0 else 1 else 0
  refine ⟨s, ?_⟩
  have hval_eq : val σ0 = ∑ x : Vec k, |∑ j ∈ B, sgn (s j) * sgn (dot x (v j) + c j)| := by
    simp only [val]
    apply Finset.sum_congr rfl; intro x _
    congr 1
    rw [← Finset.sum_coe_sort B, ← e.sum_comp]
    apply Finset.sum_congr rfl; intro i _
    have hmem : (e i).1 ∈ B := (e i).2
    have hs_eq : sgn (s (e i).1) = if σ0 i then (1 : ℤ) else -1 := by
      simp only [s, hmem, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
      cases σ0 i <;> decide
    rw [hs_eq]
  rw [← hval_eq]
  have hkh := khintchine_l1 d hB
  have h2d_pos : (0 : ℤ) < ((2 : ℤ) ^ d) ^ 2 := by positivity
  have hmul : ((2 : ℤ) ^ d) ^ 2 * ((d : ℤ) * ((2 ^ k : ℕ) : ℤ) ^ 2) ≤
      ((2 : ℤ) ^ d) ^ 2 * (3 * val σ0 ^ 2) := by
    calc ((2 : ℤ) ^ d) ^ 2 * ((d : ℤ) * ((2 ^ k : ℕ) : ℤ) ^ 2)
        = ((2 ^ k : ℕ) : ℤ) ^ 2 * ((d : ℤ) * ((2 : ℤ) ^ d) ^ 2) := by ring
      _ ≤ ((2 ^ k : ℕ) : ℤ) ^ 2 * (3 * (∑ σ : Fin d → Bool, |radSum d σ|) ^ 2) :=
          mul_le_mul_of_nonneg_left hkh (sq_nonneg _)
      _ = 3 * (((2 ^ k : ℕ) : ℤ) * ∑ σ : Fin d → Bool, |radSum d σ|) ^ 2 := by ring
      _ ≤ 3 * (((2 : ℤ) ^ d) * val σ0) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_left₀ (mul_nonneg (by positivity)
            (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) hmax 2
      _ = ((2 : ℤ) ^ d) ^ 2 * (3 * val σ0 ^ 2) := by ring
  exact le_of_mul_le_mul_left hmul h2d_pos

lemma part2_lower {k m a b : ℕ} (hab : a + b ≤ m)
    (v : Fin m → Vec k) (c : Fin m → F2) :
    let N := 2 ^ k
    ∃ js : Fin a → Fin m, Function.Injective js ∧
      let t := fun (x : Vec k) (i : Fin a) => dot x (v (js i))
      ∃ (enc : Vec k → (Fin b → Bool)) (dec : (Fin a → F2) → (Fin b → Bool) → Fin m → F2),
        let gain := 2 * ((Finset.univ : Finset (Vec k × Fin m)).filter (fun q =>
          dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)).card - N * m
        a * N ≤ gain ∧ b * (m - a) * N ^ 2 ≤ 6 * (gain - a * N) ^ 2 := by
  classical
  dsimp only
  let N := 2 ^ k
  let js : Fin a → Fin m := fun i => ⟨i.1, by omega⟩
  have hjs_inj : Function.Injective js := by
    intro i1 i2 heq
    exact Fin.ext (congrArg (Fin.val : Fin m → ℕ) heq)
  refine ⟨js, hjs_inj, ?_⟩
  let t : Vec k → (Fin a → F2) := fun x i => dot x (v (js i))
  by_cases hb0 : b = 0
  · subst hb0
    let sgn_opt : Fin m → F2 := fun j =>
      if 0 ≤ ∑ x : Vec k, sgn (dot x (v j) + c j) then 0 else 1
    let enc : Vec k → (Fin 0 → Bool) := fun _ => Fin.elim0
    let dec : (Fin a → F2) → (Fin 0 → Bool) → Fin m → F2 := fun u _ j =>
      if h : j.1 < a then u ⟨j.1, h⟩ + c j else sgn_opt j
    refine ⟨enc, dec, ?_, by simp⟩
    let C := ((Finset.univ : Finset (Vec k × Fin m)).filter (fun q =>
      dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)).card
    let G : ℤ := ∑ x : Vec k, ∑ j : Fin m,
      if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1
    have hG_eq : G = 2 * (C : ℤ) - (N : ℤ) * (m : ℤ) := by
      have h1 := sum_filter_sgn_eq_two_mul_sub (α := Vec k × Fin m)
        (fun q => dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)
      have hsum : G = ∑ q : Vec k × Fin m,
          if dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2 then (1 : ℤ) else -1 := by
        rw [Fintype.sum_prod_type]
      rw [hsum, h1]
      have hcard : Fintype.card (Vec k × Fin m) = N * m := by
        rw [Fintype.card_prod, card_vec, Fintype.card_fin]
      rw [hcard]; push_cast; rfl
    have hG_ge : (a : ℤ) * (N : ℤ) ≤ G := by
      dsimp only [G]
      rw [Finset.sum_comm]
      let Aset : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.1 < a)
      let Rset : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => ¬j.1 < a)
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin m => j.1 < a)]
      have hA : ∑ j ∈ Aset, ∑ x : Vec k,
          (if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) = (a : ℤ) * (N : ℤ) := by
        have hterm : ∀ j ∈ Aset, ∑ x : Vec k,
            (if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) = (N : ℤ) := by
          intro j hj
          have hja : j.1 < a := (Finset.mem_filter.mp hj).2
          have h1 : ∀ x : Vec k, dec (t x) (enc x) j = dot x (v j) + c j := by
            intro x
            simp only [dec, hja, ↓reduceDIte, t, js]
          simp [h1, N]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        have hAcard : Aset.card = a := by
          have : Aset = Finset.univ.image js := by
            ext j
            simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hja; exact ⟨⟨j.1, hja⟩, rfl⟩
            · rintro ⟨i, rfl⟩; exact i.2
          rw [this, Finset.card_image_of_injective _ hjs_inj, Finset.card_univ, Fintype.card_fin]
        rw [hAcard]
      have hR : 0 ≤ ∑ j ∈ Rset, ∑ x : Vec k,
          (if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) := by
        apply Finset.sum_nonneg
        intro j hj
        have hjna : ¬j.1 < a := (Finset.mem_filter.mp hj).2
        have heq : ∑ x : Vec k, (if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) =
            sgn (sgn_opt j) * ∑ x : Vec k, sgn (dot x (v j) + c j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x _
          simp only [dec, hjna, ↓reduceDIte]
          exact sgn_eq_iff_hit _ _
        rw [heq]
        by_cases hnn : 0 ≤ ∑ x : Vec k, sgn (dot x (v j) + c j)
        · have hs0 : sgn_opt j = 0 := by simp [sgn_opt, hnn]
          rw [hs0]; simp only [sgn, ↓reduceIte, one_mul]; exact hnn
        · have hs1 : sgn_opt j = 1 := by simp [sgn_opt, hnn]
          have h1 : sgn (1 : F2) = -1 := by decide
          rw [hs1, h1]; linarith
      change (∑ j ∈ Aset, _) + (∑ j ∈ Rset, _) ≥ _
      linarith
    have hZ : (N : ℤ) * (m : ℤ) + (a : ℤ) * (N : ℤ) ≤ 2 * (C : ℤ) := by linarith
    have hN : N * m + a * N ≤ 2 * C := by exact_mod_cast hZ
    change a * N ≤ 2 * C - N * m
    omega
  · have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
    let blk : Fin b → Finset (Fin m) := fun l =>
      Finset.univ.filter (fun j : Fin m => a ≤ j.1 ∧ (j.1 - a) % b = l.1)
    let q : ℕ := (m - a) / b
    have hq1 : 1 ≤ q := Nat.div_pos (by omega) hb1
    have hblk_card : ∀ l : Fin b, q ≤ (blk l).card := by
      intro l
      let f : Fin q → Fin m := fun i => ⟨a + i.1 * b + l.1, by
        have h1 : (i.1 + 1) * b ≤ q * b := Nat.mul_le_mul_right b (by omega)
        have h2 : q * b ≤ m - a := Nat.div_mul_le_self (m - a) b
        have h3 : l.1 < b := l.2
        have h4 : i.1 * b + l.1 < (i.1 + 1) * b := by rw [add_mul, one_mul]; omega
        omega⟩
      have hfinj : Function.Injective f := by
        intro i1 i2 heq
        have hv : a + i1.1 * b + l.1 = a + i2.1 * b + l.1 := congrArg Fin.val heq
        have hmul : i1.1 * b = i2.1 * b := by omega
        ext
        exact Nat.eq_of_mul_eq_mul_right hb1 hmul
      have hsub : Finset.univ.image f ⊆ blk l := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
        simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and, f]
        refine ⟨by omega, ?_⟩
        have hsub1 : a + i.1 * b + l.1 - a = l.1 + b * i.1 := by ring_nf; omega
        rw [hsub1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l.2]
      calc q = (Finset.univ.image f).card := by rw [Finset.card_image_of_injective _ hfinj]; simp
        _ ≤ (blk l).card := Finset.card_le_card hsub
    have hgood : ∀ l : Fin b, ∃ s : Fin m → F2,
        ((blk l).card : ℤ) * (N : ℤ) ^ 2 ≤
          3 * (∑ x : Vec k, |∑ j ∈ blk l, sgn (s j) * sgn (dot x (v j) + c j)|) ^ 2 :=
      fun l => exists_good_signs v c (blk l) (le_trans hq1 (hblk_card l))
    choose sfn hsfn using hgood
    let s : Fin m → F2 := fun j =>
      if h : a ≤ j.1 then sfn ⟨(j.1 - a) % b, Nat.mod_lt _ hb1⟩ j else 0
    let Y : Fin b → Vec k → ℤ := fun l x =>
      ∑ j ∈ blk l, sgn (s j) * sgn (dot x (v j) + c j)
    let enc : Vec k → (Fin b → Bool) := fun x l => decide (Y l x < 0)
    let dec : (Fin a → F2) → (Fin b → Bool) → Fin m → F2 := fun u w j =>
      if h : j.1 < a then u ⟨j.1, h⟩ + c j
      else s j + (if w ⟨(j.1 - a) % b, Nat.mod_lt _ hb1⟩ then 1 else 0)
    refine ⟨enc, dec, ?_⟩
    let C := ((Finset.univ : Finset (Vec k × Fin m)).filter (fun p =>
      dec (t p.1) (enc p.1) p.2 = dot p.1 (v p.2) + c p.2)).card
    let G : ℤ := ∑ x : Vec k, ∑ j : Fin m,
      if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1
    have hG_eq : G = 2 * (C : ℤ) - (N : ℤ) * (m : ℤ) := by
      have h1 := sum_filter_sgn_eq_two_mul_sub (α := Vec k × Fin m)
        (fun p => dec (t p.1) (enc p.1) p.2 = dot p.1 (v p.2) + c p.2)
      have hsum : G = ∑ p : Vec k × Fin m,
          if dec (t p.1) (enc p.1) p.2 = dot p.1 (v p.2) + c p.2 then (1 : ℤ) else -1 := by
        rw [Fintype.sum_prod_type]
      rw [hsum, h1]
      have hcard : Fintype.card (Vec k × Fin m) = N * m := by
        rw [Fintype.card_prod, card_vec, Fintype.card_fin]
      rw [hcard]; push_cast; rfl
    let A : Fin b → ℤ := fun l => ∑ x : Vec k, |Y l x|
    have hG_exact : G = (a : ℤ) * (N : ℤ) + ∑ l : Fin b, A l := by
      let Aset : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.1 < a)
      let Rset : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => ¬j.1 < a)
      have hrow : ∀ x : Vec k,
          (∑ j : Fin m, if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) =
          (a : ℤ) + ∑ l : Fin b, |Y l x| := by
        intro x
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin m => j.1 < a)]
        congr 1
        · have hterm : ∀ j ∈ Aset,
              (if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) = 1 := by
            intro j hj
            have hja : j.1 < a := (Finset.mem_filter.mp hj).2
            simp [dec, hja, t, js]
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
          have hAcard : Aset.card = a := by
            have : Aset = Finset.univ.image js := by
              ext j
              simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hja; exact ⟨⟨j.1, hja⟩, rfl⟩
              · rintro ⟨i, rfl⟩; exact i.2
            rw [this, Finset.card_image_of_injective _ hjs_inj, Finset.card_univ, Fintype.card_fin]
          rw [hAcard]
        · have hpart : Rset = Finset.univ.biUnion blk := by
            ext j
            simp only [Rset, blk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
            constructor
            · intro hj; exact ⟨⟨(j.1 - a) % b, Nat.mod_lt _ hb1⟩, by omega, rfl⟩
            · rintro ⟨l, hl, _⟩; omega
          have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin b))) blk := by
            intro l1 _ l2 _ hne
            change Disjoint (blk l1) (blk l2)
            rw [Finset.disjoint_left]
            intro j hj1 hj2
            have h1 := (Finset.mem_filter.mp hj1).2.2
            have h2 := (Finset.mem_filter.mp hj2).2.2
            exact hne (Fin.ext (h1.symm.trans h2))
          change ∑ j ∈ Rset, _ = _
          rw [hpart, Finset.sum_biUnion hdisj]
          apply Finset.sum_congr rfl
          intro l _
          have hblk_eq : ∑ j ∈ blk l,
              (if dec (t x) (enc x) j = dot x (v j) + c j then (1 : ℤ) else -1) =
              (if enc x l then (-1 : ℤ) else 1) * Y l x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hja : a ≤ j.1 := (Finset.mem_filter.mp hj).2.1
            have hmod : (j.1 - a) % b = l.1 := (Finset.mem_filter.mp hj).2.2
            have hjna : ¬j.1 < a := by omega
            have hl_eq : (⟨(j.1 - a) % b, Nat.mod_lt _ hb1⟩ : Fin b) = l := Fin.ext hmod
            rw [sgn_eq_iff_hit]
            simp only [dec, hjna, ↓reduceDIte, hl_eq, sgn_add]
            cases enc x l
            · simp [sgn]
            · have h1 : sgn (1 : F2) = -1 := by decide
              simp [h1]
          rw [hblk_eq]
          by_cases hneg : Y l x < 0
          · simp [enc, hneg, abs_of_neg hneg]
          · simp [enc, hneg, abs_of_nonneg (not_lt.mp hneg)]
      calc G = ∑ x : Vec k, ((a : ℤ) + ∑ l : Fin b, |Y l x|) := Finset.sum_congr rfl (fun x _ => hrow x)
        _ = (∑ _x : Vec k, (a : ℤ)) + ∑ x : Vec k, ∑ l : Fin b, |Y l x| := Finset.sum_add_distrib
        _ = (a : ℤ) * (N : ℤ) + ∑ l : Fin b, A l := by
            rw [Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul, Finset.sum_comm]
            ring
    have hAnn : ∀ l : Fin b, 0 ≤ A l := fun l => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hsumA_nn : 0 ≤ ∑ l : Fin b, A l := Finset.sum_nonneg (fun l _ => hAnn l)
    have hgain_ge : a * N ≤ 2 * C - N * m := by
      have hZ : (N : ℤ) * (m : ℤ) + (a : ℤ) * (N : ℤ) ≤ 2 * (C : ℤ) := by linarith
      have hN : N * m + a * N ≤ 2 * C := by exact_mod_cast hZ
      omega
    have hdiff_eq : (((2 * C - N * m) - a * N : ℕ) : ℤ) = ∑ l : Fin b, A l := by
      have hge1 : N * m ≤ 2 * C := by
        have hZ : (N : ℤ) * (m : ℤ) ≤ 2 * (C : ℤ) := by linarith [show (0 : ℤ) ≤ (a : ℤ) * (N : ℤ) by positivity]
        exact_mod_cast hZ
      rw [Nat.cast_sub hgain_ge, Nat.cast_sub hge1]
      push_cast
      linarith
    have hAl_lb : ∀ l : Fin b, (q : ℤ) * (N : ℤ) ^ 2 ≤ 3 * A l ^ 2 := by
      intro l
      have hY_eq : ∀ x : Vec k, Y l x = ∑ j ∈ blk l, sgn (sfn l j) * sgn (dot x (v j) + c j) := by
        intro x
        apply Finset.sum_congr rfl; intro j hj
        have hja : a ≤ j.1 := (Finset.mem_filter.mp hj).2.1
        have hmod : (j.1 - a) % b = l.1 := (Finset.mem_filter.mp hj).2.2
        have hl_eq : (⟨(j.1 - a) % b, Nat.mod_lt _ hb1⟩ : Fin b) = l := Fin.ext hmod
        simp [s, hja, hl_eq]
      have hA_eq : A l = ∑ x : Vec k, |∑ j ∈ blk l, sgn (sfn l j) * sgn (dot x (v j) + c j)| := by
        simp only [A, hY_eq]
      rw [hA_eq]
      have hqle : (q : ℤ) ≤ ((blk l).card : ℤ) := by exact_mod_cast hblk_card l
      exact (mul_le_mul_of_nonneg_right hqle (sq_nonneg _)).trans (hsfn l)
    have hpair : ∀ l1 l2 : Fin b, (q : ℤ) * (N : ℤ) ^ 2 ≤ 3 * A l1 * A l2 := by
      intro l1 l2
      have hsq : ((q : ℤ) * (N : ℤ) ^ 2) ^ 2 ≤ (3 * A l1 * A l2) ^ 2 := by
        calc ((q : ℤ) * (N : ℤ) ^ 2) ^ 2
            = ((q : ℤ) * (N : ℤ) ^ 2) * ((q : ℤ) * (N : ℤ) ^ 2) := sq _
          _ ≤ (3 * A l1 ^ 2) * (3 * A l2 ^ 2) :=
              mul_le_mul (hAl_lb l1) (hAl_lb l2) (by positivity) (by positivity)
          _ = (3 * A l1 * A l2) ^ 2 := by ring
      by_contra hlt
      push Not at hlt
      have hstrict : (3 * A l1 * A l2) ^ 2 < ((q : ℤ) * (N : ℤ) ^ 2) ^ 2 :=
        pow_lt_pow_left₀ hlt (by have := hAnn l1; have := hAnn l2; positivity) (by norm_num)
      omega
    have hsum_sq : (b : ℤ) ^ 2 * (q : ℤ) * (N : ℤ) ^ 2 ≤ 3 * (∑ l : Fin b, A l) ^ 2 := by
      have hsqA : (∑ l : Fin b, A l) ^ 2 = ∑ l1 : Fin b, ∑ l2 : Fin b, A l1 * A l2 := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro l1 _
        rw [Finset.mul_sum]
      calc (b : ℤ) ^ 2 * (q : ℤ) * (N : ℤ) ^ 2
          = ∑ _l1 : Fin b, ∑ _l2 : Fin b, (q : ℤ) * (N : ℤ) ^ 2 := by
            simp [Finset.sum_const]; ring
        _ ≤ ∑ l1 : Fin b, ∑ l2 : Fin b, 3 * A l1 * A l2 :=
            Finset.sum_le_sum (fun l1 _ => Finset.sum_le_sum (fun l2 _ => hpair l1 l2))
        _ = 3 * (∑ l : Fin b, A l) ^ 2 := by
            symm
            rw [hsqA, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro l1 _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro l2 _; ring
    have hma_le : m - a ≤ 2 * b * q := by
      have hdiv : b * q + (m - a) % b = m - a := Nat.div_add_mod (m - a) b
      have hrem : (m - a) % b < b := Nat.mod_lt _ hb1
      have hle1 : b * q + b ≤ b * q + b * q := Nat.add_le_add_left (Nat.le_mul_of_pos_right b hq1) _
      have h2bq : b * q + b * q = 2 * b * q := by ring
      omega
    have hZ : (b : ℤ) * ((m - a : ℕ) : ℤ) * (N : ℤ) ^ 2 ≤ 6 * (∑ l : Fin b, A l) ^ 2 := by
      have hmaZ : ((m - a : ℕ) : ℤ) ≤ 2 * (b : ℤ) * (q : ℤ) := by exact_mod_cast hma_le
      calc (b : ℤ) * ((m - a : ℕ) : ℤ) * (N : ℤ) ^ 2
          ≤ (b : ℤ) * (2 * (b : ℤ) * (q : ℤ)) * (N : ℤ) ^ 2 := by
            have : 0 ≤ (b : ℤ) * (N : ℤ) ^ 2 := by positivity
            nlinarith
        _ = 2 * ((b : ℤ) ^ 2 * (q : ℤ) * (N : ℤ) ^ 2) := by ring
        _ ≤ 2 * (3 * (∑ l : Fin b, A l) ^ 2) := mul_le_mul_of_nonneg_left hsum_sq (by norm_num)
        _ = 6 * (∑ l : Fin b, A l) ^ 2 := by ring
    rw [← hdiff_eq] at hZ
    refine ⟨hgain_ge, ?_⟩
    exact_mod_cast hZ

end PEqualNP.Outside.L_meta_27811_aux

theorem PEqualNP.Outside.L_meta_27811 :
∀ (k m a b : ℕ), a+b ≤ m →
  let F := ZMod 2
  let V := Fin k → F
  let U := Fin a → F
  let W := Fin b → Bool
  let N := 2^k
  let dot := fun (x y : V) => ∑ i : Fin k, x i * y i
  ∀ (v : Fin m → V) (c : Fin m → F),
    (∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a+1)*max 1 (2*b) →
      (∑ j ∈ S, v j) ≠ 0) →
    let flat := fun (t : V → U) => ∀ x : V, ∃ p : Fin a → V, ∀ y : V,
      t y = t x ↔ ∀ i : Fin a, dot y (p i) = dot x (p i)
    let gain := fun (t : V → U) (enc : V → W) (dec : U → W → Fin m → F) =>
      2*((Finset.univ : Finset (V × Fin m)).filter (fun q =>
        dec (t q.1) (enc q.1) q.2 = dot q.1 (v q.2) + c q.2)).card - N*m
    (∀ t, flat t → ∀ enc dec, (gain t enc dec - a*N)^2 ≤ 4*b*m*N^2) ∧
    (∃ js : Fin a → Fin m, Function.Injective js ∧
      let t := fun (x : V) (i : Fin a) => dot x (v (js i))
      ∃ enc dec, a*N ≤ gain t enc dec ∧
        b*(m-a)*N^2 ≤ 6*(gain t enc dec - a*N)^2) := by
  intro k m a b hab
  dsimp only
  intro v c hindep
  exact ⟨fun t hflat enc dec => PEqualNP.Outside.L_meta_27811_aux.part1_upper v c hindep t hflat enc dec,
    PEqualNP.Outside.L_meta_27811_aux.part2_lower hab v c⟩
