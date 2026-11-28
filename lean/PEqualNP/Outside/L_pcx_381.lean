import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_381

private abbrev Vec (n : ℕ) := Fin n → ZMod 2
private abbrev Dual (n : ℕ) := Vec n →ₗ[ZMod 2] ZMod 2

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_eq_iff_add_eq_zero (a b : ZMod 2) : a = b ↔ a + b = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact False.elim (ha rfl)
  · rfl

private def Ddual {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) : Dual n →ₗ[ZMod 2] Dual n where
  toFun a := a.comp T.toLinearMap + a
  map_add' a₁ a₂ := by ext x; simp; ring
  map_smul' c a := by ext x; simp

private def Dprimal {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) : Vec n →ₗ[ZMod 2] Vec n :=
  T.toLinearMap + LinearMap.id

private def transpose {n : ℕ} (L : Vec n →ₗ[ZMod 2] Vec n) : Dual n →ₗ[ZMod 2] Dual n where
  toFun a := a.comp L
  map_add' a₁ a₂ := by apply LinearMap.ext; intro x; simp
  map_smul' c a := by apply LinearMap.ext; intro x; simp

private lemma Ddual_eq_transpose {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) :
    Ddual T = transpose (Dprimal T) := by
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro x
  simp [Ddual, Dprimal, transpose]

private lemma transpose_comp {n : ℕ} (L₁ L₂ : Vec n →ₗ[ZMod 2] Vec n) :
    transpose (L₁.comp L₂) = (transpose L₂).comp (transpose L₁) := by
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro x
  simp [transpose]

private lemma transpose_pow {n : ℕ} (L : Vec n →ₗ[ZMod 2] Vec n) (k : ℕ) :
    (transpose L) ^ k = transpose (L ^ k) := by
  induction k with
  | zero =>
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro x
    simp [transpose]
  | succ k ih =>
    rw [pow_succ', pow_succ, ih]
    change (transpose L).comp (transpose (L ^ k)) = transpose ((L ^ k).comp L)
    rw [transpose_comp]

private lemma transpose_aeval {n : ℕ} (L : Vec n →ₗ[ZMod 2] Vec n) (p : Polynomial (ZMod 2)) :
    Polynomial.aeval (transpose L) p = transpose (Polynomial.aeval L p) := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [map_add, map_add, ihp, ihq]
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro x
    simp [transpose]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, map_smul,
      smul_mul_assoc, one_mul, transpose_pow]
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro x
    simp [transpose]

private lemma shift_eq_map {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (S : Submodule (ZMod 2) (Dual n)) :
    Submodule.span (ZMod 2) (Set.image (fun a : Dual n => a.comp T.toLinearMap + a) (S : Set (Dual n))) =
      S.map (Ddual T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨a, ha, rfl⟩

private def Ann {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) : Submodule (ZMod 2) (Vec n) :=
  { carrier := {v | ∀ φ ∈ M, φ v = 0}, zero_mem' := fun φ _ => map_zero φ, add_mem' := fun {u v} hu hv φ hφ => by rw [map_add, hu φ hφ, hv φ hφ, add_zero], smul_mem' := fun c {v} hv φ hφ => by rw [map_smul, hv φ hφ, smul_zero] }

private lemma mem_Ann_iff {n : ℕ} {M : Submodule (ZMod 2) (Dual n)} {v : Vec n} :
    v ∈ Ann M ↔ ∀ φ ∈ M, φ v = 0 := Iff.rfl

private lemma mem_Ann_sup {n : ℕ} {M₁ M₂ : Submodule (ZMod 2) (Dual n)} {v : Vec n} :
    v ∈ Ann (M₁ ⊔ M₂) ↔ v ∈ Ann M₁ ∧ v ∈ Ann M₂ := by
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (Submodule.mem_sup_left hφ),
      fun φ hφ => h φ (Submodule.mem_sup_right hφ)⟩
  · rintro ⟨h1, h2⟩ φ hφ
    rcases Submodule.mem_sup.mp hφ with ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩
    rw [LinearMap.add_apply, h1 φ₁ hφ₁, h2 φ₂ hφ₂, add_zero]

private lemma mem_Ann_span {n : ℕ} {s : Set (Dual n)} {v : Vec n} :
    v ∈ Ann (Submodule.span (ZMod 2) s) ↔ ∀ φ ∈ s, φ v = 0 := by
  constructor
  · intro h φ hφ; exact h φ (Submodule.subset_span hφ)
  · intro h φ hφ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
    · intro ψ hψ; exact h ψ hψ
    · simp
    · intro ψ₁ ψ₂ _ _ h1 h2; simp [h1, h2]
    · intro c ψ _ h1; simp [h1]

private lemma mem_Ann_map_Ddual {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    {M : Submodule (ZMod 2) (Dual n)} {v : Vec n} :
    v ∈ Ann (M.map (Ddual T)) ↔ ∀ φ ∈ M, Ddual T φ v = 0 := by
  constructor
  · intro h φ hφ; exact h (Ddual T φ) ⟨φ, hφ, rfl⟩
  · intro h _ hψ
    rcases hψ with ⟨φ, hφ, rfl⟩
    exact h φ hφ

private lemma Ann_top_eq_bot {n : ℕ} :
    Ann (⊤ : Submodule (ZMod 2) (Dual n)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  ext i
  exact hv (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i) Submodule.mem_top

private lemma dual_eq_sum_proj {n : ℕ} (φ : Dual n) :
    φ = ∑ i : Fin n, φ (Pi.single i (1 : ZMod 2)) •
      LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, map_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private def evalSub {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Vec n →ₗ[ZMod 2] (M →ₗ[ZMod 2] ZMod 2) where
  toFun v :=
    { toFun := fun φ => φ.1 v
      map_add' := fun φ₁ φ₂ => rfl
      map_smul' := fun c φ => rfl }
  map_add' u v := by ext φ; exact map_add φ.1 u v
  map_smul' c v := by ext φ; exact map_smul φ.1 c v

private lemma evalSub_ker {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    LinearMap.ker (evalSub M) = Ann M := by
  ext v
  simp only [LinearMap.mem_ker, mem_Ann_iff]
  constructor
  · intro h φ hφ
    exact LinearMap.congr_fun h ⟨φ, hφ⟩
  · intro h
    ext ⟨φ, hφ⟩
    exact h φ hφ

private lemma evalSub_surjective {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Function.Surjective (evalSub M) := by
  intro ψ
  rcases Submodule.exists_isCompl M with ⟨N, hMN⟩
  let projM : Dual n →ₗ[ZMod 2] M := Submodule.linearProjOfIsCompl M N hMN
  let Ψ : Dual n →ₗ[ZMod 2] ZMod 2 := ψ.comp projM
  let v : Vec n := fun i => Ψ (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i)
  refine ⟨v, ?_⟩
  ext ⟨φ, hφ⟩
  change φ v = ψ ⟨φ, hφ⟩
  have hΨφ : Ψ φ = ψ ⟨φ, hφ⟩ := by
    change ψ (Submodule.linearProjOfIsCompl M N hMN φ) = ψ ⟨φ, hφ⟩
    congr 1
    exact Submodule.linearProjOfIsCompl_apply_left hMN ⟨φ, hφ⟩
  rw [← hΨφ]
  conv_rhs => rw [dual_eq_sum_proj φ, map_sum]
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only [v]
  ring

private lemma finrank_Ann_add_finrank {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Module.finrank (ZMod 2) (Ann M) + Module.finrank (ZMod 2) M = n := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (evalSub M)
  rw [LinearMap.range_eq_top.mpr (evalSub_surjective M), evalSub_ker M,
    finrank_top, Module.finrank_fin_fun] at hrk
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  have hdual : Module.finrank (ZMod 2) (M →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) M := by
    rw [Module.finrank_eq_card_basis (Module.finBasis (ZMod 2) M).dualBasis, Fintype.card_fin]
  omega

private lemma finrank_dual_le {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Module.finrank (ZMod 2) M ≤ n := by
  have := finrank_Ann_add_finrank M
  omega

private lemma finrank_range_transpose {n : ℕ} (L : Vec n →ₗ[ZMod 2] Vec n) :
    Module.finrank (ZMod 2) (LinearMap.range (transpose L)) =
      Module.finrank (ZMod 2) (LinearMap.range L) := by
  have hAnn : Ann (LinearMap.range (transpose L)) = LinearMap.ker L := by
    ext v
    simp only [mem_Ann_iff, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff]
    constructor
    · intro h
      have hv : L v ∈ Ann (⊤ : Submodule (ZMod 2) (Dual n)) := fun a _ => h a
      rw [Ann_top_eq_bot] at hv
      exact (Submodule.mem_bot (ZMod 2)).mp hv
    · intro h a
      change a (L v) = 0
      rw [h, map_zero]
  have h1 := finrank_Ann_add_finrank (LinearMap.range (transpose L))
  rw [hAnn] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_fin_fun] at h2
  omega

private lemma finrank_range_inf_ker {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g : V →ₗ[K] V) :
    Module.finrank K (LinearMap.range g ⊓ LinearMap.ker f : Submodule K V) +
      Module.finrank K (LinearMap.range (f.comp g)) =
      Module.finrank K (LinearMap.range g) := by
  let h : LinearMap.range g →ₗ[K] V := f.comp (LinearMap.range g).subtype
  have hrk := LinearMap.finrank_range_add_finrank_ker h
  have hrange : LinearMap.range h = LinearMap.range (f.comp g) := by
    ext y
    simp only [h, LinearMap.mem_range, LinearMap.comp_apply, Submodule.coe_subtype, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨g x, ⟨x, rfl⟩, rfl⟩
  have hker : Module.finrank K (LinearMap.ker h) =
      Module.finrank K (LinearMap.range g ⊓ LinearMap.ker f : Submodule K V) := by
    let e : LinearMap.ker h ≃ₗ[K] (LinearMap.range g ⊓ LinearMap.ker f : Submodule K V) :=
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  rw [hrange, hker] at hrk
  omega

private lemma end_mul_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] V) (x : V) : (f * g) x = f (g x) := rfl

private lemma end_one_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (x : V) : (1 : V →ₗ[K] V) x = x := rfl

private lemma map_map_end {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] V) (S : Submodule K V) :
    (S.map f).map g = S.map (g * f) :=
  (Submodule.map_comp f g S).symm

private lemma finrank_W_dual_eq {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (s : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range ((Ddual T) ^ s)) =
      Module.finrank (ZMod 2) (LinearMap.range ((Dprimal T) ^ s)) := by
  rw [Ddual_eq_transpose, transpose_pow, finrank_range_transpose]

private lemma transpose_socle_finrank {n s : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (p : Polynomial (ZMod 2)) :
    Module.finrank (ZMod 2)
        (LinearMap.range ((Ddual T) ^ s) ⊓ LinearMap.ker (Polynomial.aeval (Ddual T) p) :
          Submodule (ZMod 2) (Dual n)) =
      Module.finrank (ZMod 2)
        (LinearMap.range ((Dprimal T) ^ s) ⊓ LinearMap.ker (Polynomial.aeval (Dprimal T) p) :
          Submodule (ZMod 2) (Vec n)) := by
  have h1 := finrank_range_inf_ker (Polynomial.aeval (Ddual T) p) ((Ddual T) ^ s)
  have h2 := finrank_range_inf_ker (Polynomial.aeval (Dprimal T) p) ((Dprimal T) ^ s)
  have hrW := finrank_W_dual_eq T s
  have hrComp : Module.finrank (ZMod 2)
        (LinearMap.range ((Polynomial.aeval (Ddual T) p).comp ((Ddual T) ^ s))) =
      Module.finrank (ZMod 2)
        (LinearMap.range ((Polynomial.aeval (Dprimal T) p).comp ((Dprimal T) ^ s))) := by
    have hcomm : (Polynomial.aeval (Ddual T) p).comp ((Ddual T) ^ s) =
        ((Ddual T) ^ s).comp (Polynomial.aeval (Ddual T) p) := by
      have hpow : (Ddual T) ^ s = Polynomial.aeval (Ddual T) ((Polynomial.X : Polynomial (ZMod 2)) ^ s) := by simp
      rw [hpow]
      change Polynomial.aeval (Ddual T) p * Polynomial.aeval (Ddual T) ((Polynomial.X : Polynomial (ZMod 2)) ^ s) =
        Polynomial.aeval (Ddual T) ((Polynomial.X : Polynomial (ZMod 2)) ^ s) * Polynomial.aeval (Ddual T) p
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hcomm, Ddual_eq_transpose, transpose_pow, transpose_aeval, ← transpose_comp,
      finrank_range_transpose]
  omega

open Classical in
private lemma card_coset_Ann {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) (x₀ : Vec n) :
    (Finset.univ.filter (fun x : Vec n => x - x₀ ∈ Ann M)).card =
      2 ^ (n - Module.finrank (ZMod 2) M) := by
  have hbij : (Finset.univ.filter (fun x : Vec n => x - x₀ ∈ Ann M)).card =
      Fintype.card (Ann M) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x hx => ⟨x - x₀, (Finset.mem_filter.mp hx).2⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ _ x₂ _ heq => by
        have h : x₁ - x₀ = x₂ - x₀ := congrArg Subtype.val heq
        exact sub_left_inj.mp h)
      (fun v _ => ⟨v.1 + x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [v.2]⟩,
        by ext; simp⟩)
  rw [hbij, Module.card_eq_pow_finrank (K := ZMod 2) (V := Ann M), ZMod.card 2]
  have hsum := finrank_Ann_add_finrank M
  congr 1
  omega

private def step {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (hist : List (Fin w → ZMod 2)) :
    List (Fin w → ZMod 2) :=
  hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]

private def tr {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) : ℕ → List (Fin w → ZMod 2)
  | 0 => []
  | j + 1 => step ask layer word (tr ask layer word j)

private lemma tr_eq_foldl {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (s : ℕ) :
    (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
      hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) [] =
      tr ask layer word s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [List.range_succ, List.foldl_concat, ih]
    rfl

private lemma tr_length {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (j : ℕ) :
    (tr ask layer word j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [tr, step, ih]

private lemma tr_take {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (j : ℕ) :
    (tr ask layer word (j + 1)).take j = tr ask layer word j := by
  change (tr ask layer word j ++ [_]).take j = tr ask layer word j
  rw [List.take_left' (tr_length ask layer word j)]

private lemma tr_take_le {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) {r j : ℕ} (hrj : r ≤ j) :
    (tr ask layer word j).take r = tr ask layer word r := by
  induction j with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0; rfl
  | succ j ih =>
    by_cases h : r = j + 1
    · subst h; rw [List.take_of_length_le (by rw [tr_length])]
    · have hrle : r ≤ j := by omega
      rw [← ih hrle, ← tr_take ask layer word j, List.take_take, Nat.min_eq_left hrle]

private lemma tr_succ_eq_iff {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (j : ℕ)
    (h : List (Fin w → ZMod 2)) (hlen : h.length = j) (y : Fin w → ZMod 2) :
    tr ask layer word (j + 1) = h ++ [y] ↔
      tr ask layer word j = h ∧
      (fun i : Fin w => (ask h i).1 word + (ask h i).2.1 * layer + (ask h i).2.2) = y := by
  change tr ask layer word j ++
      [fun i : Fin w => (ask (tr ask layer word j) i).1 word +
        (ask (tr ask layer word j) i).2.1 * layer + (ask (tr ask layer word j) i).2.2] =
      h ++ [y] ↔ _
  constructor
  · intro heq
    have h1 : tr ask layer word j = h := by
      have ht := congrArg (List.take j) heq
      rw [List.take_left' (tr_length ask layer word j), List.take_left' hlen] at ht
      exact ht
    rw [h1] at heq
    have h2 : [fun i : Fin w => (ask h i).1 word + (ask h i).2.1 * layer + (ask h i).2.2] = [y] :=
      List.append_cancel_left heq
    exact ⟨h1, (List.cons.inj h2).1⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

private lemma layer_agree_iff {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (a : Dual n) (c₁ c₂ : ZMod 2) (x : Vec n) :
    (a x + c₁ * 0 + c₂ = a (T x + b) + c₁ * 1 + c₂) ↔
      Ddual T a x = a b + c₁ := by
  simp only [mul_zero, add_zero, mul_one, map_add, add_left_inj]
  change a x = a (T x) + a b + c₁ ↔ a (T x) + a x = a b + c₁
  rw [zmod2_eq_iff_add_eq_zero (a x), zmod2_eq_iff_add_eq_zero (a (T x) + a x)]
  have hring : a x + (a (T x) + a b + c₁) = a (T x) + a x + (a b + c₁) := by ring
  rw [hring]

private def Hists (w : ℕ) : ℕ → Finset (List (Fin w → ZMod 2))
  | 0 => {[]}
  | j + 1 => (Hists w j).biUnion (fun h => Finset.univ.image (fun y : Fin w → ZMod 2 => h ++ [y]))

private lemma mem_Hists_iff {w j : ℕ} {h : List (Fin w → ZMod 2)} :
    h ∈ Hists w j ↔ h.length = j := by
  induction j generalizing h with
  | zero => simp [Hists]
  | succ j ih =>
    simp only [Hists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, ih]
    constructor
    · rintro ⟨h', hh', y, rfl⟩; simp [hh']
    · intro hlen
      have hne : h ≠ [] := by intro h0; subst h0; simp at hlen
      refine ⟨h.dropLast, ?_, h.getLast hne, List.dropLast_append_getLast hne⟩
      simp [hlen]

private lemma sum_Hists_succ {w j : ℕ} (f : List (Fin w → ZMod 2) → ℕ) :
    ∑ h' ∈ Hists w (j + 1), f h' =
      ∑ h ∈ Hists w j, ∑ y : Fin w → ZMod 2, f (h ++ [y]) := by
  change ∑ h' ∈ (Hists w j).biUnion (fun h => Finset.univ.image (fun y => h ++ [y])), f h' = _
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.sum_image]
    intro y₁ _ y₂ _ heq
    exact (List.cons.inj (List.append_cancel_left heq)).1
  · intro h₁ hh₁ h₂ hh₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨y₁, _, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨y₂, _, heq⟩
    have hl1 : h₁.length = j := mem_Hists_iff.mp hh₁
    have hl2 : h₂.length = j := mem_Hists_iff.mp hh₂
    have ht := congrArg (List.take j) heq
    rw [List.take_left' hl1, List.take_left' hl2] at ht
    exact hne ht.symm

private def roundSpace {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) : Submodule (ZMod 2) (Dual n) :=
  Submodule.span (ZMod 2) (Set.range (fun i : Fin w => (ask h i).1))

private def histFlag {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) : ℕ → Submodule (ZMod 2) (Dual n)
  | 0 => ⊥
  | j + 1 => histFlag ask h j ⊔ roundSpace ask (h.take j)

private lemma histFlag_eq_of_take {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h₁ h₂ : List (Fin w → ZMod 2)) (j : ℕ) (ht : h₁.take j = h₂.take j) :
    histFlag ask h₁ j = histFlag ask h₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hprev : h₁.take j = h₂.take j := by
      have := congrArg (List.take j) ht
      rwa [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_succ j)] at this
    simp only [histFlag, ih hprev, hprev]

private lemma histFlag_append {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) (y : Fin w → ZMod 2) (j : ℕ) (hlen : h.length = j) :
    histFlag ask (h ++ [y]) (j + 1) = histFlag ask h j ⊔ roundSpace ask h := by
  simp only [histFlag]
  have ht : (h ++ [y]).take j = h := List.take_left' hlen
  have htake : (h ++ [y]).take j = h.take j := by
    rw [ht, List.take_of_length_le (le_of_eq hlen)]
  rw [histFlag_eq_of_take ask (h ++ [y]) h j htake, ht]

private noncomputable def stepCost {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (A B : Submodule (ZMod 2) (Dual n)) : ℕ :=
  let base := A ⊔ A.map (Ddual T)
  Module.finrank (ZMod 2) (base ⊔ B.map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
    Module.finrank (ZMod 2) base

private noncomputable def histCost {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => histCost T ask h j +
      stepCost T (histFlag ask h j) (histFlag ask h (j + 1))

private lemma histCost_eq_of_take {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h₁ h₂ : List (Fin w → ZMod 2)) (j : ℕ) (ht : h₁.take j = h₂.take j) :
    histCost T ask h₁ j = histCost T ask h₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hprev : h₁.take j = h₂.take j := by
      have := congrArg (List.take j) ht
      rwa [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_succ j)] at this
    simp only [histCost, ih hprev, histFlag_eq_of_take ask h₁ h₂ j hprev,
      histFlag_eq_of_take ask h₁ h₂ (j + 1) ht]

private lemma histCost_eq_range_sum {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) (s : ℕ) :
    histCost T ask h s =
      (Finset.range s).sum (fun j => stepCost T (histFlag ask h j) (histFlag ask h (j + 1))) := by
  induction s with
  | zero => simp [histCost]
  | succ s ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

private lemma surv_coset_iff {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (j : ℕ) (h : List (Fin w → ZMod 2)) (hlen : h.length = j)
    (x₀ : Vec n) (hx₀ : tr ask 0 x₀ j = h ∧ tr ask 1 (T x₀ + b) j = h) :
    ∀ x : Vec n, (tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h) ↔
      x - x₀ ∈ Ann (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) := by
  induction j generalizing h with
  | zero =>
    have hnil : h = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    intro x
    simp [tr, histFlag, Ann]
  | succ j ih =>
    have hne : h ≠ [] := by intro h0; subst h0; simp at hlen
    set h' := h.dropLast
    set y := h.getLast hne
    have hcat : h = h' ++ [y] := (List.dropLast_append_getLast hne).symm
    have h'len : h'.length = j := by simp [h', hlen]
    have hx₀_split : (tr ask 0 x₀ j = h' ∧
        (fun i => (ask h' i).1 x₀ + (ask h' i).2.1 * 0 + (ask h' i).2.2) = y) ∧
        (tr ask 1 (T x₀ + b) j = h' ∧
        (fun i => (ask h' i).1 (T x₀ + b) + (ask h' i).2.1 * 1 + (ask h' i).2.2) = y) := by
      rw [hcat] at hx₀
      exact ⟨(tr_succ_eq_iff ask 0 x₀ j h' h'len y).mp hx₀.1,
        (tr_succ_eq_iff ask 1 (T x₀ + b) j h' h'len y).mp hx₀.2⟩
    have hx₀_prev : tr ask 0 x₀ j = h' ∧ tr ask 1 (T x₀ + b) j = h' :=
      ⟨hx₀_split.1.1, hx₀_split.2.1⟩
    have hx₀_agree : ∀ i : Fin w, Ddual T (ask h' i).1 x₀ = (ask h' i).1 b + (ask h' i).2.1 := by
      intro i
      rw [← layer_agree_iff T b (ask h' i).1 (ask h' i).2.1 (ask h' i).2.2 x₀]
      exact (congrFun hx₀_split.1.2 i).trans (congrFun hx₀_split.2.2 i).symm
    have hflag_eq : histFlag ask h (j + 1) = histFlag ask h' j ⊔ roundSpace ask h' := by
      rw [hcat]
      exact histFlag_append ask h' y j h'len
    intro x
    rw [hflag_eq, Submodule.map_sup]
    have hsup_rearr : (histFlag ask h' j ⊔ roundSpace ask h') ⊔
        ((histFlag ask h' j).map (Ddual T) ⊔ (roundSpace ask h').map (Ddual T)) =
        (histFlag ask h' j ⊔ (histFlag ask h' j).map (Ddual T)) ⊔
        (roundSpace ask h' ⊔ (roundSpace ask h').map (Ddual T)) := by ac_rfl
    rw [hsup_rearr, mem_Ann_sup, ← ih h' h'len hx₀_prev x, hcat,
      tr_succ_eq_iff ask 0 x j h' h'len y, tr_succ_eq_iff ask 1 (T x + b) j h' h'len y]
    rw [mem_Ann_sup, roundSpace, mem_Ann_span, mem_Ann_map_Ddual]
    constructor
    · rintro ⟨⟨h0p, h0y⟩, ⟨h1p, h1y⟩⟩
      refine ⟨⟨h0p, h1p⟩, ?_, ?_⟩
      · rintro _ ⟨i, rfl⟩
        have e1 := congrFun h0y i
        have e2 := congrFun hx₀_split.1.2 i
        have hax : (ask h' i).1 x = (ask h' i).1 x₀ := by
          simp only [mul_zero, add_zero] at e1 e2
          exact add_right_cancel (e1.trans e2.symm)
        rw [map_sub, hax, sub_self]
      · intro φ hφ
        have hker : ∀ i : Fin w, Ddual T (ask h' i).1 (x - x₀) = 0 := by
          intro i
          have hax_ag : Ddual T (ask h' i).1 x = (ask h' i).1 b + (ask h' i).2.1 := by
            rw [← layer_agree_iff T b (ask h' i).1 (ask h' i).2.1 (ask h' i).2.2 x]
            exact (congrFun h0y i).trans (congrFun h1y i).symm
          rw [map_sub, hax_ag, hx₀_agree i, sub_self]
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
        · rintro _ ⟨i, rfl⟩; exact hker i
        · simp
        · intro ψ₁ ψ₂ _ _ h1 h2; simp [h1, h2]
        · intro c ψ _ h1; simp [h1]
    · rintro ⟨⟨h0p, h1p⟩, hR0, hRD⟩
      have h0y : (fun i => (ask h' i).1 x + (ask h' i).2.1 * 0 + (ask h' i).2.2) = y := by
        ext i
        have hsub : (ask h' i).1 (x - x₀) = 0 := hR0 _ ⟨i, rfl⟩
        have hax : (ask h' i).1 x = (ask h' i).1 x₀ := sub_eq_zero.mp (by rwa [map_sub] at hsub)
        rw [hax]
        exact congrFun hx₀_split.1.2 i
      have h1y : (fun i => (ask h' i).1 (T x + b) + (ask h' i).2.1 * 1 + (ask h' i).2.2) = y := by
        ext i
        have hsub : Ddual T (ask h' i).1 (x - x₀) = 0 :=
          hRD (ask h' i).1 (Submodule.subset_span ⟨i, rfl⟩)
        have hd : Ddual T (ask h' i).1 x = (ask h' i).1 b + (ask h' i).2.1 := by
          rw [← hx₀_agree i]
          exact sub_eq_zero.mp (by rwa [map_sub] at hsub)
        have hag := (layer_agree_iff T b (ask h' i).1 (ask h' i).2.1 (ask h' i).2.2 x).mpr hd
        rw [← hag]
        exact congrFun h0y i
      exact ⟨⟨h0p, h0y⟩, ⟨h1p, h1y⟩⟩

private lemma agree_next_coset_iff {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (j : ℕ) (h : List (Fin w → ZMod 2)) (hlen : h.length = j)
    (x₁ : Vec n)
    (hx₁ : tr ask 0 x₁ j = h ∧ tr ask 1 (T x₁ + b) j = h ∧
      (fun i : Fin w => (ask h i).1 x₁ + (ask h i).2.1 * 0 + (ask h i).2.2) =
      (fun i : Fin w => (ask h i).1 (T x₁ + b) + (ask h i).2.1 * 1 + (ask h i).2.2)) :
    ∀ x : Vec n,
      (tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h ∧
        (fun i : Fin w => (ask h i).1 x + (ask h i).2.1 * 0 + (ask h i).2.2) =
        (fun i : Fin w => (ask h i).1 (T x + b) + (ask h i).2.1 * 1 + (ask h i).2.2)) ↔
      x - x₁ ∈ Ann ((histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔
        (roundSpace ask h).map (Ddual T)) := by
  have hx₁_ag : ∀ i : Fin w, Ddual T (ask h i).1 x₁ = (ask h i).1 b + (ask h i).2.1 := by
    intro i
    rw [← layer_agree_iff T b (ask h i).1 (ask h i).2.1 (ask h i).2.2 x₁]
    exact congrFun hx₁.2.2 i
  intro x
  rw [mem_Ann_sup, ← surv_coset_iff T b ask j h hlen x₁ ⟨hx₁.1, hx₁.2.1⟩ x, mem_Ann_map_Ddual]
  constructor
  · rintro ⟨h0, h1, hag⟩
    refine ⟨⟨h0, h1⟩, ?_⟩
    intro φ hφ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨i, rfl⟩
      have hd : Ddual T (ask h i).1 x = (ask h i).1 b + (ask h i).2.1 := by
        rw [← layer_agree_iff T b (ask h i).1 (ask h i).2.1 (ask h i).2.2 x]
        exact congrFun hag i
      rw [map_sub, hd, hx₁_ag i, sub_self]
    · simp
    · intro ψ₁ ψ₂ _ _ h1' h2'; simp [h1', h2']
    · intro c ψ _ h1'; simp [h1']
  · rintro ⟨⟨h0, h1⟩, hRD⟩
    refine ⟨h0, h1, ?_⟩
    ext i
    rw [layer_agree_iff T b (ask h i).1 (ask h i).2.1 (ask h i).2.2 x]
    have hsub : Ddual T (ask h i).1 (x - x₁) = 0 :=
      hRD (ask h i).1 (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hx₁_ag i]
    exact sub_eq_zero.mp (by rwa [map_sub] at hsub)

open Classical in
private lemma children_card_mul_pow_le {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (j : ℕ) (h : List (Fin w → ZMod 2)) (hlen : h.length = j) :
    (∑ y : Fin w → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
      2 ^ (stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h)) ≤
    (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card := by
  set Surv := Finset.univ.filter (fun x : Vec n =>
    tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h ∧
    (fun i : Fin w => (ask h i).1 x + (ask h i).2.1 * 0 + (ask h i).2.2) =
    (fun i : Fin w => (ask h i).1 (T x + b) + (ask h i).2.1 * 1 + (ask h i).2.2))
  set Parent := Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)
  have hsum_eq : ∑ y : Fin w → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card = Surv.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Surv, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        tr_succ_eq_iff ask 0 x j h hlen, tr_succ_eq_iff ask 1 (T x + b) j h hlen]
      constructor
      · rintro ⟨y, ⟨h0, hy0⟩, ⟨h1, hy1⟩⟩; exact ⟨h0, h1, hy0.trans hy1.symm⟩
      · rintro ⟨h0, h1, hag⟩; exact ⟨_, ⟨h0, rfl⟩, ⟨h1, hag.symm⟩⟩
    · intro y₁ _ y₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have h1 := ((tr_succ_eq_iff ask 0 x j h hlen y₁).mp (Finset.mem_filter.mp hx₁).2.1).2
      have h2 := ((tr_succ_eq_iff ask 0 x j h hlen y₂).mp (Finset.mem_filter.mp hx₂).2.1).2
      exact hne (h1.symm.trans h2)
  rw [hsum_eq]
  by_cases hne : Surv.Nonempty
  · rcases hne with ⟨x₁, hx₁⟩
    have hx₁' := (Finset.mem_filter.mp hx₁).2
    have hSurv_eq : Surv = Finset.univ.filter (fun x : Vec n =>
        x - x₁ ∈ Ann ((histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔
          (roundSpace ask h).map (Ddual T))) := by
      ext x
      simp only [Surv, Finset.mem_filter, Finset.mem_univ, true_and]
      exact agree_next_coset_iff T b ask j h hlen x₁ hx₁' x
    have hParent_eq : Parent = Finset.univ.filter (fun x : Vec n =>
        x - x₁ ∈ Ann (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T))) := by
      ext x
      simp only [Parent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact surv_coset_iff T b ask j h hlen x₁ ⟨hx₁'.1, hx₁'.2.1⟩ x
    rw [hSurv_eq, hParent_eq, card_coset_Ann, card_coset_Ann]
    set base := histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)
    have hstep_eq : stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h) =
        Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
          Module.finrank (ZMod 2) base := by
      unfold stepCost
      dsimp only
      have heq : base ⊔ (histFlag ask h j ⊔ roundSpace ask h).map (Ddual T) =
          base ⊔ (roundSpace ask h).map (Ddual T) := by
        rw [Submodule.map_sup]
        change (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔
            ((histFlag ask h j).map (Ddual T) ⊔ (roundSpace ask h).map (Ddual T)) =
            (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔ (roundSpace ask h).map (Ddual T)
        apply le_antisymm
        · refine sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
        · exact sup_le le_sup_left (le_sup_of_le_right le_sup_right)
      rw [heq]
    rw [hstep_eq, ← pow_add]
    have hle1 : Module.finrank (ZMod 2) base ≤
        Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) :=
      Submodule.finrank_mono le_sup_left
    have hle2 : Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) ≤ n :=
      finrank_dual_le _
    have hexp : n - Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) +
        (Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
          Module.finrank (ZMod 2) base) = n - Module.finrank (ZMod 2) base := by omega
    rw [hexp]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

open Classical in
private lemma weighted_sum_le {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2) (j : ℕ) :
    ∑ h ∈ Hists w j,
      (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card *
        2 ^ (histCost T ask h j) ≤ 2 ^ n := by
  induction j with
  | zero =>
    simp only [Hists, Finset.sum_singleton, histCost, pow_zero, mul_one, tr, true_and,
      Finset.filter_true, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
      ZMod.card 2, Finset.prod_const]
    exact le_rfl
  | succ j ih =>
    rw [sum_Hists_succ]
    refine le_trans ?_ ih
    refine Finset.sum_le_sum (fun h hh => ?_)
    have hlen : h.length = j := mem_Hists_iff.mp hh
    have hcost : ∀ y : Fin w → ZMod 2,
        histCost T ask (h ++ [y]) (j + 1) =
          histCost T ask h j + stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h) := by
      intro y
      simp only [histCost]
      have htake : (h ++ [y]).take j = h.take j := by
        rw [List.take_left' hlen, List.take_of_length_le (le_of_eq hlen)]
      rw [histCost_eq_of_take T ask (h ++ [y]) h j htake,
        histFlag_eq_of_take ask (h ++ [y]) h j htake,
        histFlag_append ask h y j hlen]
    calc ∑ y : Fin w → ZMod 2,
          (Finset.univ.filter (fun x : Vec n =>
            tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card *
          2 ^ histCost T ask (h ++ [y]) (j + 1)
        = ∑ y : Fin w → ZMod 2,
          (Finset.univ.filter (fun x : Vec n =>
            tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card *
          (2 ^ stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h) *
            2 ^ histCost T ask h j) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hcost y, pow_add, mul_comm (2 ^ histCost T ask h j)]
      _ = ((∑ y : Fin w → ZMod 2,
            (Finset.univ.filter (fun x : Vec n =>
              tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
            2 ^ stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h)) *
          2 ^ histCost T ask h j := by
          simp_rw [← mul_assoc, ← Finset.sum_mul]
      _ ≤ (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card *
          2 ^ histCost T ask h j :=
          Nat.mul_le_mul_right _ (children_card_mul_pow_le T b ask j h hlen)

private lemma tr_eq_of_ann_histFlag {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (x₀ v : Vec n) (s : ℕ)
    (hv : v ∈ Ann (histFlag ask (tr ask layer x₀ s) s)) :
    ∀ j ≤ s, tr ask layer (x₀ + v) j = tr ask layer x₀ j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hjs
    have hprev : tr ask layer (x₀ + v) j = tr ask layer x₀ j := ih (by omega)
    change step ask layer (x₀ + v) (tr ask layer (x₀ + v) j) = step ask layer x₀ (tr ask layer x₀ j)
    rw [hprev]
    unfold step
    congr 1; congr 1; ext i
    have hstep_le : ∀ a b, a ≤ b → histFlag ask (tr ask layer x₀ s) a ≤ histFlag ask (tr ask layer x₀ s) b := by
      intro a b hab
      induction b with
      | zero =>
        have ha0 : a = 0 := by omega
        subst ha0; exact le_rfl
      | succ b ihb =>
        by_cases h : a = b + 1
        · subst h; exact le_rfl
        · exact (ihb (by omega)).trans le_sup_left
    have hmem : (ask (tr ask layer x₀ j) i).1 ∈ histFlag ask (tr ask layer x₀ s) s := by
      have h1 : (ask ((tr ask layer x₀ s).take j) i).1 ∈ histFlag ask (tr ask layer x₀ s) (j + 1) :=
        Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
      rw [tr_take_le ask layer x₀ (by omega : j ≤ s)] at h1
      exact hstep_le (j + 1) s hjs h1
    have hzero : (ask (tr ask layer x₀ j) i).1 v = 0 := hv _ hmem
    rw [map_add, hzero, add_zero]

private lemma histFlag_top_of_injective {n w s : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (hinj : Function.Injective (fun x : Vec n => tr ask 0 x s))
    (x₀ : Vec n) :
    histFlag ask (tr ask 0 x₀ s) s = ⊤ := by
  by_contra hne
  have hlt : Module.finrank (ZMod 2) (histFlag ask (tr ask 0 x₀ s) s) < n := by
    have hle := finrank_dual_le (histFlag ask (tr ask 0 x₀ s) s)
    by_contra hge
    have heq : Module.finrank (ZMod 2) (histFlag ask (tr ask 0 x₀ s) s) =
        Module.finrank (ZMod 2) (Dual n) := by
      have hd : Module.finrank (ZMod 2) (Dual n) = n := by
        have h := finrank_Ann_add_finrank (⊤ : Submodule (ZMod 2) (Dual n))
        rw [Ann_top_eq_bot, finrank_bot, finrank_top] at h
        omega
      omega
    exact hne (Submodule.eq_top_of_finrank_eq heq)
  have hAnn_pos : 0 < Module.finrank (ZMod 2) (Ann (histFlag ask (tr ask 0 x₀ s) s)) := by
    have := finrank_Ann_add_finrank (histFlag ask (tr ask 0 x₀ s) s)
    omega
  have hAnn_ne_bot : Ann (histFlag ask (tr ask 0 x₀ s) s) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hAnn_pos
    omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hAnn_ne_bot with ⟨v, hv, hv0⟩
  have htr : tr ask 0 (x₀ + v) s = tr ask 0 x₀ s :=
    tr_eq_of_ann_histFlag ask 0 x₀ v s hv s le_rfl
  have heq : x₀ + v = x₀ := hinj htr
  exact hv0 (add_left_cancel (heq.trans (add_zero x₀).symm))

private noncomputable def spanGenerators {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) : Fin n → Dual n :=
  letI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  let e := Module.finBasis (ZMod 2) M
  fun i => if hi : i.val < Module.finrank (ZMod 2) M then (e ⟨i.val, hi⟩).1 else 0

private lemma span_spanGenerators {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Submodule.span (ZMod 2) (Set.range (spanGenerators M)) = M := by
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    unfold spanGenerators
    split_ifs with hi
    · exact (Module.finBasis (ZMod 2) M ⟨i.val, hi⟩).2
    · exact M.zero_mem
  · intro φ hφ
    let e := Module.finBasis (ZMod 2) M
    have hle : Module.finrank (ZMod 2) M ≤ n := finrank_dual_le M
    have hrep := e.sum_repr ⟨φ, hφ⟩
    have hval : φ = ∑ k : Fin (Module.finrank (ZMod 2) M), (e.repr ⟨φ, hφ⟩ k) • (e k).1 := by
      have := congrArg Subtype.val hrep
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
    rw [hval]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    refine Submodule.subset_span ⟨⟨k.val, lt_of_lt_of_le k.isLt hle⟩, ?_⟩
    unfold spanGenerators
    dsimp only
    rw [dif_pos k.isLt]

open Classical in
private noncomputable def askUpTo {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) :
    ℕ → (List (Fin n → ZMod 2) → Fin n → Dual n × ZMod 2 × ZMod 2)
  | 0 => fun _ _ => (0, 0, 0)
  | j + 1 =>
    let prev := askUpTo L T b j
    fun h =>
      if h.length = j then
        if hex : ∃ x₀ : Vec n, tr prev 0 x₀ j = h ∧ tr prev 1 (T x₀ + b) j = h then
          let x₀ := Classical.choose hex
          fun i => (L j i, L j i (T x₀ + b) + L j i x₀, 0)
        else
          fun i => (L j i, 0, 0)
      else
        prev h

private lemma askUpTo_agree {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) {j m : ℕ} (hjm : j ≤ m)
    (h : List (Fin n → ZMod 2)) (hlen : h.length < j) :
    askUpTo L T b m h = askUpTo L T b j h := by
  induction m with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; rfl
  | succ m ih =>
    by_cases h' : j = m + 1
    · subst h'; rfl
    · have hne : h.length ≠ m := by omega
      change (if h.length = m then _ else askUpTo L T b m h) = askUpTo L T b j h
      rw [if_neg hne]
      exact ih (by omega)

private lemma tr_askUpTo_agree {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) {r j m : ℕ} (hrj : r ≤ j) (hjm : j ≤ m)
    (layer : ZMod 2) (word : Vec n) :
    tr (askUpTo L T b m) layer word r = tr (askUpTo L T b j) layer word r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hprev := ih (by omega)
    change step (askUpTo L T b m) layer word (tr (askUpTo L T b m) layer word r) =
      step (askUpTo L T b j) layer word (tr (askUpTo L T b j) layer word r)
    rw [hprev]
    unfold step
    have hlen : (tr (askUpTo L T b j) layer word r).length < j := by
      rw [tr_length]; omega
    rw [askUpTo_agree L T b hjm _ hlen]

private lemma askUpTo_fst {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) {j s : ℕ} (hjs : j < s)
    (h : List (Fin n → ZMod 2)) (hlen : h.length = j) (i : Fin n) :
    (askUpTo L T b s h i).1 = L j i := by
  rw [askUpTo_agree L T b hjs h (by omega)]
  unfold askUpTo
  dsimp only
  rw [if_pos hlen]
  split_ifs <;> rfl

private lemma askUpTo_histFlag {n s : ℕ} (flag : ℕ → Submodule (ZMod 2) (Dual n))
    (h0 : flag 0 = ⊥) (hmono : ∀ j < s, flag j ≤ flag (j + 1))
    (L : ℕ → Fin n → Dual n) (hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1))
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    {j : ℕ} (hjs : j ≤ s) (h : List (Fin n → ZMod 2)) (hlen : h.length = j) :
    histFlag (askUpTo L T b s) h j = flag j := by
  induction j generalizing h with
  | zero => exact h0.symm
  | succ j ih =>
    have h'len : (h.take j).length = j := by rw [List.length_take, hlen]; omega
    simp only [histFlag]
    rw [histFlag_eq_of_take (askUpTo L T b s) h (h.take j) j (by rw [List.take_take, Nat.min_self]),
      ih (by omega) (h.take j) h'len]
    have hround : roundSpace (askUpTo L T b s) (h.take j) = flag (j + 1) := by
      unfold roundSpace
      have hfun : (fun i : Fin n => (askUpTo L T b s (h.take j) i).1) = L j := by
        funext i; exact askUpTo_fst L T b (by omega) (h.take j) h'len i
      rw [hfun, hL j (by omega)]
    rw [hround, sup_eq_right.mpr (hmono j (by omega))]

open Classical in
private lemma askUpTo_children_eq {n s : ℕ} (flag : ℕ → Submodule (ZMod 2) (Dual n))
    (h0 : flag 0 = ⊥) (hmono : ∀ j < s, flag j ≤ flag (j + 1))
    (L : ℕ → Fin n → Dual n) (hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1))
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    {j : ℕ} (hjs : j < s) (h : List (Fin n → ZMod 2)) (hlen : h.length = j) :
    (∑ y : Fin n → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr (askUpTo L T b s) 0 x (j + 1) = h ++ [y] ∧
        tr (askUpTo L T b s) 1 (T x + b) (j + 1) = h ++ [y])).card) *
      2 ^ (stepCost T (flag j) (flag (j + 1))) =
    (Finset.univ.filter (fun x : Vec n =>
      tr (askUpTo L T b s) 0 x j = h ∧ tr (askUpTo L T b s) 1 (T x + b) j = h)).card := by
  set ask := askUpTo L T b s
  set Surv := Finset.univ.filter (fun x : Vec n =>
    tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h ∧
    (fun i : Fin n => (ask h i).1 x + (ask h i).2.1 * 0 + (ask h i).2.2) =
    (fun i : Fin n => (ask h i).1 (T x + b) + (ask h i).2.1 * 1 + (ask h i).2.2))
  set Parent := Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)
  have hsum_eq : ∑ y : Fin n → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card = Surv.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Surv, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        tr_succ_eq_iff ask 0 x j h hlen, tr_succ_eq_iff ask 1 (T x + b) j h hlen]
      constructor
      · rintro ⟨y, ⟨h0', hy0⟩, ⟨h1', hy1⟩⟩; exact ⟨h0', h1', hy0.trans hy1.symm⟩
      · rintro ⟨h0', h1', hag⟩; exact ⟨_, ⟨h0', rfl⟩, ⟨h1', hag.symm⟩⟩
    · intro y₁ _ y₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have h1 := ((tr_succ_eq_iff ask 0 x j h hlen y₁).mp (Finset.mem_filter.mp hx₁).2.1).2
      have h2 := ((tr_succ_eq_iff ask 0 x j h hlen y₂).mp (Finset.mem_filter.mp hx₂).2.1).2
      exact hne (h1.symm.trans h2)
  rw [hsum_eq]
  by_cases hPne : Parent.Nonempty
  · have hex_prev : ∃ x₀ : Vec n,
        tr (askUpTo L T b j) 0 x₀ j = h ∧ tr (askUpTo L T b j) 1 (T x₀ + b) j = h := by
      rcases hPne with ⟨x, hx⟩
      have hx' := (Finset.mem_filter.mp hx).2
      refine ⟨x, ?_, ?_⟩
      · rw [← tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 0 x]; exact hx'.1
      · rw [← tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 1 (T x + b)]; exact hx'.2
    set x₀ := Classical.choose hex_prev
    have hx₀_prev : tr (askUpTo L T b j) 0 x₀ j = h ∧ tr (askUpTo L T b j) 1 (T x₀ + b) j = h :=
      Classical.choose_spec hex_prev
    have hx₀_cur : tr ask 0 x₀ j = h ∧ tr ask 1 (T x₀ + b) j = h := by
      refine ⟨?_, ?_⟩
      · rw [tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 0 x₀]; exact hx₀_prev.1
      · rw [tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 1 (T x₀ + b)]; exact hx₀_prev.2
    have hask_h : ask h = fun i => (L j i, L j i (T x₀ + b) + L j i x₀, 0) := by
      change askUpTo L T b s h = _
      rw [askUpTo_agree L T b hjs h (by omega)]
      change (if h.length = j then
        if hex : ∃ x₀ : Vec n, tr (askUpTo L T b j) 0 x₀ j = h ∧ tr (askUpTo L T b j) 1 (T x₀ + b) j = h then
          fun i => (L j i, L j i (T (Classical.choose hex) + b) + L j i (Classical.choose hex), 0)
        else fun i => (L j i, 0, 0)
        else askUpTo L T b j h) = _
      rw [if_pos hlen, dif_pos hex_prev]
    have hx₀_ag : (fun i : Fin n => (ask h i).1 x₀ + (ask h i).2.1 * 0 + (ask h i).2.2) =
        (fun i : Fin n => (ask h i).1 (T x₀ + b) + (ask h i).2.1 * 1 + (ask h i).2.2) := by
      ext i
      rw [hask_h]
      dsimp only
      simp only [mul_zero, add_zero, mul_one]
      have hz := zmod2_add_self (L j i (T x₀ + b))
      calc L j i x₀ = 0 + L j i x₀ := (zero_add _).symm
        _ = (L j i (T x₀ + b) + L j i (T x₀ + b)) + L j i x₀ := by rw [hz]
        _ = L j i (T x₀ + b) + (L j i (T x₀ + b) + L j i x₀) := by ring
    have hflagj : histFlag ask h j = flag j := askUpTo_histFlag flag h0 hmono L hL T b (le_of_lt hjs) h hlen
    have hroundj : roundSpace ask h = flag (j + 1) := by
      unfold roundSpace
      have hfun : (fun i : Fin n => (ask h i).1) = L j := by
        funext i; exact askUpTo_fst L T b hjs h hlen i
      rw [hfun, hL j hjs]
    have hSurv_eq : Surv = Finset.univ.filter (fun x : Vec n =>
        x - x₀ ∈ Ann ((flag j ⊔ (flag j).map (Ddual T)) ⊔ (flag (j + 1)).map (Ddual T))) := by
      ext x
      simp only [Surv, Finset.mem_filter, Finset.mem_univ, true_and]
      have hiff := agree_next_coset_iff T b ask j h hlen x₀ ⟨hx₀_cur.1, hx₀_cur.2, hx₀_ag⟩ x
      rwa [hflagj, hroundj] at hiff
    have hParent_eq : Parent = Finset.univ.filter (fun x : Vec n =>
        x - x₀ ∈ Ann (flag j ⊔ (flag j).map (Ddual T))) := by
      ext x
      simp only [Parent, Finset.mem_filter, Finset.mem_univ, true_and]
      have hiff := surv_coset_iff T b ask j h hlen x₀ hx₀_cur x
      rwa [hflagj] at hiff
    rw [hSurv_eq, hParent_eq, card_coset_Ann, card_coset_Ann]
    set base := flag j ⊔ (flag j).map (Ddual T)
    change 2 ^ (n - Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n))) *
        2 ^ (Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
          Module.finrank (ZMod 2) base) =
      2 ^ (n - Module.finrank (ZMod 2) base)
    rw [← pow_add]
    have hle1 : Module.finrank (ZMod 2) base ≤
        Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n)) :=
      Submodule.finrank_mono le_sup_left
    have hle2 : Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n)) ≤ n :=
      finrank_dual_le _
    congr 1; omega
  · have hP0 : Parent = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPne
    have hS0 : Surv = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have hmem : x ∈ Parent := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx'.1, hx'.2.1⟩
      rw [hP0] at hmem
      exact Finset.notMem_empty x hmem
    rw [hS0, hP0, Finset.card_empty, zero_mul]

private lemma askUpTo_injective {n s : ℕ} (flag : ℕ → Submodule (ZMod 2) (Dual n))
    (h0 : flag 0 = ⊥) (hs : flag s = ⊤)
    (L : ℕ → Fin n → Dual n) (hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1))
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) (layer : ZMod 2) :
    Function.Injective (fun x : Vec n => tr (askUpTo L T b s) layer x s) := by
  intro x y hxy
  by_cases hs0 : s = 0
  · subst hs0
    have hbot_top : (⊥ : Submodule (ZMod 2) (Dual n)) = ⊤ := h0.symm.trans hs
    have hAnn : (⊤ : Submodule (ZMod 2) (Vec n)) = ⊥ := by
      have h1 : Ann (⊥ : Submodule (ZMod 2) (Dual n)) = ⊤ := by ext v; simp [Ann]
      rw [← h1, hbot_top, Ann_top_eq_bot]
    have hsub : x - y ∈ (⊥ : Submodule (ZMod 2) (Vec n)) := by rw [← hAnn]; exact Submodule.mem_top
    exact sub_eq_zero.mp ((Submodule.mem_bot (ZMod 2)).mp hsub)
  · have hlt : s - 1 < s := by omega
    have hprev : tr (askUpTo L T b s) layer x (s - 1) = tr (askUpTo L T b s) layer y (s - 1) := by
      have ht := congrArg (List.take (s - 1)) hxy
      rwa [tr_take_le _ _ _ (by omega : s - 1 ≤ s), tr_take_le _ _ _ (by omega : s - 1 ≤ s)] at ht
    set h := tr (askUpTo L T b s) layer x (s - 1)
    have hlen : h.length = s - 1 := tr_length _ _ _ _
    have hs_eq : s = (s - 1) + 1 := by omega
    have hxy' : tr (askUpTo L T b s) layer x ((s - 1) + 1) =
        tr (askUpTo L T b s) layer y ((s - 1) + 1) := by
      dsimp only at hxy; rwa [← hs_eq]
    have hstep_x : tr (askUpTo L T b s) layer x ((s - 1) + 1) =
        h ++ [fun i => (askUpTo L T b s h i).1 x + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2] := rfl
    have hstep_y : tr (askUpTo L T b s) layer y ((s - 1) + 1) =
        h ++ [fun i => (askUpTo L T b s h i).1 y + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2] := by
      change tr (askUpTo L T b s) layer y (s - 1) ++ _ = _
      rw [← hprev]
    rw [hstep_x, hstep_y] at hxy'
    have hfun : (fun i => (askUpTo L T b s h i).1 x + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2) =
        (fun i => (askUpTo L T b s h i).1 y + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2) :=
      (List.cons.inj (List.append_cancel_left hxy')).1
    have hsub_ann : x - y ∈ Ann (⊤ : Submodule (ZMod 2) (Dual n)) := by
      rw [← hs, hs_eq, ← hL (s - 1) hlt, mem_Ann_span]
      rintro _ ⟨i, rfl⟩
      have heq := congrFun hfun i
      rw [askUpTo_fst L T b hlt h hlen i] at heq
      have hcancel : L (s - 1) i x = L (s - 1) i y := add_right_cancel (add_right_cancel heq)
      rw [map_sub, hcancel, sub_self]
    rw [Ann_top_eq_bot, Submodule.mem_bot] at hsub_ann
    exact sub_eq_zero.mp hsub_ann

private lemma feasible_iff_flag (n s : ℕ) (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) (K : ℕ) :
    (∃ (w : ℕ) (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2),
      (∀ layer : ZMod 2, Function.Injective (fun word : Vec n =>
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) [])) ∧
      K ≤ (Finset.univ.filter (fun x : Vec n =>
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 x + (ask hist i).2.1 * 0 + (ask hist i).2.2]) [] =
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 (T x + b) + (ask hist i).2.1 * 1 + (ask hist i).2.2]) [])).card) ↔
    ∃ flag : ℕ → Submodule (ZMod 2) (Dual n),
      flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j + 1)) ∧
      K * 2 ^ ((Finset.range s).sum (fun j => stepCost T (flag j) (flag (j + 1)))) ≤ 2 ^ n := by
  constructor
  · rintro ⟨w, ask, hinj, hK⟩
    have htr_eq : ∀ layer x,
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 x + (ask hist i).2.1 * layer + (ask hist i).2.2]) [] =
        tr ask layer x s := fun layer x => tr_eq_foldl ask layer x s
    have hinj0 : Function.Injective (fun x => tr ask 0 x s) := by
      intro x y hxy; apply hinj 0; dsimp only; rwa [htr_eq 0 x, htr_eq 0 y]
    by_cases hK0 : K = 0
    · subst hK0
      refine ⟨histFlag ask (tr ask 0 0 s), rfl, histFlag_top_of_injective ask hinj0 0,
        fun j _ => le_sup_left, by simp⟩
    · classical
      set Matches := Finset.univ.filter (fun x : Vec n => tr ask 0 x s = tr ask 1 (T x + b) s)
      have hK_le : K ≤ Matches.card := by
        convert hK using 2; ext x
        simp only [Matches, Finset.mem_filter, Finset.mem_univ, true_and, htr_eq]
      set Occ := (Hists w s).filter (fun h =>
        (Finset.univ.filter (fun x : Vec n => tr ask 0 x s = h ∧ tr ask 1 (T x + b) s = h)).Nonempty)
      have hMatches_sum : Matches.card = ∑ h ∈ Occ,
          (Finset.univ.filter (fun x : Vec n => tr ask 0 x s = h ∧ tr ask 1 (T x + b) s = h)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext x
          simp only [Matches, Occ, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, mem_Hists_iff]
          constructor
          · intro hmatch
            exact ⟨tr ask 0 x s, ⟨tr_length ask 0 x s,
              ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl, hmatch.symm⟩⟩⟩, rfl, hmatch.symm⟩
          · rintro ⟨h, _, h0, h1⟩; exact h0.trans h1.symm
        · intro h₁ _ h₂ _ hne
          change Disjoint _ _; rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          exact hne ((Finset.mem_filter.mp hx₁).2.1.symm.trans (Finset.mem_filter.mp hx₂).2.1)
      have hOcc_ne : Occ.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hMatches_sum
        omega
      rcases Finset.exists_min_image Occ (fun h => histCost T ask h s) hOcc_ne
        with ⟨h_star, hh_star_mem, hh_star_min⟩
      have hpow_le : K * 2 ^ (histCost T ask h_star s) ≤ 2 ^ n := by
        calc K * 2 ^ histCost T ask h_star s
            ≤ Matches.card * 2 ^ histCost T ask h_star s := Nat.mul_le_mul_right _ hK_le
          _ = ∑ h ∈ Occ,
                (Finset.univ.filter (fun x : Vec n => tr ask 0 x s = h ∧ tr ask 1 (T x + b) s = h)).card *
                2 ^ histCost T ask h_star s := by rw [hMatches_sum, Finset.sum_mul]
          _ ≤ ∑ h ∈ Occ,
                (Finset.univ.filter (fun x : Vec n => tr ask 0 x s = h ∧ tr ask 1 (T x + b) s = h)).card *
                2 ^ histCost T ask h s :=
              Finset.sum_le_sum (fun h hh => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (hh_star_min h hh)))
          _ ≤ ∑ h ∈ Hists w s,
                (Finset.univ.filter (fun x : Vec n => tr ask 0 x s = h ∧ tr ask 1 (T x + b) s = h)).card *
                2 ^ histCost T ask h s := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          _ ≤ 2 ^ n := weighted_sum_le T b ask s
      rcases (Finset.mem_filter.mp hh_star_mem).2 with ⟨x₀, hx₀⟩
      have hx₀_tr : tr ask 0 x₀ s = h_star := (Finset.mem_filter.mp hx₀).2.1
      refine ⟨histFlag ask h_star, rfl, ?_, fun j _ => le_sup_left, ?_⟩
      · rw [← hx₀_tr]; exact histFlag_top_of_injective ask hinj0 x₀
      · rw [← histCost_eq_range_sum T ask h_star s]; exact hpow_le
  · rintro ⟨flag, hflag0, hflags, hmono, hKbound⟩
    classical
    let L : ℕ → Fin n → Dual n := fun j => spanGenerators (flag (j + 1))
    have hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1) :=
      fun j _ => span_spanGenerators (flag (j + 1))
    let ask := askUpTo L T b s
    refine ⟨n, ask, ?_, ?_⟩
    · intro layer x y hxy
      dsimp only at hxy
      rw [tr_eq_foldl ask layer x s, tr_eq_foldl ask layer y s] at hxy
      exact askUpTo_injective flag hflag0 hflags L hL T b layer hxy
    · have hsum_exact : ∀ j ≤ s,
          (∑ h ∈ Hists n j,
            (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card) *
            2 ^ ((Finset.range j).sum (fun r => stepCost T (flag r) (flag (r + 1)))) = 2 ^ n := by
        intro j
        induction j with
        | zero =>
          intro _
          simp only [Hists, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty, pow_zero,
            mul_one, tr, true_and, Finset.filter_true, Finset.card_univ, Fintype.card_pi,
            Fintype.card_fin, ZMod.card 2, Finset.prod_const]
        | succ j ih =>
          intro hjs
          rw [sum_Hists_succ, Finset.sum_range_succ, pow_add]
          calc (∑ h ∈ Hists n j, ∑ y : Fin n → ZMod 2,
                  (Finset.univ.filter (fun x : Vec n =>
                    tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
                (2 ^ ((Finset.range j).sum (fun r => stepCost T (flag r) (flag (r + 1)))) *
                2 ^ stepCost T (flag j) (flag (j + 1)))
              = ((∑ h ∈ Hists n j, ∑ y : Fin n → ZMod 2,
                  (Finset.univ.filter (fun x : Vec n =>
                    tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
                  2 ^ stepCost T (flag j) (flag (j + 1))) *
                2 ^ ((Finset.range j).sum (fun r => stepCost T (flag r) (flag (r + 1)))) := by ring
            _ = (∑ h ∈ Hists n j, (∑ y : Fin n → ZMod 2,
                  (Finset.univ.filter (fun x : Vec n =>
                    tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
                  2 ^ stepCost T (flag j) (flag (j + 1))) *
                2 ^ ((Finset.range j).sum (fun r => stepCost T (flag r) (flag (r + 1)))) := by
                rw [Finset.sum_mul]
            _ = (∑ h ∈ Hists n j,
                  (Finset.univ.filter (fun x : Vec n =>
                    tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card) *
                2 ^ ((Finset.range j).sum (fun r => stepCost T (flag r) (flag (r + 1)))) := by
                congr 1
                exact Finset.sum_congr rfl (fun h hh =>
                  askUpTo_children_eq flag hflag0 hmono L hL T b (by omega) h (mem_Hists_iff.mp hh))
            _ = 2 ^ n := ih (by omega)
      have hMatches_eq :
          (Finset.univ.filter (fun x : Vec n =>
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 x + (ask hist i).2.1 * 0 + (ask hist i).2.2]) [] =
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 (T x + b) + (ask hist i).2.1 * 1 + (ask hist i).2.2]) [])).card =
          ∑ h ∈ Hists n s,
            (Finset.univ.filter (fun x : Vec n => tr ask 0 x s = h ∧ tr ask 1 (T x + b) s = h)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext x
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            mem_Hists_iff, tr_eq_foldl]
          constructor
          · intro hmatch; exact ⟨tr ask 0 x s, tr_length ask 0 x s, rfl, hmatch.symm⟩
          · rintro ⟨h, _, h0, h1⟩; exact h0.trans h1.symm
        · intro h₁ _ h₂ _ hne
          change Disjoint _ _; rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          exact hne ((Finset.mem_filter.mp hx₁).2.1.symm.trans (Finset.mem_filter.mp hx₂).2.1)
      have hexact := hsum_exact s le_rfl
      rw [← hMatches_eq] at hexact
      have hmul : K * 2 ^ ((Finset.range s).sum (fun r => stepCost T (flag r) (flag (r + 1)))) ≤
          (Finset.univ.filter (fun x : Vec n =>
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 x + (ask hist i).2.1 * 0 + (ask hist i).2.2]) [] =
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 (T x + b) + (ask hist i).2.1 * 1 + (ask hist i).2.2]) [])).card *
          2 ^ ((Finset.range s).sum (fun r => stepCost T (flag r) (flag (r + 1)))) := by
        rw [hexact]; exact hKbound
      exact Nat.le_of_mul_le_mul_right hmul (Nat.pos_of_ne_zero (by positivity))

private lemma finrank_iSup_range_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (m : ℕ) (S : ℕ → Submodule K V) :
    Module.finrank K (⨆ i ∈ Finset.range m, S i : Submodule K V) ≤
      ∑ i ∈ Finset.range m, Module.finrank K (S i) := by
  induction m with
  | zero =>
    have hbot : (⨆ i ∈ (∅ : Finset ℕ), S i : Submodule K V) = ⊥ := by simp
    rw [Finset.range_zero, hbot, finrank_bot, Finset.sum_empty]
  | succ m ih =>
    rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
    have hsup : (⨆ i ∈ insert m (Finset.range m), S i : Submodule K V) =
        S m ⊔ (⨆ i ∈ Finset.range m, S i) := by
      simp [iSup_or, iSup_sup_eq]
    rw [hsup]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (S m) (⨆ i ∈ Finset.range m, S i)
    omega

private lemma exists_sub_compl {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Submodule K V) :
    ∃ E : Submodule K V, E ≤ B ∧ A ⊔ E = A ⊔ B ∧ A ⊓ E = ⊥ := by
  let I : Submodule K B := A.comap B.subtype
  rcases Submodule.exists_isCompl I with ⟨C, hIC⟩
  let E : Submodule K V := C.map B.subtype
  have hEB : E ≤ B := by rintro _ ⟨x, _, rfl⟩; exact x.2
  refine ⟨E, hEB, ?_, ?_⟩
  · apply le_antisymm
    · exact sup_le le_sup_left (hEB.trans le_sup_right)
    · refine sup_le le_sup_left ?_
      intro x hx
      have hmem : (⟨x, hx⟩ : B) ∈ (⊤ : Submodule K B) := Submodule.mem_top
      rw [← hIC.sup_eq_top] at hmem
      rcases Submodule.mem_sup.mp hmem with ⟨u, hu, v, hv, huv⟩
      have hxeq : x = u.1 + v.1 := (congrArg Subtype.val huv).symm
      rw [hxeq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  · rw [eq_bot_iff]
    rintro x ⟨hxA, ⟨v, hvC, rfl⟩⟩
    have hv0 : v ∈ I ⊓ C := ⟨hxA, hvC⟩
    rw [hIC.inf_eq_bot] at hv0
    have : v = 0 := (Submodule.mem_bot K).mp hv0
    rw [this]; exact Submodule.zero_mem _

private lemma exists_generating_subspace_of_flag {n s : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (flag : ℕ → Submodule (ZMod 2) (Dual n)) (h0 : flag 0 = ⊥) (hs : flag s = ⊤) :
    ∃ E : Submodule (ZMod 2) (Dual n),
      Module.finrank (ZMod 2) E ≤ (Finset.range s).sum (fun j => stepCost T (flag j) (flag (j + 1))) ∧
      LinearMap.range ((Ddual T) ^ s) ≤ ⨆ r ∈ Finset.range s, E.map ((Ddual T) ^ r) := by
  let D' := Ddual T
  have hex_step : ∀ j : ℕ, ∃ Ej : Submodule (ZMod 2) (Dual n),
      Module.finrank (ZMod 2) Ej = stepCost T (flag j) (flag (j + 1)) ∧
      (flag (j + 1)).map D' ≤ (flag j ⊔ (flag j).map D') ⊔ Ej := by
    intro j
    set base := flag j ⊔ (flag j).map D'
    set target := (flag (j + 1)).map D'
    rcases exists_sub_compl base target with ⟨Ej, _, hsup_eq, hdisj⟩
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq base Ej
    rw [hsup_eq, hdisj, finrank_bot, add_zero] at hdim
    refine ⟨Ej, ?_, le_sup_right.trans hsup_eq.symm.le⟩
    change Module.finrank (ZMod 2) Ej =
      Module.finrank (ZMod 2) (base ⊔ target : Submodule (ZMod 2) (Dual n)) - Module.finrank (ZMod 2) base
    omega
  let Es : ℕ → Submodule (ZMod 2) (Dual n) := fun j => Classical.choose (hex_step j)
  have hEs : ∀ j, Module.finrank (ZMod 2) (Es j) = stepCost T (flag j) (flag (j + 1)) ∧
      (flag (j + 1)).map D' ≤ (flag j ⊔ (flag j).map D') ⊔ Es j :=
    fun j => Classical.choose_spec (hex_step j)
  let E : Submodule (ZMod 2) (Dual n) := ⨆ j ∈ Finset.range s, Es j
  refine ⟨E, ?_, ?_⟩
  · calc Module.finrank (ZMod 2) E
        ≤ ∑ j ∈ Finset.range s, Module.finrank (ZMod 2) (Es j) := finrank_iSup_range_le s Es
      _ = ∑ j ∈ Finset.range s, stepCost T (flag j) (flag (j + 1)) :=
          Finset.sum_congr rfl (fun j _ => (hEs j).1)
  · have hpow : ∀ k ≤ s, (flag k).map (D' ^ k) ≤ ⨆ r ∈ Finset.range k, E.map (D' ^ r) := by
      intro k
      induction k with
      | zero => intro _; simp [h0]
      | succ k ih =>
        intro hks
        have hstep := (hEs k).2
        have hpow_succ : (flag (k + 1)).map (D' ^ (k + 1)) =
            ((flag (k + 1)).map D').map (D' ^ k) := by
          rw [map_map_end, ← pow_succ]
        rw [hpow_succ]
        refine (Submodule.map_mono hstep).trans ?_
        rw [Submodule.map_sup, Submodule.map_sup]
        refine sup_le (sup_le ?_ ?_) ?_
        · refine (ih (by omega)).trans ?_
          refine iSup₂_le (fun r hr => ?_)
          exact le_biSup (fun r => E.map (D' ^ r)) (Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega))
        · have hmap : ((flag k).map D').map (D' ^ k) = ((flag k).map (D' ^ k)).map D' := by
            rw [map_map_end, map_map_end, ← pow_succ, ← pow_succ']
          rw [hmap]
          refine (Submodule.map_mono (ih (by omega))).trans ?_
          rw [Submodule.map_iSup]
          refine iSup_le (fun r => ?_)
          rw [Submodule.map_iSup]
          refine iSup_le (fun hr => ?_)
          rw [map_map_end, ← pow_succ']
          exact le_biSup (fun r => E.map (D' ^ r)) (Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega))
        · have hEsub : Es k ≤ E := le_biSup Es (Finset.mem_range.mpr (by omega))
          exact (Submodule.map_mono hEsub).trans
            (le_biSup (fun r => E.map (D' ^ r)) (Finset.mem_range.mpr (Nat.lt_succ_self k)))
    have htop : LinearMap.range (D' ^ s) = (⊤ : Submodule (ZMod 2) (Dual n)).map (D' ^ s) :=
      (Submodule.map_top _).symm
    rw [htop, ← hs]
    exact hpow s le_rfl

private lemma poly_inv_of_end_inv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (D' : V →ₗ[K] V) (M : Submodule K V) (hM : M.map D' ≤ M) (f : Polynomial K) :
    M.map (Polynomial.aeval D' f) ≤ M := by
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ ih₁ ih₂ =>
    rintro _ ⟨x, hx, rfl⟩
    rw [map_add, LinearMap.add_apply]
    exact M.add_mem (ih₁ ⟨x, hx, rfl⟩) (ih₂ ⟨x, hx, rfl⟩)
  | monomial k c =>
    rintro _ ⟨x, hx, rfl⟩
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.smul_apply]
    refine M.smul_mem c ?_
    have hpow : ∀ t, M.map (D' ^ t) ≤ M := by
      intro t
      induction t with
      | zero => rintro _ ⟨y, hy, rfl⟩; exact hy
      | succ t iht =>
        rw [pow_succ', ← map_map_end]
        exact (Submodule.map_mono iht).trans hM
    exact hpow k ⟨x, hx, rfl⟩

private lemma finrank_ker_eq_finrank_quot_end {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (M : Submodule K V) (f : V →ₗ[K] V) (hM : M.map f ≤ M)
    (W : Submodule K V) (hWM : W ≤ M)
    (k : ℕ) (g : Fin k → V) (hgM : ∀ i, g i ∈ M)
    (hgen : ∀ x ∈ M, ∃ c : Fin k → K, x - ∑ i, c i • g i ∈ M.map f) :
    Module.finrank K (W ⊓ LinearMap.ker f : Submodule K V) ≤ k := by
  classical
  let fp : M →ₗ[K] M :=
    { toFun := fun x => ⟨f x.1, hM ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hker_le : Module.finrank K (W ⊓ LinearMap.ker f : Submodule K V) ≤
      Module.finrank K (LinearMap.ker fp) := by
    let incl : (W ⊓ LinearMap.ker f : Submodule K V) →ₗ[K] LinearMap.ker fp :=
      { toFun := fun x => ⟨⟨x.1, hWM x.2.1⟩, Subtype.ext x.2.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact LinearMap.finrank_le_finrank_of_injective (f := incl)
      (fun _ _ h => Subtype.ext (congrArg (fun z => z.1.1) h))
  have hker_eq_quot : Module.finrank K (LinearMap.ker fp) =
      Module.finrank K (M ⧸ LinearMap.range fp) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker fp
    have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range fp)
    omega
  let gen : Fin k → (M ⧸ LinearMap.range fp) := fun i => (LinearMap.range fp).mkQ ⟨g i, hgM i⟩
  have hspan_top : Submodule.span K (Set.range gen) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases Submodule.Quotient.mk_surjective _ z with ⟨x, rfl⟩
    rcases hgen x.1 x.2 with ⟨c, ⟨y, hyM, hyf⟩⟩
    have heq : (Submodule.Quotient.mk x : M ⧸ LinearMap.range fp) = ∑ i : Fin k, c i • gen i := by
      have hsum : ∑ i : Fin k, c i • gen i =
          (Submodule.Quotient.mk (∑ i : Fin k, c i • (⟨g i, hgM i⟩ : M)) : M ⧸ LinearMap.range fp) := by
        change ∑ i : Fin k, c i • (LinearMap.range fp).mkQ ⟨g i, hgM i⟩ =
          (LinearMap.range fp).mkQ (∑ i : Fin k, c i • (⟨g i, hgM i⟩ : M))
        rw [map_sum]; refine Finset.sum_congr rfl (fun i _ => by rw [map_smul])
      rw [hsum, Submodule.Quotient.eq]
      refine ⟨⟨y, hyM⟩, ?_⟩
      ext
      simpa [fp, Submodule.coe_sum, Submodule.coe_smul] using hyf
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hquot_le : Module.finrank K (M ⧸ LinearMap.range fp) ≤ k := by
    have hcard := finrank_span_le_card (R := K) (Set.range gen)
    rw [hspan_top, finrank_top] at hcard
    refine hcard.trans ?_
    rw [Set.toFinset_card]
    exact (Fintype.card_range_le gen).trans (by simp)
  omega

private lemma natDegree_modByMonic_lt_of_ne_zero (f d : Polynomial (ZMod 2)) (hd : d.Monic)
    (h0 : f %ₘ d ≠ 0) : (f %ₘ d).natDegree < d.natDegree := by
  have hdeg := Polynomial.degree_modByMonic_lt f hd
  rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hd.ne_zero] at hdeg
  exact WithBot.coe_lt_coe.mp hdeg

private lemma lower_bound_socle {n s : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (E : Submodule (ZMod 2) (Dual n))
    (hW : LinearMap.range ((Ddual T) ^ s) ≤ ⨆ r ∈ Finset.range s, E.map ((Ddual T) ^ r))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((Ddual T) ^ s) ⊓ LinearMap.ker (Polynomial.aeval (Ddual T) p) :
        Submodule (ZMod 2) (Dual n)) ≤
      p.natDegree * Module.finrank (ZMod 2) E := by
  let D' := Ddual T
  let M : Submodule (ZMod 2) (Dual n) := ⨆ r : ℕ, E.map (D' ^ r)
  have hM_inv : M.map D' ≤ M := by
    rw [Submodule.map_iSup]
    refine iSup_le (fun r => ?_)
    rw [map_map_end, ← pow_succ']
    exact le_iSup (fun k => E.map (D' ^ k)) (r + 1)
  have hM_aeval : ∀ f : Polynomial (ZMod 2), M.map (Polynomial.aeval D' f) ≤ M :=
    poly_inv_of_end_inv D' M hM_inv
  have hWM : LinearMap.range (D' ^ s) ≤ M :=
    hW.trans (iSup₂_le (fun r _ => le_iSup (fun k => E.map (D' ^ k)) r))
  have hp_monic : p.Monic := by
    rw [Polynomial.Monic]
    exact zmod2_eq_one_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero)
  haveI : Module.Free (ZMod 2) E := Module.Free.of_divisionRing (ZMod 2) E
  let bE := Module.finBasis (ZMod 2) E
  let q := Module.finrank (ZMod 2) E
  let eProd : Fin (p.natDegree * q) ≃ Fin p.natDegree × Fin q := finProdFinEquiv.symm
  let g : Fin (p.natDegree * q) → Dual n := fun idx =>
    (D' ^ (eProd idx).1.val) (bE (eProd idx).2).1
  have hgM : ∀ idx, g idx ∈ M := fun idx =>
    le_iSup (fun k => E.map (D' ^ k)) (eProd idx).1.val ⟨(bE (eProd idx).2).1, (bE (eProd idx).2).2, rfl⟩
  refine finrank_ker_eq_finrank_quot_end M (Polynomial.aeval D' p) (hM_aeval p)
    (LinearMap.range (D' ^ s)) hWM (p.natDegree * q) g hgM ?_
  let Ksub : Submodule (ZMod 2) (Dual n) :=
    Submodule.span (ZMod 2) (Set.range g) ⊔ M.map (Polynomial.aeval D' p)
  have hMK : M ≤ Ksub := by
    refine iSup_le (fun r => ?_)
    rintro _ ⟨u, hu, rfl⟩
    let f : Polynomial (ZMod 2) := (Polynomial.X : Polynomial (ZMod 2)) ^ r
    let rem := f %ₘ p
    let quo := f /ₘ p
    have hdiv : rem + p * quo = f := Polynomial.modByMonic_add_div f p
    have huM : u ∈ M := le_iSup (fun k => E.map (D' ^ k)) 0 ⟨u, hu, by simp⟩
    have hsplit : (D' ^ r) u = Polynomial.aeval D' rem u +
        Polynomial.aeval D' p (Polynomial.aeval D' quo u) := by
      have h2 := LinearMap.congr_fun (congrArg (Polynomial.aeval D') hdiv) u
      simpa [f, map_add, map_mul, end_mul_apply] using h2.symm
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right ⟨Polynomial.aeval D' quo u, hM_aeval quo ⟨u, huM, rfl⟩, rfl⟩)
    have hrem_sum : rem = ∑ t ∈ Finset.range p.natDegree,
        Polynomial.monomial t (rem.coeff t) := by
      by_cases h0 : rem = 0
      · simp [h0]
      · exact Polynomial.as_sum_range' rem p.natDegree (natDegree_modByMonic_lt_of_ne_zero f p hp_monic h0)
    rw [hrem_sum, map_sum, LinearMap.sum_apply, Finset.sum_range]
    refine Submodule.sum_mem _ (fun t _ => ?_)
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    have hurep := bE.sum_repr ⟨u, hu⟩
    have huval : u = ∑ i : Fin q, (bE.repr ⟨u, hu⟩ i) • (bE i).1 := by
      have := congrArg Subtype.val hurep
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
    rw [huval, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨eProd.symm (t, i), ?_⟩
    simp [g]
  intro x hxM
  rcases Submodule.mem_sup.mp (hMK hxM) with ⟨s_el, hs_el, m_el, hm_el, hsm⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hs_el
  rcases hs_el with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  have hsub : x - ∑ i, c i • g i = m_el := by rw [← hsm]; abel
  rw [hsub]
  exact hm_el

private def cycSpan {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (v : Dual n) (m : ℕ) :
    Submodule (ZMod 2) (Dual n) :=
  Submodule.span (ZMod 2) (Set.image (fun r : ℕ => (D' ^ r) v) (Finset.range m : Set ℕ))

private lemma pow_mem_cycSpan {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (v : Dual n) (m r : ℕ)
    (hr : r < m) : (D' ^ r) v ∈ cycSpan D' v m :=
  Submodule.subset_span ⟨r, Finset.mem_range.mpr hr, rfl⟩

private lemma cycSpan_mono {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (v : Dual n) {m₁ m₂ : ℕ}
    (h : m₁ ≤ m₂) : cycSpan D' v m₁ ≤ cycSpan D' v m₂ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) h), rfl⟩

private lemma aeval_mem_cycSpan_of_lt {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (v : Dual n)
    (m : ℕ) (f : Polynomial (ZMod 2)) (hf : f.natDegree < m ∨ f = 0) :
    Polynomial.aeval D' f v ∈ cycSpan D' v m := by
  rcases hf with hlt | rfl
  · rw [Polynomial.as_sum_range' f m hlt, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ (fun r hr => ?_)
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (pow_mem_cycSpan D' v m r (Finset.mem_range.mp hr))
  · simp only [map_zero, LinearMap.zero_apply, Submodule.zero_mem]

private lemma cycSpan_inv_of_ann {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (v : Dual n)
    (d : Polynomial (ZMod 2)) (hd : d.Monic) (hann : Polynomial.aeval D' d v = 0) :
    ∀ f : Polynomial (ZMod 2), Polynomial.aeval D' f v ∈ cycSpan D' v d.natDegree := by
  intro f
  have hdiv : f %ₘ d + d * (f /ₘ d) = f := Polynomial.modByMonic_add_div f d
  have heval : Polynomial.aeval D' f v = Polynomial.aeval D' (f %ₘ d) v := by
    conv_lhs => rw [← hdiv]
    rw [map_add, map_mul, LinearMap.add_apply, end_mul_apply]
    have hcomm : Polynomial.aeval D' d (Polynomial.aeval D' (f /ₘ d) v) =
        Polynomial.aeval D' (f /ₘ d) (Polynomial.aeval D' d v) := by
      change (Polynomial.aeval D' d * Polynomial.aeval D' (f /ₘ d)) v =
        (Polynomial.aeval D' (f /ₘ d) * Polynomial.aeval D' d) v
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hcomm, hann, map_zero, add_zero]
  rw [heval]
  refine aeval_mem_cycSpan_of_lt D' v d.natDegree (f %ₘ d) ?_
  by_cases h0 : f %ₘ d = 0
  · exact Or.inr h0
  · exact Or.inl (natDegree_modByMonic_lt_of_ne_zero f d hd h0)

private lemma cycSpan_map_le {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (v : Dual n)
    (d : Polynomial (ZMod 2)) (hd : d.Monic) (hann : Polynomial.aeval D' d v = 0) :
    (cycSpan D' v d.natDegree).map D' ≤ cycSpan D' v d.natDegree := by
  rintro _ ⟨x, hx, rfl⟩
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨r, _, rfl⟩
    dsimp only
    have heq : D' ((D' ^ r) v) = Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) ^ (r + 1)) v := by
      simp [pow_succ']
    rw [heq]
    exact cycSpan_inv_of_ann D' v d hd hann _
  · simp
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma cycSpan_le_of_inv {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n)
    (M : Submodule (ZMod 2) (Dual n)) (hM : M.map D' ≤ M) (v : Dual n) (hv : v ∈ M) (m : ℕ) :
    cycSpan D' v m ≤ M := by
  have hpow : ∀ r : ℕ, (D' ^ r) v ∈ M := by
    intro r
    induction r with
    | zero => simpa using hv
    | succ r ih =>
      rw [pow_succ', end_mul_apply]
      exact hM ⟨_, ih, rfl⟩
  rw [cycSpan, Submodule.span_le]
  rintro _ ⟨r, _, rfl⟩
  exact hpow r

private lemma exists_nonzero_ann_poly_gen {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (D' : V →ₗ[K] V) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval D' q = 0 := by
  let N := Module.finrank K (V →ₗ[K] V) + 1
  have hnot : ¬ LinearIndependent K (fun k : Fin N => D' ^ k.val) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnot
  rcases hnot with ⟨c, hsum, k₀, hk₀⟩
  let q : Polynomial K := ∑ k : Fin N, Polynomial.C (c k) * (Polynomial.X : Polynomial K) ^ k.val
  have hqne : q ≠ 0 := by
    intro hq0
    have hcoeff : Polynomial.lcoeff K k₀.val q = 0 := by rw [hq0, map_zero]
    rw [map_sum] at hcoeff
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero] at hcoeff
    have hsingle : ∑ k : Fin N, (if k₀.val = k.val then c k else 0) = c k₀ := by
      rw [Finset.sum_eq_single k₀]
      · simp
      · intro k _ hne
        have : k₀.val ≠ k.val := fun h => hne (Fin.ext h).symm
        simp [this]
      · intro h; exact False.elim (h (Finset.mem_univ k₀))
    rw [hsingle] at hcoeff
    exact hk₀ hcoeff
  refine ⟨q, hqne, ?_⟩
  simp only [q, map_sum, map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    map_pow, Polynomial.aeval_X, smul_mul_assoc, one_mul]
  exact hsum

private lemma exists_nonzero_ann_poly {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) :
    ∃ q : Polynomial (ZMod 2), q.Monic ∧ Polynomial.aeval D' q = 0 := by
  rcases exists_nonzero_ann_poly_gen D' with ⟨q, hqne, hqann⟩
  refine ⟨q, ?_, hqann⟩
  rw [Polynomial.Monic]
  exact zmod2_eq_one_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hqne)

private lemma natDegree_sum_lt_of_forall_lt {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (ZMod 2)) (m : ℕ) (hm : 0 < m)
    (h : ∀ i ∈ s, (f i).natDegree < m) : (∑ i ∈ s, f i).natDegree < m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (Polynomial.natDegree_add_le _ _).trans_lt (max_lt (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

private lemma coeff_fin_sum_C_X_pow (m : ℕ) (c : Fin m → ZMod 2) (r : Fin m) :
    (∑ i : Fin m, Polynomial.C (c i) * (Polynomial.X : Polynomial (ZMod 2)) ^ i.val).coeff r.val = c r := by
  change Polynomial.lcoeff (ZMod 2) r.val (∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ i.val) = c r
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single r]
  · simp
  · intro i _ hne
    have : r.val ≠ i.val := fun h => hne (Fin.ext h).symm
    simp [this]
  · intro h; exact False.elim (h (Finset.mem_univ r))

private lemma finrank_ker_eval_ge {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (M : Submodule K V) (m : ℕ) (g : Fin m → V →ₗ[K] K) :
    Module.finrank K M - m ≤
      Module.finrank K ((LinearMap.ker (LinearMap.pi (fun r : Fin m => (g r).comp M.subtype))).map M.subtype) := by
  let Ψ : M →ₗ[K] (Fin m → K) := LinearMap.pi (fun r : Fin m => (g r).comp M.subtype)
  have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
  have hrange_le : Module.finrank K (LinearMap.range Ψ) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    simpa using this
  have hW'eq : Module.finrank K ((LinearMap.ker Ψ).map M.subtype) = Module.finrank K (LinearMap.ker Ψ) :=
    (Submodule.equivMapOfInjective M.subtype Subtype.val_injective (LinearMap.ker Ψ)).finrank_eq.symm
  change Module.finrank K M - m ≤ Module.finrank K ((LinearMap.ker Ψ).map M.subtype)
  omega

private lemma isCoprime_of_dvd {a b c d : Polynomial (ZMod 2)}
    (h : IsCoprime a b) (hc : c ∣ a) (hd : d ∣ b) : IsCoprime c d := by
  rcases h with ⟨u, v, huv⟩
  rcases hc with ⟨a', rfl⟩
  rcases hd with ⟨b', rfl⟩
  exact ⟨u * a', v * b', by rw [← huv]; ring⟩

private lemma sum_fin_dite_eq {k m : ℕ} (hkm : k ≤ m) (f : Fin k → ℕ) :
    ∑ i : Fin m, (if hi : i.val < k then f ⟨i.val, hi⟩ else 0) = ∑ j : Fin k, f j := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m)) (fun i => i.val < k)]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < k),
      (if hi : i.val < k then f ⟨i.val, hi⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hnot : ¬ i.val < k := (Finset.mem_filter.mp hi).2
    rw [dif_neg hnot]
  rw [h0, add_zero]
  refine Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun i₁ _ i₂ _ heq => Fin.ext (Fin.mk.inj heq))
    (fun j _ => ⟨⟨j.val, lt_of_lt_of_le j.isLt hkm⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, Fin.ext rfl⟩)
    (fun i hi => by rw [dif_pos (Finset.mem_filter.mp hi).2])

private lemma poly_factor_power (p : Polynomial (ZMod 2)) (hp : Irreducible p) :
    ∀ (deg : ℕ) (q : Polynomial (ZMod 2)), q.natDegree ≤ deg → q ≠ 0 → p ∣ q →
      ∃ (e : ℕ) (q₂ : Polynomial (ZMod 2)), 1 ≤ e ∧ q = p ^ e * q₂ ∧ ¬ p ∣ q₂ := by
  intro deg
  induction deg with
  | zero =>
    intro q hdeg hq0 hdvd
    rcases hdvd with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := right_ne_zero_of_mul hq0
    have hpdeg : 1 ≤ p.natDegree := by
      by_contra h0
      have hpeq : p.natDegree = 0 := by omega
      have hpc := Polynomial.eq_C_of_natDegree_eq_zero hpeq
      have hc0 : p.coeff 0 ≠ 0 := fun h => hp.ne_zero (by rw [hpc, h, map_zero])
      have hc1 : p.coeff 0 = 1 := zmod2_eq_one_of_ne_zero hc0
      rw [hc1, map_one] at hpc
      exact hp.not_isUnit (hpc ▸ isUnit_one)
    rw [Polynomial.natDegree_mul hp.ne_zero hr0] at hdeg
    omega
  | succ deg ih =>
    intro q hdeg hq0 hdvd
    rcases hdvd with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := right_ne_zero_of_mul hq0
    have hpdeg : 1 ≤ p.natDegree := by
      by_contra h0
      have hpeq : p.natDegree = 0 := by omega
      have hpc := Polynomial.eq_C_of_natDegree_eq_zero hpeq
      have hc0 : p.coeff 0 ≠ 0 := fun h => hp.ne_zero (by rw [hpc, h, map_zero])
      have hc1 : p.coeff 0 = 1 := zmod2_eq_one_of_ne_zero hc0
      rw [hc1, map_one] at hpc
      exact hp.not_isUnit (hpc ▸ isUnit_one)
    have hrdeg : r.natDegree ≤ deg := by
      rw [Polynomial.natDegree_mul hp.ne_zero hr0] at hdeg; omega
    by_cases hpr : p ∣ r
    · rcases ih r hrdeg hr0 hpr with ⟨e, q₂, he, rfl, hndvd⟩
      exact ⟨e + 1, q₂, by omega, by rw [pow_succ', mul_assoc], hndvd⟩
    · exact ⟨1, r, le_rfl, by simp, hpr⟩

private lemma primary_cyclic_decomp {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n)
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (e : ℕ) :
    ∀ (dim : ℕ) (M : Submodule (ZMod 2) (Dual n)),
      Module.finrank (ZMod 2) M ≤ dim → M.map D' ≤ M →
      (∀ x ∈ M, Polynomial.aeval D' (p ^ e) x = 0) →
      ∃ (k : ℕ) (v : Fin k → Dual n) (d : Fin k → Polynomial (ZMod 2)),
        k * p.natDegree = Module.finrank (ZMod 2)
          (M ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) ∧
        (∀ i, v i ∈ M ∧ (d i).Monic ∧ Polynomial.aeval D' (d i) (v i) = 0 ∧ d i ∣ p ^ e) ∧
        (⨆ i : Fin k, cycSpan D' (v i) (d i).natDegree) = M ∧
        (∑ i : Fin k, (d i).natDegree) = Module.finrank (ZMod 2) M := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hp_monic : p.Monic := by
    rw [Polynomial.Monic]
    exact zmod2_eq_one_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp_ne)
  have hp_deg_pos : 0 < p.natDegree := by
    by_contra h0
    have hpeq : p.natDegree = 0 := by omega
    have hpc := Polynomial.eq_C_of_natDegree_eq_zero hpeq
    have hc0 : p.coeff 0 ≠ 0 := fun h => hp_ne (by rw [hpc, h, map_zero])
    have hc1 : p.coeff 0 = 1 := zmod2_eq_one_of_ne_zero hc0
    rw [hc1, map_one] at hpc
    exact hp.not_isUnit (hpc ▸ isUnit_one)
  intro dim
  induction dim with
  | zero =>
    intro M hdim _ _
    have hMbot : M = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    subst hMbot
    refine ⟨0, Fin.elim0, Fin.elim0, by rw [bot_inf_eq, finrank_bot]; simp, fun i => Fin.elim0 i, by simp, by simp⟩
  | succ dim ih =>
    intro M hdim hMinv hMann
    by_cases hMbot : M = ⊥
    · subst hMbot
      refine ⟨0, Fin.elim0, Fin.elim0, by rw [bot_inf_eq, finrank_bot]; simp, fun i => Fin.elim0 i, by simp, by simp⟩
    · have hex_e : ∃ r ≤ e, ∀ x ∈ M, Polynomial.aeval D' (p ^ r) x = 0 := ⟨e, le_rfl, hMann⟩
      classical
      let e₀ := Nat.find hex_e
      have he₀_spec : e₀ ≤ e ∧ ∀ x ∈ M, Polynomial.aeval D' (p ^ e₀) x = 0 := Nat.find_spec hex_e
      have he₀_pos : 1 ≤ e₀ := by
        by_contra h0
        have he0 : e₀ = 0 := by omega
        apply hMbot
        rw [eq_bot_iff]
        intro x hx
        have h1 := he₀_spec.2 x hx
        rw [he0, pow_zero, map_one] at h1
        exact (Submodule.mem_bot (ZMod 2)).mpr h1
      have hnot_prev : ¬ (∀ x ∈ M, Polynomial.aeval D' (p ^ (e₀ - 1)) x = 0) := by
        intro hprev
        have hlt : e₀ - 1 < e₀ := by omega
        exact Nat.find_min hex_e hlt ⟨by omega, hprev⟩
      push_neg at hnot_prev
      rcases hnot_prev with ⟨v₀, hv₀M, hv₀_ne⟩
      let u₀ := Polynomial.aeval D' (p ^ (e₀ - 1)) v₀
      have hu₀_ne : u₀ ≠ 0 := hv₀_ne
      have hex_x₀ : ∃ x₀ : Vec n, u₀ x₀ = 1 := by
        by_contra hall
        push_neg at hall
        apply hu₀_ne
        apply LinearMap.ext; intro x
        rcases zmod2_cases (u₀ x) with h0 | h1
        · exact h0
        · exact False.elim (hall x h1)
      rcases hex_x₀ with ⟨x₀, hx₀⟩
      let pe₀ : Polynomial (ZMod 2) := p ^ e₀
      have hpe₀_monic : pe₀.Monic := hp_monic.pow e₀
      have hpe₀_deg : pe₀.natDegree = e₀ * p.natDegree := by
        simp [pe₀, Polynomial.natDegree_pow]
      have hpe₀_ann : Polynomial.aeval D' pe₀ v₀ = 0 := he₀_spec.2 v₀ hv₀M
      let C : Submodule (ZMod 2) (Dual n) := cycSpan D' v₀ pe₀.natDegree
      have hCM : C ≤ M := cycSpan_le_of_inv D' M hMinv v₀ hv₀M _
      have hC_ann_dvd : ∀ f : Polynomial (ZMod 2), Polynomial.aeval D' f v₀ = 0 → pe₀ ∣ f := by
        intro f hf
        by_contra hndvd
        have hex_r : ∃ r < e₀, p ^ r ∣ f ∧ ¬ p ^ (r + 1) ∣ f := by
          have h0 : p ^ 0 ∣ f := by simp
          by_cases hf0 : f = 0
          · exact False.elim (hndvd (hf0 ▸ dvd_zero pe₀))
          · have hmax : ∃ r, r < e₀ ∧ p ^ r ∣ f ∧ ¬ p ^ (r + 1) ∣ f := by
              have hstep : ∀ k ≤ e₀, ¬ p ^ k ∣ f → ∃ r < k, p ^ r ∣ f ∧ ¬ p ^ (r + 1) ∣ f := by
                intro k
                induction k with
                | zero => intro _ h; exact False.elim (h (by simp))
                | succ k ihk =>
                  intro hkle hnk
                  by_cases hk : p ^ k ∣ f
                  · exact ⟨k, Nat.lt_succ_self k, hk, hnk⟩
                  · rcases ihk (by omega) hk with ⟨r, hr, h1, h2⟩
                    exact ⟨r, by omega, h1, h2⟩
              exact hstep e₀ le_rfl hndvd
            exact hmax
        rcases hex_r with ⟨r, hr_lt, ⟨g, rfl⟩, hndvd1⟩
        have hndvd_p : ¬ p ∣ g := by
          intro hpg
          apply hndvd1
          rcases hpg with ⟨g', rfl⟩
          exact ⟨g', by rw [pow_succ, mul_assoc]⟩
        have hcop : IsCoprime p g := hp.coprime_iff_not_dvd.mpr hndvd_p
        have hcop_pow : IsCoprime (p ^ e₀) g := hcop.pow_left
        rcases hcop_pow with ⟨a, b, hab⟩
        have hu0 : u₀ = 0 := by
          have h1 : Polynomial.aeval D' (p ^ (e₀ - 1)) v₀ =
              Polynomial.aeval D' ((a * p ^ e₀ + b * g) * p ^ (e₀ - 1)) v₀ := by
            rw [hab, one_mul]
          rw [show u₀ = Polynomial.aeval D' (p ^ (e₀ - 1)) v₀ from rfl, h1]
          have hsplit : (a * p ^ e₀ + b * g) * p ^ (e₀ - 1) =
              (a * p ^ (e₀ - 1)) * p ^ e₀ + (b * p ^ (e₀ - 1 - r)) * (p ^ r * g) := by
            have hpow_eq : p ^ (e₀ - 1 - r) * p ^ r = p ^ (e₀ - 1) := by
              rw [← pow_add]; congr 1; omega
            calc (a * p ^ e₀ + b * g) * p ^ (e₀ - 1)
                = a * p ^ (e₀ - 1) * p ^ e₀ + b * g * p ^ (e₀ - 1) := by ring
              _ = a * p ^ (e₀ - 1) * p ^ e₀ + b * g * (p ^ (e₀ - 1 - r) * p ^ r) := by rw [hpow_eq]
              _ = a * p ^ (e₀ - 1) * p ^ e₀ + b * p ^ (e₀ - 1 - r) * (p ^ r * g) := by ring
          have ht1 : Polynomial.aeval D' (a * p ^ (e₀ - 1) * p ^ e₀) v₀ = 0 := by
            rw [map_mul, end_mul_apply, hpe₀_ann, map_zero]
          have ht2 : Polynomial.aeval D' (b * p ^ (e₀ - 1 - r) * (p ^ r * g)) v₀ = 0 := by
            rw [map_mul, end_mul_apply, hf, map_zero]
          rw [hsplit, map_add, LinearMap.add_apply, ht1, ht2, add_zero]
        exact hu₀_ne hu0
      have hC_finrank : Module.finrank (ZMod 2) C = pe₀.natDegree := by
        have hli : LinearIndependent (ZMod 2) (fun r : Fin pe₀.natDegree => (D' ^ r.val) v₀) := by
          rw [Fintype.linearIndependent_iff]
          intro c hsum
          let f : Polynomial (ZMod 2) := ∑ r : Fin pe₀.natDegree, Polynomial.C (c r) * Polynomial.X ^ r.val
          have hfeval : Polynomial.aeval D' f v₀ = 0 := by
            simp only [f, map_sum, map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
              map_pow, Polynomial.aeval_X, smul_mul_assoc, one_mul, LinearMap.sum_apply,
              LinearMap.smul_apply]
            exact hsum
          have hdvd : pe₀ ∣ f := hC_ann_dvd f hfeval
          have hf0 : f = 0 := by
            by_contra hne
            have hdeg_le : pe₀.natDegree ≤ f.natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
            have hpos : 0 < pe₀.natDegree := by rw [hpe₀_deg]; exact Nat.mul_pos he₀_pos hp_deg_pos
            have hdeg_lt : f.natDegree < pe₀.natDegree := by
              refine natDegree_sum_lt_of_forall_lt Finset.univ _ pe₀.natDegree hpos (fun r _ => ?_)
              by_cases hcr : c r = 0
              · simp [hcr, hpos]
              · have hcr1 : c r = 1 := zmod2_eq_one_of_ne_zero hcr
                simp [hcr1, r.isLt]
            omega
          intro r
          have hcoeff : f.coeff r.val = 0 := by rw [hf0, Polynomial.coeff_zero]
          rw [coeff_fin_sum_C_X_pow] at hcoeff
          exact hcoeff
        have hC_eq : C = Submodule.span (ZMod 2) (Set.range (fun r : Fin pe₀.natDegree => (D' ^ r.val) v₀)) := by
          unfold C cycSpan
          congr 1; ext x
          simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range, Set.mem_range]
          exact ⟨fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, h⟩, fun ⟨r, h⟩ => ⟨r.val, r.isLt, h⟩⟩
        rw [hC_eq, finrank_span_eq_card hli, Fintype.card_fin]
      let evX : Dual n →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun a => a x₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      let gPsi : Fin pe₀.natDegree → Dual n →ₗ[ZMod 2] ZMod 2 := fun r => evX.comp (D' ^ r.val)
      let Ψ : M →ₗ[ZMod 2] (Fin pe₀.natDegree → ZMod 2) :=
        LinearMap.pi (fun r : Fin pe₀.natDegree => (gPsi r).comp M.subtype)
      let W' : Submodule (ZMod 2) (Dual n) := (LinearMap.ker Ψ).map M.subtype
      have hW'M : W' ≤ M := by rintro _ ⟨w, _, rfl⟩; exact w.2
      have hW'_iff : ∀ w : Dual n, w ∈ W' ↔ w ∈ M ∧ ∀ f : Polynomial (ZMod 2), (Polynomial.aeval D' f w) x₀ = 0 := by
        intro w
        constructor
        · rintro ⟨⟨w, hwM⟩, hwker, rfl⟩
          refine ⟨hwM, ?_⟩
          intro f
          change (Polynomial.aeval D' f w) x₀ = 0
          have hdiv : f %ₘ pe₀ + pe₀ * (f /ₘ pe₀) = f := Polynomial.modByMonic_add_div f pe₀
          have heval : Polynomial.aeval D' f w = Polynomial.aeval D' (f %ₘ pe₀) w := by
            conv_lhs => rw [← hdiv]
            rw [map_add, map_mul, LinearMap.add_apply, end_mul_apply]
            have hcomm : Polynomial.aeval D' pe₀ (Polynomial.aeval D' (f /ₘ pe₀) w) =
                Polynomial.aeval D' (f /ₘ pe₀) (Polynomial.aeval D' pe₀ w) := by
              change (Polynomial.aeval D' pe₀ * Polynomial.aeval D' (f /ₘ pe₀)) w =
                (Polynomial.aeval D' (f /ₘ pe₀) * Polynomial.aeval D' pe₀) w
              rw [← map_mul, ← map_mul, mul_comm]
            rw [hcomm, he₀_spec.2 w hwM, map_zero, add_zero]
          rw [heval]
          by_cases h0 : f %ₘ pe₀ = 0
          · simp [h0]
          · have hlt : (f %ₘ pe₀).natDegree < pe₀.natDegree :=
              natDegree_modByMonic_lt_of_ne_zero f pe₀ hpe₀_monic h0
            rw [Polynomial.as_sum_range' (f %ₘ pe₀) pe₀.natDegree hlt, map_sum, LinearMap.sum_apply,
              LinearMap.sum_apply, Finset.sum_range]
            refine Finset.sum_eq_zero (fun r _ => ?_)
            simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
              smul_mul_assoc, one_mul, LinearMap.smul_apply, smul_eq_mul]
            have hr0 : ((D' ^ r.val) w) x₀ = 0 := congrFun hwker r
            rw [hr0, mul_zero]
        · rintro ⟨hwM, hall⟩
          refine ⟨⟨w, hwM⟩, ?_, rfl⟩
          ext r
          change ((D' ^ r.val) w) x₀ = 0
          simpa using hall ((Polynomial.X : Polynomial (ZMod 2)) ^ r.val)
      have hW'_inv : W'.map D' ≤ W' := by
        rintro _ ⟨w, hw, rfl⟩
        rcases (hW'_iff w).mp hw with ⟨hwM, hall⟩
        rw [hW'_iff]
        refine ⟨hMinv ⟨w, hwM, rfl⟩, fun f => ?_⟩
        have heq : Polynomial.aeval D' f (D' w) = Polynomial.aeval D' (f * Polynomial.X) w := by
          simp [map_mul, end_mul_apply]
        rw [heq]
        exact hall (f * Polynomial.X)
      have hdisj : C ⊓ W' = ⊥ := by
        rw [eq_bot_iff]
        rintro w ⟨hwC, hwW'⟩
        by_contra hw0
        have hw_ne : w ≠ 0 := fun h => hw0 ((Submodule.mem_bot (ZMod 2)).mpr h)
        have hex_f : ∃ f : Polynomial (ZMod 2), w = Polynomial.aeval D' f v₀ := by
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hwC
          · rintro _ ⟨r, _, rfl⟩; exact ⟨Polynomial.X ^ r, by simp⟩
          · exact ⟨0, by simp⟩
          · rintro _ _ _ _ ⟨f₁, rfl⟩ ⟨f₂, rfl⟩; exact ⟨f₁ + f₂, by simp⟩
          · rintro c _ _ ⟨f, rfl⟩; exact ⟨Polynomial.C c * f, by simp [Algebra.algebraMap_eq_smul_one]⟩
        rcases hex_f with ⟨f, rfl⟩
        have hndvd : ¬ pe₀ ∣ f := fun hdvd => by
          rcases hdvd with ⟨g, rfl⟩
          apply hw_ne
          rw [map_mul, end_mul_apply]
          have hcomm : Polynomial.aeval D' pe₀ (Polynomial.aeval D' g v₀) =
              Polynomial.aeval D' g (Polynomial.aeval D' pe₀ v₀) := by
            change (Polynomial.aeval D' pe₀ * Polynomial.aeval D' g) v₀ =
              (Polynomial.aeval D' g * Polynomial.aeval D' pe₀) v₀
            rw [← map_mul, ← map_mul, mul_comm]
          rw [hcomm, hpe₀_ann, map_zero]
        have hex_r : ∃ r < e₀, p ^ r ∣ f ∧ ¬ p ^ (r + 1) ∣ f := by
          have hstep : ∀ k ≤ e₀, ¬ p ^ k ∣ f → ∃ r < k, p ^ r ∣ f ∧ ¬ p ^ (r + 1) ∣ f := by
            intro k
            induction k with
            | zero => intro _ h; exact False.elim (h (by simp))
            | succ k ihk =>
              intro hkle hnk
              by_cases hk : p ^ k ∣ f
              · exact ⟨k, Nat.lt_succ_self k, hk, hnk⟩
              · rcases ihk (by omega) hk with ⟨r, hr, h1, h2⟩
                exact ⟨r, by omega, h1, h2⟩
          exact hstep e₀ le_rfl hndvd
        rcases hex_r with ⟨r, hr_lt, ⟨g, rfl⟩, hndvd1⟩
        have hndvd_p : ¬ p ∣ g := fun ⟨g', hg'⟩ => hndvd1 ⟨g', by rw [hg', pow_succ, mul_assoc]⟩
        rcases (hp.coprime_iff_not_dvd.mpr hndvd_p).pow_left (m := e₀) with ⟨a, b, hab⟩
        have hu_eq : Polynomial.aeval D' (b * p ^ (e₀ - 1 - r)) (Polynomial.aeval D' (p ^ r * g) v₀) = u₀ := by
          have h1 : (b * p ^ (e₀ - 1 - r)) * (p ^ r * g) =
              p ^ (e₀ - 1) - (a * p ^ (e₀ - 1)) * p ^ e₀ := by
            have hpow_eq : p ^ (e₀ - 1 - r) * p ^ r = p ^ (e₀ - 1) := by
              rw [← pow_add]; congr 1; omega
            have hbg : b * g = 1 - a * p ^ e₀ := eq_sub_of_add_eq' hab
            calc (b * p ^ (e₀ - 1 - r)) * (p ^ r * g)
                = (b * g) * (p ^ (e₀ - 1 - r) * p ^ r) := by ring
              _ = (1 - a * p ^ e₀) * p ^ (e₀ - 1) := by rw [hbg, hpow_eq]
              _ = p ^ (e₀ - 1) - a * p ^ (e₀ - 1) * p ^ e₀ := by ring
          rw [← end_mul_apply, ← map_mul, h1, map_sub, map_mul, LinearMap.sub_apply,
            end_mul_apply, hpe₀_ann, map_zero, sub_zero]
        have h0 := ((hW'_iff _).mp hwW').2 (b * p ^ (e₀ - 1 - r))
        rw [hu_eq, hx₀] at h0
        exact (by decide : (1 : ZMod 2) ≠ 0) h0
      have hW'_finrank_ge : Module.finrank (ZMod 2) M - pe₀.natDegree ≤ Module.finrank (ZMod 2) W' :=
        finrank_ker_eval_ge M pe₀.natDegree gPsi
      have hsup_eq : C ⊔ W' = M := by
        have hle : C ⊔ W' ≤ M := sup_le hCM hW'M
        have hdim_sup := Submodule.finrank_sup_add_finrank_inf_eq C W'
        rw [hdisj, finrank_bot, add_zero, hC_finrank] at hdim_sup
        have hC_le : pe₀.natDegree ≤ Module.finrank (ZMod 2) M := by
          rw [← hC_finrank]; exact Submodule.finrank_mono hCM
        have heq_dim : Module.finrank (ZMod 2) (C ⊔ W' : Submodule (ZMod 2) (Dual n)) =
            Module.finrank (ZMod 2) M := by
          have := Submodule.finrank_mono hle
          omega
        exact Submodule.eq_of_le_of_finrank_eq hle heq_dim
      have hW'_dim : Module.finrank (ZMod 2) W' + pe₀.natDegree = Module.finrank (ZMod 2) M := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq C W'
        rw [hsup_eq, hdisj, finrank_bot, add_zero, hC_finrank] at h
        omega
      have hW'_lt : Module.finrank (ZMod 2) W' ≤ dim := by
        have hpos : 0 < pe₀.natDegree := by rw [hpe₀_deg]; exact Nat.mul_pos he₀_pos hp_deg_pos
        omega
      have hC_socle : Module.finrank (ZMod 2)
          (C ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) = p.natDegree := by
        let G : Submodule (ZMod 2) (Dual n) := cycSpan D' u₀ p.natDegree
        have hG_eq : C ⊓ LinearMap.ker (Polynomial.aeval D' p) = G := by
          apply le_antisymm
          · rintro w ⟨hwC, hwker⟩
            have hex_f : ∃ f : Polynomial (ZMod 2), w = Polynomial.aeval D' f v₀ := by
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hwC
              · rintro _ ⟨r, _, rfl⟩; exact ⟨Polynomial.X ^ r, by simp⟩
              · exact ⟨0, by simp⟩
              · rintro _ _ _ _ ⟨f₁, rfl⟩ ⟨f₂, rfl⟩; exact ⟨f₁ + f₂, by simp⟩
              · rintro c _ _ ⟨f, rfl⟩; exact ⟨Polynomial.C c * f, by simp [Algebra.algebraMap_eq_smul_one]⟩
            rcases hex_f with ⟨f, rfl⟩
            have hpf0 : Polynomial.aeval D' (p * f) v₀ = 0 := by
              rw [map_mul, end_mul_apply]; exact hwker
            have hdvd : p ^ e₀ ∣ p * f := hC_ann_dvd (p * f) hpf0
            have hdvd' : p ^ (e₀ - 1) ∣ f := by
              rcases hdvd with ⟨q, hq⟩
              have hpeq : p ^ e₀ = p * p ^ (e₀ - 1) := by
                conv_lhs => rw [show e₀ = (e₀ - 1) + 1 by omega, pow_succ']
              rw [hpeq, mul_assoc] at hq
              exact ⟨q, mul_left_cancel₀ hp_ne hq⟩
            rcases hdvd' with ⟨q, rfl⟩
            have heval : Polynomial.aeval D' (p ^ (e₀ - 1) * q) v₀ = Polynomial.aeval D' q u₀ := by
              rw [mul_comm, map_mul, end_mul_apply]
            rw [heval]
            have hu_ann : Polynomial.aeval D' p u₀ = 0 := by
              change Polynomial.aeval D' p (Polynomial.aeval D' (p ^ (e₀ - 1)) v₀) = 0
              rw [← end_mul_apply, ← map_mul, show p * p ^ (e₀ - 1) = p ^ e₀ by
                conv_rhs => rw [show e₀ = (e₀ - 1) + 1 by omega, pow_succ']]
              exact hpe₀_ann
            exact cycSpan_inv_of_ann D' u₀ p hp_monic hu_ann q
          · refine Submodule.span_le.mpr ?_
            rintro _ ⟨r, _, rfl⟩
            dsimp only
            refine ⟨?_, ?_⟩
            · have heq : (D' ^ r) u₀ = Polynomial.aeval D' (Polynomial.X ^ r * p ^ (e₀ - 1)) v₀ := by
                simp [u₀, map_mul, end_mul_apply]
              rw [heq]
              exact cycSpan_inv_of_ann D' v₀ pe₀ hpe₀_monic hpe₀_ann _
            · change Polynomial.aeval D' p ((D' ^ r) u₀) = 0
              have heq : Polynomial.aeval D' p ((D' ^ r) u₀) =
                  Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) ^ r) (Polynomial.aeval D' pe₀ v₀) := by
                have hXr : Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) ^ r) = D' ^ r := by simp
                rw [← hXr, show u₀ = Polynomial.aeval D' (p ^ (e₀ - 1)) v₀ from rfl,
                  ← end_mul_apply, ← end_mul_apply, ← map_mul, ← map_mul,
                  ← end_mul_apply, ← map_mul]
                congr 2
                have hpeq : p * p ^ (e₀ - 1) = pe₀ := by
                  show p * p ^ (e₀ - 1) = p ^ e₀
                  conv_rhs => rw [show e₀ = (e₀ - 1) + 1 by omega, pow_succ']
                rw [← hpeq]; ring
              rw [heq, hpe₀_ann, map_zero]
        rw [hG_eq]
        have hli : LinearIndependent (ZMod 2) (fun r : Fin p.natDegree => (D' ^ r.val) u₀) := by
          rw [Fintype.linearIndependent_iff]
          intro c hsum
          let f : Polynomial (ZMod 2) := ∑ r : Fin p.natDegree, Polynomial.C (c r) * Polynomial.X ^ r.val
          have hfeval : Polynomial.aeval D' (f * p ^ (e₀ - 1)) v₀ = 0 := by
            rw [map_mul, end_mul_apply]
            change Polynomial.aeval D' f u₀ = 0
            simp only [f, map_sum, map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
              map_pow, Polynomial.aeval_X, smul_mul_assoc, one_mul, LinearMap.sum_apply,
              LinearMap.smul_apply]
            exact hsum
          have hdvd : p ^ e₀ ∣ f * p ^ (e₀ - 1) := hC_ann_dvd _ hfeval
          have hpf : p ∣ f := by
            rcases hdvd with ⟨q, hq⟩
            have hpeq : p ^ e₀ = p * p ^ (e₀ - 1) := by
              conv_lhs => rw [show e₀ = (e₀ - 1) + 1 by omega, pow_succ']
            rw [hpeq] at hq
            have hmul : f * p ^ (e₀ - 1) = (p * q) * p ^ (e₀ - 1) := by rw [hq]; ring
            exact ⟨q, mul_right_cancel₀ (pow_ne_zero _ hp_ne) hmul⟩
          have hf0 : f = 0 := by
            by_contra hne
            have hdeg_le : p.natDegree ≤ f.natDegree := Polynomial.natDegree_le_of_dvd hpf hne
            have hdeg_lt : f.natDegree < p.natDegree := by
              refine natDegree_sum_lt_of_forall_lt Finset.univ _ p.natDegree hp_deg_pos (fun r _ => ?_)
              by_cases hcr : c r = 0
              · simp [hcr, hp_deg_pos]
              · have hcr1 : c r = 1 := zmod2_eq_one_of_ne_zero hcr
                simp [hcr1, r.isLt]
            omega
          intro r
          have hcoeff : f.coeff r.val = 0 := by rw [hf0, Polynomial.coeff_zero]
          rw [coeff_fin_sum_C_X_pow] at hcoeff
          exact hcoeff
        have hG_eq' : G = Submodule.span (ZMod 2) (Set.range (fun r : Fin p.natDegree => (D' ^ r.val) u₀)) := by
          unfold G cycSpan
          congr 1; ext x
          simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range, Set.mem_range]
          exact ⟨fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, h⟩, fun ⟨r, h⟩ => ⟨r.val, r.isLt, h⟩⟩
        rw [hG_eq', finrank_span_eq_card hli, Fintype.card_fin]
      have hsocle_split :
          Module.finrank (ZMod 2) (C ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) +
          Module.finrank (ZMod 2) (W' ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) =
          Module.finrank (ZMod 2) (M ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) := by
        have hsup_s : (C ⊓ LinearMap.ker (Polynomial.aeval D' p)) ⊔ (W' ⊓ LinearMap.ker (Polynomial.aeval D' p)) =
            M ⊓ LinearMap.ker (Polynomial.aeval D' p) := by
          apply le_antisymm
          · exact sup_le (inf_le_inf_right _ hCM) (inf_le_inf_right _ hW'M)
          · rintro x ⟨hxM, hxker⟩
            rw [← hsup_eq] at hxM
            rcases Submodule.mem_sup.mp hxM with ⟨c, hc, w, hw, rfl⟩
            have hCinv : C.map D' ≤ C := cycSpan_map_le D' v₀ pe₀ hpe₀_monic hpe₀_ann
            have hCaeval : Polynomial.aeval D' p c ∈ C := poly_inv_of_end_inv D' C hCinv p ⟨c, hc, rfl⟩
            have hW'aeval : Polynomial.aeval D' p w ∈ W' := poly_inv_of_end_inv D' W' hW'_inv p ⟨w, hw, rfl⟩
            have hsum0 : Polynomial.aeval D' p c + Polynomial.aeval D' p w = 0 := by
              rw [← map_add]; exact hxker
            have hc0 : Polynomial.aeval D' p c = 0 := by
              have hmem : Polynomial.aeval D' p c ∈ C ⊓ W' := by
                refine ⟨hCaeval, ?_⟩
                have heq : Polynomial.aeval D' p c = -Polynomial.aeval D' p w := eq_neg_of_add_eq_zero_left hsum0
                rw [heq]; exact W'.neg_mem hW'aeval
              rw [hdisj] at hmem
              exact (Submodule.mem_bot (ZMod 2)).mp hmem
            have hw0 : Polynomial.aeval D' p w = 0 := by rw [hc0, zero_add] at hsum0; exact hsum0
            exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨hc, hc0⟩) (Submodule.mem_sup_right ⟨hw, hw0⟩)
        have hinf_s : (C ⊓ LinearMap.ker (Polynomial.aeval D' p)) ⊓
            (W' ⊓ LinearMap.ker (Polynomial.aeval D' p)) = ⊥ := by
          rw [eq_bot_iff]
          rintro x ⟨⟨hxC, _⟩, ⟨hxW', _⟩⟩
          exact (hdisj ▸ (⟨hxC, hxW'⟩ : x ∈ C ⊓ W'))
        have h := Submodule.finrank_sup_add_finrank_inf_eq
          (C ⊓ LinearMap.ker (Polynomial.aeval D' p)) (W' ⊓ LinearMap.ker (Polynomial.aeval D' p))
        rw [hsup_s, hinf_s, finrank_bot, add_zero] at h
        exact h.symm
      rcases ih W' hW'_lt hW'_inv (fun x hx => hMann x (hW'M hx)) with ⟨k', v', d', hk', hv', hspan', hsum'⟩
      let vNew : Fin (k' + 1) → Dual n := fun i =>
        if hi : i.val = 0 then v₀ else v' ⟨i.val - 1, by omega⟩
      let dNew : Fin (k' + 1) → Polynomial (ZMod 2) := fun i =>
        if hi : i.val = 0 then pe₀ else d' ⟨i.val - 1, by omega⟩
      refine ⟨k' + 1, vNew, dNew, ?_, ?_, ?_, ?_⟩
      · rw [add_mul, one_mul, hk', ← hC_socle]
        omega
      · intro i
        by_cases hi : i.val = 0
        · simp only [vNew, dNew, hi, dite_true]
          exact ⟨hv₀M, hpe₀_monic, hpe₀_ann, pow_dvd_pow p he₀_spec.1⟩
        · simp only [vNew, dNew, hi, dite_false]
          rcases hv' ⟨i.val - 1, by omega⟩ with ⟨hjM, hjm, hja, hjd⟩
          exact ⟨hW'M hjM, hjm, hja, hjd⟩
      · rw [← hsup_eq, ← hspan']
        apply le_antisymm
        · refine iSup_le (fun i => ?_)
          by_cases hi : i.val = 0
          · simp only [vNew, dNew, hi, dite_true]; exact le_sup_left
          · simp only [vNew, dNew, hi, dite_false]
            exact (le_iSup (fun j => cycSpan D' (v' j) (d' j).natDegree) ⟨i.val - 1, by omega⟩).trans le_sup_right
        · refine sup_le ?_ ?_
          · have h0 := le_iSup (fun i : Fin (k' + 1) => cycSpan D' (vNew i) (dNew i).natDegree) ⟨0, Nat.succ_pos k'⟩
            simpa [vNew, dNew, C] using h0
          · refine iSup_le (fun j => ?_)
            have hj := le_iSup (fun i : Fin (k' + 1) => cycSpan D' (vNew i) (dNew i).natDegree) ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
            simpa [vNew, dNew] using hj
      · rw [Fin.sum_univ_succ]
        have h0 : (dNew 0).natDegree = pe₀.natDegree := by simp [dNew]
        have hs : ∀ j : Fin k', (dNew j.succ).natDegree = (d' j).natDegree := by
          intro j; simp [dNew]
        rw [h0, Finset.sum_congr rfl (fun j _ => hs j), hsum']
        omega

private lemma cyclic_decomp_of_poly {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n) (gBound : ℕ) :
    ∀ (deg : ℕ) (q : Polynomial (ZMod 2)) (M : Submodule (ZMod 2) (Dual n)),
      q.natDegree ≤ deg → q ≠ 0 → M.map D' ≤ M →
      (∀ x ∈ M, Polynomial.aeval D' q x = 0) →
      (∀ p : Polynomial (ZMod 2), Irreducible p →
        Module.finrank (ZMod 2) (M ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) /
          p.natDegree ≤ gBound) →
      ∃ (k : ℕ) (v : Fin k → Dual n) (d : Fin k → Polynomial (ZMod 2)),
        k ≤ gBound ∧
        (∀ i, v i ∈ M ∧ (d i).Monic ∧ Polynomial.aeval D' (d i) (v i) = 0 ∧ d i ∣ q) ∧
        (⨆ i : Fin k, cycSpan D' (v i) (d i).natDegree) = M ∧
        (∑ i : Fin k, (d i).natDegree) = Module.finrank (ZMod 2) M := by
  intro deg
  induction deg with
  | zero =>
    intro q M hdeg hq0 _ hMann _
    have hqc := Polynomial.eq_C_of_natDegree_eq_zero (by omega : q.natDegree = 0)
    have hc1 : q.coeff 0 = 1 := zmod2_eq_one_of_ne_zero (fun h => hq0 (by rw [hqc, h, map_zero]))
    have hq1 : q = 1 := by rw [hqc, hc1, map_one]
    have hMbot : M = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h := hMann x hx
      rw [hq1, map_one] at h
      exact (Submodule.mem_bot (ZMod 2)).mpr h
    subst hMbot
    refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, fun i => Fin.elim0 i, by simp, by simp⟩
  | succ deg ih =>
    intro q M hdeg hq0 hMinv hMann hsocle
    by_cases hqdeg : q.natDegree = 0
    · have hqc := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
      have hc1 : q.coeff 0 = 1 := zmod2_eq_one_of_ne_zero (fun h => hq0 (by rw [hqc, h, map_zero]))
      have hq1 : q = 1 := by rw [hqc, hc1, map_one]
      have hMbot : M = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h := hMann x hx
        rw [hq1, map_one] at h
        exact (Submodule.mem_bot (ZMod 2)).mpr h
      subst hMbot
      refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, fun i => Fin.elim0 i, by simp, by simp⟩
    · have hnotu : ¬ IsUnit q := by
        intro hu
        have := Polynomial.natDegree_eq_zero_of_isUnit hu
        omega
      rcases WfDvdMonoid.exists_irreducible_factor hnotu hq0 with ⟨p, hp, hpq⟩
      rcases poly_factor_power p hp (deg + 1) q hdeg hq0 hpq with ⟨e, q₂, he, rfl, hndvd⟩
      have hq₂0 : q₂ ≠ 0 := right_ne_zero_of_mul hq0
      have hp_deg_pos : 0 < p.natDegree := by
        by_contra h0
        have hpc := Polynomial.eq_C_of_natDegree_eq_zero (by omega : p.natDegree = 0)
        have hc1 : p.coeff 0 = 1 := zmod2_eq_one_of_ne_zero (fun h => hp.ne_zero (by rw [hpc, h, map_zero]))
        exact hp.not_isUnit (by rw [hpc, hc1, map_one]; exact isUnit_one)
      have hq₂_deg : q₂.natDegree ≤ deg := by
        rw [Polynomial.natDegree_mul (pow_ne_zero e hp.ne_zero) hq₂0, Polynomial.natDegree_pow] at hdeg
        have : 1 ≤ e * p.natDegree := Nat.mul_pos he hp_deg_pos
        omega
      have hcop : IsCoprime (p ^ e) q₂ := (hp.coprime_iff_not_dvd.mpr hndvd).pow_left
      let M₁ : Submodule (ZMod 2) (Dual n) := M ⊓ LinearMap.ker (Polynomial.aeval D' (p ^ e))
      let M₂ : Submodule (ZMod 2) (Dual n) := M ⊓ LinearMap.ker (Polynomial.aeval D' q₂)
      have hM₁_inv : M₁.map D' ≤ M₁ := by
        rintro _ ⟨x, ⟨hxM, hxK⟩, rfl⟩
        refine ⟨hMinv ⟨x, hxM, rfl⟩, ?_⟩
        change Polynomial.aeval D' (p ^ e) (D' x) = 0
        have hcomm : Polynomial.aeval D' (p ^ e) (D' x) = D' (Polynomial.aeval D' (p ^ e) x) := by
          have h : Polynomial.aeval D' ((p ^ e) * (Polynomial.X : Polynomial (ZMod 2))) =
              Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) * (p ^ e)) := by rw [mul_comm]
          simpa [map_mul, Polynomial.aeval_X, end_mul_apply] using LinearMap.congr_fun h x
        rw [hcomm, hxK, map_zero]
      have hM₂_inv : M₂.map D' ≤ M₂ := by
        rintro _ ⟨x, ⟨hxM, hxK⟩, rfl⟩
        refine ⟨hMinv ⟨x, hxM, rfl⟩, ?_⟩
        change Polynomial.aeval D' q₂ (D' x) = 0
        have hcomm : Polynomial.aeval D' q₂ (D' x) = D' (Polynomial.aeval D' q₂ x) := by
          have h : Polynomial.aeval D' (q₂ * (Polynomial.X : Polynomial (ZMod 2))) =
              Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) * q₂) := by rw [mul_comm]
          simpa [map_mul, Polynomial.aeval_X, end_mul_apply] using LinearMap.congr_fun h x
        rw [hcomm, hxK, map_zero]
      have hM_aeval_inv : ∀ f : Polynomial (ZMod 2), M.map (Polynomial.aeval D' f) ≤ M :=
        poly_inv_of_end_inv D' M hMinv
      obtain ⟨a, b, hab⟩ := hcop
      have hsup : M₁ ⊔ M₂ = M := by
        apply le_antisymm
        · exact sup_le inf_le_left inf_le_left
        · intro x hx
          have hdecomp : x = Polynomial.aeval D' (b * q₂) x + Polynomial.aeval D' (a * p ^ e) x := by
            rw [← LinearMap.add_apply, ← map_add, add_comm, hab, map_one]; rfl
          rw [hdecomp]
          refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨hM_aeval_inv (b * q₂) ⟨x, hx, rfl⟩, ?_⟩)
            (Submodule.mem_sup_right ⟨hM_aeval_inv (a * p ^ e) ⟨x, hx, rfl⟩, ?_⟩)
          · change Polynomial.aeval D' (p ^ e) (Polynomial.aeval D' (b * q₂) x) = 0
            rw [← end_mul_apply, ← map_mul]
            have hr : p ^ e * (b * q₂) = b * (p ^ e * q₂) := by ring
            rw [hr, map_mul, end_mul_apply, hMann x hx, map_zero]
          · change Polynomial.aeval D' q₂ (Polynomial.aeval D' (a * p ^ e) x) = 0
            rw [← end_mul_apply, ← map_mul]
            have hr : q₂ * (a * p ^ e) = a * (p ^ e * q₂) := by ring
            rw [hr, map_mul, end_mul_apply, hMann x hx, map_zero]
      have hinf : M₁ ⊓ M₂ = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
        have hx0 : x = 0 := by
          have := LinearMap.congr_fun (congrArg (Polynomial.aeval D') hab) x
          simp only [map_add, map_mul, map_one, LinearMap.add_apply, end_mul_apply,
            end_one_apply] at this
          have h1' : Polynomial.aeval D' (p ^ e) x = 0 := h1
          have h2' : Polynomial.aeval D' q₂ x = 0 := h2
          rw [h1', h2', map_zero, map_zero, add_zero] at this
          exact this.symm
        exact (Submodule.mem_bot (ZMod 2)).mpr hx0
      have hdim_sum : Module.finrank (ZMod 2) M₁ + Module.finrank (ZMod 2) M₂ =
          Module.finrank (ZMod 2) M := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq M₁ M₂
        rw [hsup, hinf, finrank_bot, add_zero] at h
        exact h.symm
      rcases primary_cyclic_decomp D' p hp e (Module.finrank (ZMod 2) M₁) M₁ le_rfl hM₁_inv
        (fun x hx => hx.2) with ⟨k₁, v₁, d₁, hk₁_eq, hv₁, hspan₁, hsum₁⟩
      have hk₁_le : k₁ ≤ gBound := by
        have hle_soc := hsocle p hp
        have hsub : M₁ ⊓ LinearMap.ker (Polynomial.aeval D' p) ≤ M ⊓ LinearMap.ker (Polynomial.aeval D' p) :=
          inf_le_inf_right _ inf_le_left
        have hdim_le := Submodule.finrank_mono hsub
        rw [← hk₁_eq] at hdim_le
        have hdiv : k₁ ≤ Module.finrank (ZMod 2)
            (M ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (Dual n)) / p.natDegree := by
          rw [Nat.le_div_iff_mul_le hp_deg_pos]
          exact hdim_le
        exact hdiv.trans hle_soc
      rcases ih q₂ M₂ hq₂_deg hq₂0 hM₂_inv (fun x hx => hx.2) (fun r hr => by
        have hsub : M₂ ⊓ LinearMap.ker (Polynomial.aeval D' r) ≤ M ⊓ LinearMap.ker (Polynomial.aeval D' r) :=
          inf_le_inf_right _ inf_le_left
        exact (Nat.div_le_div_right (Submodule.finrank_mono hsub)).trans (hsocle r hr)) with
        ⟨k₂, v₂, d₂, hk₂_le, hv₂, hspan₂, hsum₂⟩
      let k := max k₁ k₂
      let v : Fin k → Dual n := fun i =>
        (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) +
        (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0)
      let d : Fin k → Polynomial (ZMod 2) := fun i =>
        (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) *
        (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1)
      have hcop_i : ∀ i : Fin k,
          IsCoprime (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1)
            (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1) := by
        intro i
        by_cases h1 : i.val < k₁
        · by_cases h2 : i.val < k₂
          · simp only [h1, h2, dite_true]
            exact isCoprime_of_dvd ⟨a, b, hab⟩ (hv₁ ⟨i.val, h1⟩).2.2.2 (hv₂ ⟨i.val, h2⟩).2.2.2
          · simp only [h2, dite_false]; exact isCoprime_one_right
        · simp only [h1, dite_false]; exact isCoprime_one_left
      refine ⟨k, v, d, max_le hk₁_le hk₂_le, ?_, ?_, ?_⟩
      · intro i
        have h1M : (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) ∈ M := by
          split_ifs with h1
          · exact (hv₁ ⟨i.val, h1⟩).1.1
          · exact M.zero_mem
        have h2M : (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0) ∈ M := by
          split_ifs with h2
          · exact (hv₂ ⟨i.val, h2⟩).1.1
          · exact M.zero_mem
        have h1mon : (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1).Monic := by
          split_ifs with h1
          · exact (hv₁ ⟨i.val, h1⟩).2.1
          · exact Polynomial.monic_one
        have h2mon : (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1).Monic := by
          split_ifs with h2
          · exact (hv₂ ⟨i.val, h2⟩).2.1
          · exact Polynomial.monic_one
        have h1ann : Polynomial.aeval D' (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1)
            (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) = 0 := by
          split_ifs with h1
          · exact (hv₁ ⟨i.val, h1⟩).2.2.1
          · simp
        have h2ann : Polynomial.aeval D' (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1)
            (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0) = 0 := by
          split_ifs with h2
          · exact (hv₂ ⟨i.val, h2⟩).2.2.1
          · simp
        have h1dvd : (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) ∣ p ^ e := by
          split_ifs with h1
          · exact (hv₁ ⟨i.val, h1⟩).2.2.2
          · exact one_dvd _
        have h2dvd : (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1) ∣ q₂ := by
          split_ifs with h2
          · exact (hv₂ ⟨i.val, h2⟩).2.2.2
          · exact one_dvd _
        refine ⟨M.add_mem h1M h2M, h1mon.mul h2mon, ?_, mul_dvd_mul h1dvd h2dvd⟩
        dsimp only [d, v]
        rw [map_add]
        have ht1 : Polynomial.aeval D'
            ((if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) *
              (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1))
            (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) = 0 := by
          rw [mul_comm, map_mul, end_mul_apply, h1ann, map_zero]
        have ht2 : Polynomial.aeval D'
            ((if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) *
              (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1))
            (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0) = 0 := by
          rw [map_mul, end_mul_apply, h2ann, map_zero]
        rw [ht1, ht2, add_zero]
      · apply le_antisymm
        · refine iSup_le (fun i => cycSpan_le_of_inv D' M hMinv (v i) ?_ _)
          refine M.add_mem ?_ ?_
          · split_ifs with h1
            · exact (hv₁ ⟨i.val, h1⟩).1.1
            · exact M.zero_mem
          · split_ifs with h2
            · exact (hv₂ ⟨i.val, h2⟩).1.1
            · exact M.zero_mem
        · rw [← hsup, ← hspan₁, ← hspan₂]
          refine sup_le ?_ ?_
          · refine iSup_le (fun j => ?_)
            let i : Fin k := ⟨j.val, lt_of_lt_of_le j.isLt (le_max_left k₁ k₂)⟩
            have h1mon : (d₁ j).Monic := (hv₁ j).2.1
            have h2mon : (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1).Monic := by
              split_ifs with h2
              · exact (hv₂ ⟨i.val, h2⟩).2.1
              · exact Polynomial.monic_one
            have hdmon : (d i).Monic := by
              dsimp only [d]; rw [dif_pos j.isLt]; exact h1mon.mul h2mon
            have hdann : Polynomial.aeval D' (d i) (v i) = 0 := by
              dsimp only [d, v]
              have h1eq : (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) = d₁ j := by
                rw [dif_pos j.isLt]
              have hv1eq : (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) = v₁ j := by
                rw [dif_pos j.isLt]
              rw [h1eq, hv1eq, map_add]
              have ht1 : Polynomial.aeval D' (d₁ j * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1)) (v₁ j) = 0 := by
                rw [mul_comm, map_mul, end_mul_apply, (hv₁ j).2.2.1, map_zero]
              have ht2 : Polynomial.aeval D' (d₁ j * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1))
                  (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0) = 0 := by
                rw [map_mul, end_mul_apply]
                split_ifs with h2
                · rw [(hv₂ ⟨i.val, h2⟩).2.2.1, map_zero]
                · simp
              rw [ht1, ht2, add_zero]
            rcases hcop_i i with ⟨s₁, s₂, hs₁₂⟩
            rw [dif_pos j.isLt] at hs₁₂
            have hv1_eq : v₁ j = Polynomial.aeval D' (s₂ * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1)) (v i) := by
              dsimp only [v]; rw [dif_pos j.isLt, map_add]
              have h2z : Polynomial.aeval D' (s₂ * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1))
                  (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0) = 0 := by
                rw [map_mul, end_mul_apply]
                split_ifs with h2
                · rw [(hv₂ ⟨i.val, h2⟩).2.2.1, map_zero]
                · simp
              rw [h2z, add_zero]
              have h1eq : s₂ * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1) = 1 - s₁ * d₁ j :=
                eq_sub_of_add_eq' hs₁₂
              rw [h1eq, map_sub, map_one, map_mul, LinearMap.sub_apply, end_one_apply,
                end_mul_apply, (hv₁ j).2.2.1, map_zero, sub_zero]
            have hsub : cycSpan D' (v₁ j) (d₁ j).natDegree ≤ cycSpan D' (v i) (d i).natDegree := by
              rw [cycSpan, Submodule.span_le]
              rintro _ ⟨r, _, rfl⟩
              dsimp only
              rw [hv1_eq]
              have heq : (D' ^ r) (Polynomial.aeval D' (s₂ * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1)) (v i)) =
                  Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) ^ r * (s₂ * (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1))) (v i) := by
                conv_rhs => rw [map_mul, map_pow, Polynomial.aeval_X, end_mul_apply]
              rw [heq]
              exact cycSpan_inv_of_ann D' (v i) (d i) hdmon hdann _
            exact hsub.trans (le_iSup (fun i => cycSpan D' (v i) (d i).natDegree) i)
          · refine iSup_le (fun j => ?_)
            let i : Fin k := ⟨j.val, lt_of_lt_of_le j.isLt (le_max_right k₁ k₂)⟩
            have h2mon : (d₂ j).Monic := (hv₂ j).2.1
            have h1mon : (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1).Monic := by
              split_ifs with h1
              · exact (hv₁ ⟨i.val, h1⟩).2.1
              · exact Polynomial.monic_one
            have hdmon : (d i).Monic := by
              dsimp only [d]; rw [dif_pos j.isLt]; exact h1mon.mul h2mon
            have hdann : Polynomial.aeval D' (d i) (v i) = 0 := by
              dsimp only [d, v]
              have h2eq : (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1) = d₂ j := by
                rw [dif_pos j.isLt]
              have hv2eq : (if h2 : i.val < k₂ then v₂ ⟨i.val, h2⟩ else 0) = v₂ j := by
                rw [dif_pos j.isLt]
              rw [h2eq, hv2eq, map_add]
              have ht1 : Polynomial.aeval D' ((if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) * d₂ j)
                  (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) = 0 := by
                rw [mul_comm, map_mul, end_mul_apply]
                split_ifs with h1
                · rw [(hv₁ ⟨i.val, h1⟩).2.2.1, map_zero]
                · simp
              have ht2 : Polynomial.aeval D' ((if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) * d₂ j) (v₂ j) = 0 := by
                rw [map_mul, end_mul_apply, (hv₂ j).2.2.1, map_zero]
              rw [ht1, ht2, add_zero]
            rcases hcop_i i with ⟨s₁, s₂, hs₁₂⟩
            rw [dif_pos j.isLt] at hs₁₂
            have hv2_eq : v₂ j = Polynomial.aeval D' (s₁ * (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1)) (v i) := by
              dsimp only [v]; rw [dif_pos j.isLt, map_add]
              have h1z : Polynomial.aeval D' (s₁ * (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1))
                  (if h1 : i.val < k₁ then v₁ ⟨i.val, h1⟩ else 0) = 0 := by
                rw [map_mul, end_mul_apply]
                split_ifs with h1
                · rw [(hv₁ ⟨i.val, h1⟩).2.2.1, map_zero]
                · simp
              rw [h1z, zero_add]
              have h2eq : s₁ * (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1) = 1 - s₂ * d₂ j :=
                eq_sub_of_add_eq hs₁₂
              rw [h2eq, map_sub, map_one, map_mul, LinearMap.sub_apply, end_one_apply,
                end_mul_apply, (hv₂ j).2.2.1, map_zero, sub_zero]
            have hsub : cycSpan D' (v₂ j) (d₂ j).natDegree ≤ cycSpan D' (v i) (d i).natDegree := by
              rw [cycSpan, Submodule.span_le]
              rintro _ ⟨r, _, rfl⟩
              dsimp only
              rw [hv2_eq]
              have heq : (D' ^ r) (Polynomial.aeval D' (s₁ * (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1)) (v i)) =
                  Polynomial.aeval D' ((Polynomial.X : Polynomial (ZMod 2)) ^ r * (s₁ * (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1))) (v i) := by
                conv_rhs => rw [map_mul, map_pow, Polynomial.aeval_X, end_mul_apply]
              rw [heq]
              exact cycSpan_inv_of_ann D' (v i) (d i) hdmon hdann _
            exact hsub.trans (le_iSup (fun i => cycSpan D' (v i) (d i).natDegree) i)
      · have hdeg_i : ∀ i : Fin k, (d i).natDegree =
            (if h1 : i.val < k₁ then (d₁ ⟨i.val, h1⟩).natDegree else 0) +
            (if h2 : i.val < k₂ then (d₂ ⟨i.val, h2⟩).natDegree else 0) := by
          intro i
          have h1mon : (if h1 : i.val < k₁ then d₁ ⟨i.val, h1⟩ else 1).Monic := by
            split_ifs with h1
            · exact (hv₁ ⟨i.val, h1⟩).2.1
            · exact Polynomial.monic_one
          have h2mon : (if h2 : i.val < k₂ then d₂ ⟨i.val, h2⟩ else 1).Monic := by
            split_ifs with h2
            · exact (hv₂ ⟨i.val, h2⟩).2.1
            · exact Polynomial.monic_one
          dsimp only [d]
          rw [Polynomial.natDegree_mul h1mon.ne_zero h2mon.ne_zero]
          congr 1
          · split_ifs with h1 <;> simp
          · split_ifs with h2 <;> simp
        simp_rw [hdeg_i, Finset.sum_add_distrib]
        rw [sum_fin_dite_eq (le_max_left k₁ k₂) (fun j => (d₁ j).natDegree),
          sum_fin_dite_eq (le_max_right k₁ k₂) (fun j => (d₂ j).natDegree),
          hsum₁, hsum₂, hdim_sum]

private abbrev PackItem (n : ℕ) := Dual n × ℕ × Submodule (ZMod 2) (Dual n)

private abbrev ValidItem {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n)
    (W Cov : Submodule (ZMod 2) (Dual n)) (it : PackItem n) : Prop :=
  it.2.2 ≤ W ∧ it.2.2.map D' ≤ it.2.2 ∧ it.1 ∈ it.2.2 ∧ it.2.2 ≤ Cov ⊔ cycSpan D' it.1 it.2.1

private lemma pow_mem_of_valid {n : ℕ} (D' : Dual n →ₗ[ZMod 2] Dual n)
    {W Cov : Submodule (ZMod 2) (Dual n)} {it : PackItem n}
    (hv : ValidItem D' W Cov it) (r : ℕ) :
    (D' ^ r) it.1 ∈ it.2.2 := by
  induction r with
  | zero => simpa using hv.2.2.1
  | succ r ih =>
    rw [pow_succ', end_mul_apply]
    exact hv.2.1 ⟨_, ih, rfl⟩

private def listSup {n : ℕ} : List (PackItem n) → Submodule (ZMod 2) (Dual n)
  | [] => ⊥
  | it :: rest => it.2.2 ⊔ listSup rest

private def listLenSum {n : ℕ} : List (PackItem n) → ℕ
  | [] => 0
  | it :: rest => it.2.1 + listLenSum rest

private lemma list_extract_pred {α : Type*} (P : α → Prop) [DecidablePred P] :
    ∀ (l : List α), (∃ x ∈ l, P x) →
      ∃ (x : α) (rest : List α), P x ∧ rest.length + 1 = l.length ∧
        (∀ y, y ∈ l ↔ y = x ∨ y ∈ rest) ∧
        (∀ f : α → ℕ, (l.map f).sum = f x + (rest.map f).sum) := by
  intro l
  induction l with
  | nil => rintro ⟨x, hx, _⟩; exact False.elim (List.not_mem_nil hx)
  | cons a t ih =>
    intro hex
    by_cases ha : P a
    · exact ⟨a, t, ha, rfl, fun y => List.mem_cons, fun f => rfl⟩
    · have hex' : ∃ x ∈ t, P x := by
        rcases hex with ⟨x, hx, hPx⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact False.elim (ha hPx)
        · exact ⟨x, hxt, hPx⟩
      rcases ih hex' with ⟨x, rest, hPx, hlen, hmem, hsum⟩
      refine ⟨x, a :: rest, hPx, by simp [hlen], ?_, ?_⟩
      · intro y
        rw [List.mem_cons, List.mem_cons, hmem y]
        tauto
      · intro f
        simp only [List.map_cons, List.sum_cons, hsum f]
        omega

private lemma listLenSum_eq_map_sum {n : ℕ} (l : List (PackItem n)) :
    listLenSum l = (l.map (fun it => it.2.1)).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [listLenSum, ih]

private lemma listSup_eq_of_mem_iff {n : ℕ} {l₁ l₂ : List (PackItem n)}
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : listSup l₁ = listSup l₂ := by
  have hle : ∀ a b : List (PackItem n), (∀ x ∈ a, x ∈ b) → listSup a ≤ listSup b := by
    intro a b hab
    induction a with
    | nil => exact bot_le
    | cons x t ih =>
      refine sup_le ?_ (ih (fun y hy => hab y (List.mem_cons_of_mem x hy)))
      have hxb : x ∈ b := hab x List.mem_cons_self
      clear ih hab t
      induction b with
      | nil => exact False.elim (List.not_mem_nil hxb)
      | cons z u ihb =>
        rcases List.mem_cons.mp hxb with rfl | hxu
        · exact le_sup_left
        · exact (ihb hxu).trans le_sup_right
  exact le_antisymm (hle l₁ l₂ (fun x hx => (h x).mp hx)) (hle l₂ l₁ (fun x hx => (h x).mpr hx))

private lemma balance_chains_pack {n s : ℕ} (hs : 0 < s) (D' : Dual n →ₗ[ZMod 2] Dual n)
    (W : Submodule (ZMod 2) (Dual n)) :
    ∀ (len : ℕ) (active : List (PackItem n)) (Cov : Submodule (ZMod 2) (Dual n)),
      active.length ≤ len →
      (∀ it ∈ active, ValidItem D' W Cov it) →
      listLenSum active ≤ s * active.length →
      ∃ G : Submodule (ZMod 2) (Dual n),
        G ≤ W ∧ Module.finrank (ZMod 2) G ≤ active.length ∧
        listSup active ≤ Cov ⊔ ⨆ r ∈ Finset.range s, G.map (D' ^ r) := by
  intro len
  induction len with
  | zero =>
    intro active Cov hlen _ _
    have hnil : active = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨⊥, bot_le, by simp, by simp [listSup]⟩
  | succ len ih =>
    intro active Cov hlen hvalid hsum
    classical
    by_cases hall : ∀ it ∈ active, it.2.1 ≤ s
    · let G : Submodule (ZMod 2) (Dual n) := Submodule.span (ZMod 2) (active.map Prod.fst).toFinset
      have hGW : G ≤ W := by
        rw [Submodule.span_le]
        intro x hx
        simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hx
        rcases hx with ⟨it, hit, rfl⟩
        exact (hvalid it hit).1 (hvalid it hit).2.2.1
      have hGdim : Module.finrank (ZMod 2) G ≤ active.length := by
        have h1 := finrank_span_le_card (R := ZMod 2) ((active.map Prod.fst).toFinset : Set (Dual n))
        refine h1.trans ?_
        rw [Finset.toFinset_coe]
        exact (List.toFinset_card_le _).trans (by simp)
      refine ⟨G, hGW, hGdim, ?_⟩
      have hle_item : ∀ it ∈ active, it.2.2 ≤ Cov ⊔ ⨆ r ∈ Finset.range s, G.map (D' ^ r) := by
        intro it hit
        refine (hvalid it hit).2.2.2.trans (sup_le le_sup_left ?_)
        refine (cycSpan_mono D' it.1 (hall it hit)).trans ?_
        rw [cycSpan, Submodule.span_le]
        rintro _ ⟨r, hr, rfl⟩
        have hvG : it.1 ∈ G := Submodule.subset_span (by
          simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map]
          exact ⟨it, hit, rfl⟩)
        exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr ⟨it.1, hvG, rfl⟩))
      have hsup_le : ∀ (l : List (PackItem n)) (Tsub : Submodule (ZMod 2) (Dual n)),
          (∀ it ∈ l, it.2.2 ≤ Tsub) → listSup l ≤ Tsub := by
        intro l Tsub hl
        induction l with
        | nil => exact bot_le
        | cons it rest ihr =>
          exact sup_le (hl it List.mem_cons_self) (ihr (fun x hx => hl x (List.mem_cons_of_mem it hx)))
      exact hsup_le active _ hle_item
    · push_neg at hall
      rcases list_extract_pred (fun it : PackItem n => s < it.2.1) active hall with
        ⟨it₀, rest0, hlt₀, hlen0, hmem0, hsum0⟩
      have hit₀_valid : ValidItem D' W Cov it₀ := hvalid it₀ ((hmem0 it₀).mpr (Or.inl rfl))
      have hrest0_valid : ∀ it ∈ rest0, ValidItem D' W Cov it :=
        fun it hit => hvalid it ((hmem0 it).mpr (Or.inr hit))
      have hsup0 : listSup active = it₀.2.2 ⊔ listSup rest0 :=
        listSup_eq_of_mem_iff (fun y => (hmem0 y).trans List.mem_cons.symm)
      have hsum_rest0 : listLenSum rest0 + (it₀.2.1 - s) ≤ s * rest0.length := by
        have h1 := hsum0 (fun it => it.2.1)
        rw [← listLenSum_eq_map_sum, ← listLenSum_eq_map_sum] at h1
        have hmul : s * active.length = s * rest0.length + s := by
          rw [← hlen0, mul_add, mul_one]
        omega
      let G0 : Submodule (ZMod 2) (Dual n) := Submodule.span (ZMod 2) {it₀.1}
      have hG0W : G0 ≤ W := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hit₀_valid.1 hit₀_valid.2.2.1))
      have hG0dim : Module.finrank (ZMod 2) G0 ≤ 1 := by
        have h := finrank_span_le_card (R := ZMod 2) ({it₀.1} : Set (Dual n))
        simpa using h
      let Cov0 : Submodule (ZMod 2) (Dual n) := Cov ⊔ ⨆ r ∈ Finset.range s, G0.map (D' ^ r)
      have hcyc0 : cycSpan D' it₀.1 s ≤ Cov0 := by
        rw [cycSpan, Submodule.span_le]
        rintro _ ⟨r, hr, rfl⟩
        exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem r
          (Submodule.mem_iSup_of_mem hr ⟨it₀.1, Submodule.subset_span rfl, rfl⟩))
      have hinner : ∀ (remLen : ℕ) (rem : List (PackItem n)) (a : ℕ) (CovCur : Submodule (ZMod 2) (Dual n)),
          rem.length ≤ remLen → remLen ≤ len →
          s ≤ a → a ≤ it₀.2.1 →
          Cov ≤ CovCur → cycSpan D' it₀.1 a ≤ CovCur →
          (∀ it ∈ rem, ValidItem D' W CovCur it) →
          listLenSum rem + (it₀.2.1 - a) ≤ s * rem.length →
          ∃ G1 : Submodule (ZMod 2) (Dual n),
            G1 ≤ W ∧ Module.finrank (ZMod 2) G1 ≤ rem.length ∧
            it₀.2.2 ⊔ listSup rem ≤ CovCur ⊔ ⨆ r ∈ Finset.range s, G1.map (D' ^ r) := by
        intro remLen
        induction remLen with
        | zero =>
          intro rem a CovCur hrl _ hsa ha hCC hca _ hsr
          have hnil : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil
          have haeq : a = it₀.2.1 := by simp [listLenSum] at hsr; omega
          subst haeq
          refine ⟨⊥, bot_le, by simp, ?_⟩
          simp only [listSup, sup_bot_eq]
          exact hit₀_valid.2.2.2.trans (sup_le (hCC.trans le_sup_left) (hca.trans le_sup_left))
        | succ remLen ih_in =>
          intro rem a CovCur hrl hrlen hsa ha hCC hca hrv hsr
          by_cases ha_eq : a = it₀.2.1
          · subst ha_eq
            rcases ih rem CovCur (by omega) hrv (by omega) with ⟨G1, hG1W, hG1d, hG1cov⟩
            refine ⟨G1, hG1W, hG1d, sup_le ?_ hG1cov⟩
            exact hit₀_valid.2.2.2.trans (sup_le (hCC.trans le_sup_left) (hca.trans le_sup_left))
          · have hshort_ex : ∃ it ∈ rem, it.2.1 < s := by
              by_contra hno
              push_neg at hno
              have hge : s * rem.length ≤ listLenSum rem := by
                clear hrl hrlen hCC hca hrv hsr ih_in
                induction rem with
                | nil => simp [listLenSum]
                | cons x t ihr =>
                  simp only [listLenSum, List.length_cons]
                  have hx := hno x List.mem_cons_self
                  have ht := ihr (fun y hy => hno y (List.mem_cons_of_mem x hy))
                  linarith
              omega
            rcases list_extract_pred (fun it : PackItem n => it.2.1 < s) rem hshort_ex with
              ⟨itj, rem', hltj, hlen', hmem', hsum'⟩
            have hitj_valid : ValidItem D' W CovCur itj := hrv itj ((hmem' itj).mpr (Or.inl rfl))
            have hrem'_valid : ∀ it ∈ rem', ValidItem D' W CovCur it :=
              fun it hit => hrv it ((hmem' it).mpr (Or.inr hit))
            have hsup' : listSup rem = itj.2.2 ⊔ listSup rem' :=
              listSup_eq_of_mem_iff (fun y => (hmem' y).trans List.mem_cons.symm)
            let g : Dual n := itj.1 + (D' ^ (a - itj.2.1)) it₀.1
            have hgW : g ∈ W := W.add_mem (hitj_valid.1 hitj_valid.2.2.1)
              (hit₀_valid.1 (pow_mem_of_valid D' hit₀_valid (a - itj.2.1)))
            by_cases hfill : s - itj.2.1 ≤ it₀.2.1 - a
            · let Gg : Submodule (ZMod 2) (Dual n) := Submodule.span (ZMod 2) {g}
              have hGgW : Gg ≤ W := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hgW)
              have hGgdim : Module.finrank (ZMod 2) Gg ≤ 1 := by
                have h := finrank_span_le_card (R := ZMod 2) ({g} : Set (Dual n))
                simpa using h
              let CovNext : Submodule (ZMod 2) (Dual n) := CovCur ⊔ ⨆ r ∈ Finset.range s, Gg.map (D' ^ r)
              have hCnext_le : CovCur ≤ CovNext := le_sup_left
              have hgj_mem : ∀ r < s, (D' ^ r) g ∈ CovNext := fun r hr =>
                Submodule.mem_sup_right (Submodule.mem_iSup_of_mem r
                  (Submodule.mem_iSup_of_mem (Finset.mem_range.mpr hr) ⟨g, Submodule.subset_span rfl, rfl⟩))
              have hcyc_j : cycSpan D' itj.1 itj.2.1 ≤ CovNext := by
                rw [cycSpan, Submodule.span_le]
                rintro _ ⟨r, hr, rfl⟩
                have hrlt : r < itj.2.1 := Finset.mem_range.mp hr
                have h1 : (D' ^ r) g ∈ CovNext := hgj_mem r (lt_trans hrlt hltj)
                have h2 : (D' ^ (a - itj.2.1 + r)) it₀.1 ∈ CovNext :=
                  hCnext_le (hca (pow_mem_cycSpan D' it₀.1 a _ (by omega)))
                have hrew : (D' ^ r) itj.1 = (D' ^ r) g - (D' ^ (a - itj.2.1 + r)) it₀.1 := by
                  simp only [g, map_add, ← end_mul_apply, ← pow_add]
                  have he : r + (a - itj.2.1) = a - itj.2.1 + r := by omega
                  rw [he]; abel
                dsimp only
                rw [hrew]
                exact CovNext.sub_mem h1 h2
              have hSj_le : itj.2.2 ≤ CovNext :=
                hitj_valid.2.2.2.trans (sup_le hCnext_le hcyc_j)
              have hca' : cycSpan D' it₀.1 (a + (s - itj.2.1)) ≤ CovNext := by
                rw [cycSpan, Submodule.span_le]
                rintro _ ⟨k, hk, rfl⟩
                have hklt : k < a + (s - itj.2.1) := Finset.mem_range.mp hk
                by_cases hka : k < a
                · exact hCnext_le (hca (pow_mem_cycSpan D' it₀.1 a k hka))
                · let r := itj.2.1 + (k - a)
                  have hrlt : r < s := by omega
                  have h1 : (D' ^ r) g ∈ CovNext := hgj_mem r hrlt
                  have h2 : (D' ^ r) itj.1 ∈ CovNext := hSj_le (pow_mem_of_valid D' hitj_valid r)
                  have hrew : (D' ^ k) it₀.1 = (D' ^ r) g - (D' ^ r) itj.1 := by
                    simp only [g, map_add, ← end_mul_apply, ← pow_add]
                    have he : r + (a - itj.2.1) = k := by omega
                    rw [he]; abel
                  dsimp only
                  rw [hrew]
                  exact CovNext.sub_mem h1 h2
              have hsr' : listLenSum rem' + (it₀.2.1 - (a + (s - itj.2.1))) ≤ s * rem'.length := by
                have h1 := hsum' (fun it => it.2.1)
                rw [← listLenSum_eq_map_sum, ← listLenSum_eq_map_sum] at h1
                have hmul : s * rem.length = s * rem'.length + s := by
                  rw [← hlen', mul_add, mul_one]
                omega
              rcases ih_in rem' (a + (s - itj.2.1)) CovNext (by omega) (by omega) (by omega) (by omega)
                (hCC.trans hCnext_le) hca'
                (fun it hit => ⟨(hrem'_valid it hit).1, (hrem'_valid it hit).2.1,
                  (hrem'_valid it hit).2.2.1, (hrem'_valid it hit).2.2.2.trans (sup_le_sup_right hCnext_le _)⟩)
                hsr' with ⟨G2, hG2W, hG2d, hG2cov⟩
              refine ⟨Gg ⊔ G2, sup_le hGgW hG2W, ?_, ?_⟩
              · have h := Submodule.finrank_sup_add_finrank_inf_eq Gg G2
                omega
              · rw [hsup']
                have hCovEq : CovNext ⊔ (⨆ r ∈ Finset.range s, G2.map (D' ^ r)) =
                    CovCur ⊔ ⨆ r ∈ Finset.range s, (Gg ⊔ G2).map (D' ^ r) := by
                  apply le_antisymm
                  · refine sup_le (sup_le le_sup_left ?_) ?_
                    · refine iSup₂_le (fun r hr => (Submodule.map_mono le_sup_left).trans
                        ((le_biSup (fun r => (Gg ⊔ G2).map (D' ^ r)) hr).trans le_sup_right))
                    · refine iSup₂_le (fun r hr => (Submodule.map_mono le_sup_right).trans
                        ((le_biSup (fun r => (Gg ⊔ G2).map (D' ^ r)) hr).trans le_sup_right))
                  · refine sup_le (le_sup_left.trans le_sup_left) (iSup₂_le (fun r hr => ?_))
                    rw [Submodule.map_sup]
                    exact sup_le
                      ((le_biSup (fun r => Gg.map (D' ^ r)) hr).trans (le_sup_right.trans le_sup_left))
                      ((le_biSup (fun r => G2.map (D' ^ r)) hr).trans le_sup_right)
                rw [← hCovEq]
                refine sup_le (le_sup_left.trans hG2cov) (sup_le (hSj_le.trans le_sup_left) (le_sup_right.trans hG2cov))
            · let t := it₀.2.1 - a
              let itj' : PackItem n := (g, itj.2.1 + t, it₀.2.2 ⊔ itj.2.2)
              have hitj'_valid : ValidItem D' W CovCur itj' := by
                refine ⟨sup_le hit₀_valid.1 hitj_valid.1, ?_, ?_, ?_⟩
                · rw [Submodule.map_sup]
                  exact sup_le (hit₀_valid.2.1.trans le_sup_left) (hitj_valid.2.1.trans le_sup_right)
                · exact Submodule.add_mem _ (Submodule.mem_sup_right hitj_valid.2.2.1)
                    (Submodule.mem_sup_left (pow_mem_of_valid D' hit₀_valid (a - itj.2.1)))
                · have hcyc_j : cycSpan D' itj.1 itj.2.1 ≤ CovCur ⊔ cycSpan D' g (itj.2.1 + t) := by
                    rw [cycSpan, Submodule.span_le]
                    rintro _ ⟨r, hr, rfl⟩
                    have hrlt : r < itj.2.1 := Finset.mem_range.mp hr
                    have h1 : (D' ^ r) g ∈ CovCur ⊔ cycSpan D' g (itj.2.1 + t) :=
                      Submodule.mem_sup_right (pow_mem_cycSpan D' g _ r (by omega))
                    have h2 : (D' ^ (a - itj.2.1 + r)) it₀.1 ∈ CovCur ⊔ cycSpan D' g (itj.2.1 + t) :=
                      Submodule.mem_sup_left (hca (pow_mem_cycSpan D' it₀.1 a _ (by omega)))
                    have hrew : (D' ^ r) itj.1 = (D' ^ r) g - (D' ^ (a - itj.2.1 + r)) it₀.1 := by
                      simp only [g, map_add, ← end_mul_apply, ← pow_add]
                      have he : r + (a - itj.2.1) = a - itj.2.1 + r := by omega
                      rw [he]; abel
                    dsimp only
                    rw [hrew]
                    exact Submodule.sub_mem _ h1 h2
                  have hSj_le : itj.2.2 ≤ CovCur ⊔ cycSpan D' g (itj.2.1 + t) :=
                    hitj_valid.2.2.2.trans (sup_le le_sup_left hcyc_j)
                  have hcyc_0 : cycSpan D' it₀.1 it₀.2.1 ≤ CovCur ⊔ cycSpan D' g (itj.2.1 + t) := by
                    rw [cycSpan, Submodule.span_le]
                    rintro _ ⟨k, hk, rfl⟩
                    have hklt : k < it₀.2.1 := Finset.mem_range.mp hk
                    by_cases hka : k < a
                    · exact Submodule.mem_sup_left (hca (pow_mem_cycSpan D' it₀.1 a k hka))
                    · let r := itj.2.1 + (k - a)
                      have h1 : (D' ^ r) g ∈ CovCur ⊔ cycSpan D' g (itj.2.1 + t) :=
                        Submodule.mem_sup_right (pow_mem_cycSpan D' g _ r (by omega))
                      have h2 : (D' ^ r) itj.1 ∈ CovCur ⊔ cycSpan D' g (itj.2.1 + t) :=
                        hSj_le (pow_mem_of_valid D' hitj_valid r)
                      have hrew : (D' ^ k) it₀.1 = (D' ^ r) g - (D' ^ r) itj.1 := by
                        simp only [g, map_add, ← end_mul_apply, ← pow_add]
                        have he : r + (a - itj.2.1) = k := by omega
                        rw [he]; abel
                      dsimp only
                      rw [hrew]
                      exact Submodule.sub_mem _ h1 h2
                  have hS0_le : it₀.2.2 ≤ CovCur ⊔ cycSpan D' g (itj.2.1 + t) :=
                    hit₀_valid.2.2.2.trans (sup_le (hCC.trans le_sup_left) hcyc_0)
                  exact sup_le hS0_le hSj_le
              have hnew_len : (itj' :: rem').length = rem.length := by simp [hlen']
              have hnew_sum : listLenSum (itj' :: rem') ≤ s * (itj' :: rem').length := by
                have h1 := hsum' (fun it => it.2.1)
                rw [← listLenSum_eq_map_sum, ← listLenSum_eq_map_sum] at h1
                simp only [listLenSum, itj', hnew_len]
                omega
              rcases ih (itj' :: rem') CovCur (by omega)
                (fun it hit => by
                  rcases List.mem_cons.mp hit with rfl | hrem
                  · exact hitj'_valid
                  · exact hrem'_valid it hrem)
                hnew_sum with ⟨G1, hG1W, hG1d, hG1cov⟩
              refine ⟨G1, hG1W, by omega, ?_⟩
              rw [hsup']
              have hls : listSup (itj' :: rem') = (it₀.2.2 ⊔ itj.2.2) ⊔ listSup rem' := rfl
              rw [hls] at hG1cov
              have heq : it₀.2.2 ⊔ (itj.2.2 ⊔ listSup rem') = (it₀.2.2 ⊔ itj.2.2) ⊔ listSup rem' := by
                exact (sup_assoc _ _ _).symm
              rw [heq]
              exact hG1cov
      rcases hinner rest0.length rest0 s Cov0 le_rfl (by omega) le_rfl (le_of_lt hlt₀)
        le_sup_left hcyc0
        (fun it hit => ⟨(hrest0_valid it hit).1, (hrest0_valid it hit).2.1,
          (hrest0_valid it hit).2.2.1, (hrest0_valid it hit).2.2.2.trans (sup_le_sup_right le_sup_left _)⟩)
        hsum_rest0 with ⟨G1, hG1W, hG1d, hG1cov⟩
      refine ⟨G0 ⊔ G1, sup_le hG0W hG1W, ?_, ?_⟩
      · have h := Submodule.finrank_sup_add_finrank_inf_eq G0 G1
        omega
      · rw [hsup0]
        have hCovEq : Cov0 ⊔ (⨆ r ∈ Finset.range s, G1.map (D' ^ r)) =
            Cov ⊔ ⨆ r ∈ Finset.range s, (G0 ⊔ G1).map (D' ^ r) := by
          apply le_antisymm
          · refine sup_le (sup_le le_sup_left ?_) ?_
            · refine iSup₂_le (fun r hr => (Submodule.map_mono le_sup_left).trans
                ((le_biSup (fun r => (G0 ⊔ G1).map (D' ^ r)) hr).trans le_sup_right))
            · refine iSup₂_le (fun r hr => (Submodule.map_mono le_sup_right).trans
                ((le_biSup (fun r => (G0 ⊔ G1).map (D' ^ r)) hr).trans le_sup_right))
          · refine sup_le (le_sup_left.trans le_sup_left) (iSup₂_le (fun r hr => ?_))
            rw [Submodule.map_sup]
            exact sup_le
              ((le_biSup (fun r => G0.map (D' ^ r)) hr).trans (le_sup_right.trans le_sup_left))
              ((le_biSup (fun r => G1.map (D' ^ r)) hr).trans le_sup_right)
        rwa [← hCovEq]

private lemma exists_flag_of_gen {n s : ℕ} (hs : 0 < s) (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (G : Submodule (ZMod 2) (Dual n)) (hGW : G ≤ LinearMap.range ((Ddual T) ^ s))
    (hspan : LinearMap.range ((Ddual T) ^ s) ≤ ⨆ r ∈ Finset.range s, G.map ((Ddual T) ^ r)) :
    ∃ flag : ℕ → Submodule (ZMod 2) (Dual n),
      flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j + 1)) ∧
      (Finset.range s).sum (fun j => stepCost T (flag j) (flag (j + 1))) ≤
        Module.finrank (ZMod 2) G := by
  let D' := Ddual T
  haveI : Module.Free (ZMod 2) G := Module.Free.of_divisionRing (ZMod 2) G
  let bG := Module.finBasis (ZMod 2) G
  let r := Module.finrank (ZMod 2) G
  have hpre : ∀ i : Fin r, ∃ u : Dual n, (D' ^ s) u = (bG i).1 := fun i => hGW (bG i).2
  let lifts : Fin r → Dual n := fun i => Classical.choose (hpre i)
  have hlifts : ∀ i : Fin r, (D' ^ s) (lifts i) = (bG i).1 := fun i => Classical.choose_spec (hpre i)
  let L : Submodule (ZMod 2) (Dual n) := Submodule.span (ZMod 2) (Set.range lifts)
  have hLG : L.map (D' ^ s) = G := by
    apply le_antisymm
    · rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hlifts i]; exact (bG i).2
    · intro x hx
      have hrep := bG.sum_repr ⟨x, hx⟩
      have hxval : x = ∑ i : Fin r, (bG.repr ⟨x, hx⟩ i) • (bG i).1 := by
        have := congrArg Subtype.val hrep
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
      refine ⟨∑ i : Fin r, (bG.repr ⟨x, hx⟩ i) • lifts i,
        Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)), ?_⟩
      rw [map_sum]
      conv_rhs => rw [hxval]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, hlifts i]
  let flag : ℕ → Submodule (ZMod 2) (Dual n) := fun j =>
    if j = 0 then ⊥
    else LinearMap.ker (D' ^ j) ⊔ ⨆ t ∈ Finset.Ico (s - j) s, L.map (D' ^ t)
  have hflag0 : flag 0 = ⊥ := by simp [flag]
  have hflag_pos : ∀ j, 0 < j → flag j = LinearMap.ker (D' ^ j) ⊔ ⨆ t ∈ Finset.Ico (s - j) s, L.map (D' ^ t) := by
    intro j hj; simp [flag, Nat.ne_of_gt hj]
  have hflags : flag s = ⊤ := by
    rw [hflag_pos s hs, Nat.sub_self, eq_top_iff]
    intro u _
    have huW : (D' ^ s) u ∈ ⨆ t ∈ Finset.range s, G.map (D' ^ t) := hspan ⟨u, rfl⟩
    have hmap_eq : (⨆ t ∈ Finset.Ico 0 s, L.map (D' ^ t)).map (D' ^ s) =
        ⨆ t ∈ Finset.range s, G.map (D' ^ t) := by
      simp_rw [Submodule.map_iSup]
      apply le_antisymm
      · refine iSup₂_le (fun t ht => ?_)
        have htlt : t < s := (Finset.mem_Ico.mp ht).2
        rw [map_map_end, ← pow_add, add_comm, pow_add, ← map_map_end, hLG]
        exact le_biSup (fun t => G.map (D' ^ t)) (Finset.mem_range.mpr htlt)
      · refine iSup₂_le (fun t ht => ?_)
        have htlt : t < s := Finset.mem_range.mp ht
        have hmem : t ∈ Finset.Ico 0 s := Finset.mem_Ico.mpr ⟨Nat.zero_le _, htlt⟩
        have hrew : G.map (D' ^ t) = (L.map (D' ^ t)).map (D' ^ s) := by
          rw [map_map_end, ← pow_add, add_comm, pow_add, ← map_map_end, hLG]
        rw [hrew]
        exact le_biSup (fun t => (L.map (D' ^ t)).map (D' ^ s)) hmem
    rw [← hmap_eq] at huW
    rcases huW with ⟨v, hv, hvu⟩
    have hker : u - v ∈ LinearMap.ker (D' ^ s) := by
      rw [LinearMap.mem_ker, map_sub, hvu, sub_self]
    have heq : u = (u - v) + v := by abel
    rw [heq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hker) (Submodule.mem_sup_right hv)
  have hmono : ∀ j < s, flag j ≤ flag (j + 1) := by
    intro j _
    by_cases hj0 : j = 0
    · subst hj0; rw [hflag0]; exact bot_le
    · rw [hflag_pos j (Nat.pos_of_ne_zero hj0), hflag_pos (j + 1) (Nat.succ_pos j)]
      refine sup_le ?_ ?_
      · refine le_sup_of_le_left ?_
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [pow_succ', end_mul_apply, hx, map_zero]
      · refine le_sup_of_le_right (iSup₂_le (fun t ht => ?_))
        have ht' := Finset.mem_Ico.mp ht
        exact le_biSup (fun t => L.map (D' ^ t)) (Finset.mem_Ico.mpr ⟨by omega, ht'.2⟩)
  have hcost0 : stepCost T (flag 0) (flag 1) ≤ Module.finrank (ZMod 2) G := by
    unfold stepCost
    dsimp only
    rw [hflag0, Submodule.map_bot, bot_sup_eq, bot_sup_eq, finrank_bot, Nat.sub_zero]
    rw [hflag_pos 1 (Nat.succ_pos 0), Submodule.map_sup]
    have hker0 : (LinearMap.ker (D' ^ 1)).map D' = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (D' ^ 1) x = 0 := hx
      rw [pow_one] at hx'
      exact (Submodule.mem_bot (ZMod 2)).mpr hx'
    rw [hker0, bot_sup_eq]
    have hsubG : (⨆ t ∈ Finset.Ico (s - 1) s, L.map (D' ^ t)).map D' ≤ G := by
      simp_rw [Submodule.map_iSup]
      refine iSup₂_le (fun t ht => ?_)
      have ht' := Finset.mem_Ico.mp ht
      have hteq : t = s - 1 := by omega
      subst hteq
      rw [map_map_end, ← pow_succ', show s - 1 + 1 = s by omega, hLG]
    exact Submodule.finrank_mono hsubG
  have hcost_pos : ∀ j, 0 < j → j < s → stepCost T (flag j) (flag (j + 1)) = 0 := by
    intro j hjpos hjs
    unfold stepCost
    dsimp only
    have hle : (flag (j + 1)).map D' ≤ flag j ⊔ (flag j).map D' := by
      rw [hflag_pos (j + 1) (Nat.succ_pos j), hflag_pos j hjpos, Submodule.map_sup]
      refine sup_le ?_ ?_
      · refine le_sup_of_le_left (le_sup_of_le_left ?_)
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (D' ^ (j + 1)) x = 0 := hx
        change (D' ^ j) (D' x) = 0
        rw [← end_mul_apply, ← pow_succ]
        exact hx'
      · simp_rw [Submodule.map_iSup]
        refine iSup₂_le (fun t ht => ?_)
        have ht' := Finset.mem_Ico.mp ht
        rw [map_map_end, ← pow_succ']
        by_cases hlast : t + 1 < s
        · refine le_sup_of_le_left (le_sup_of_le_right ?_)
          exact le_biSup (fun t => L.map (D' ^ t)) (Finset.mem_Ico.mpr ⟨by omega, hlast⟩)
        · have hteq : t = s - 1 := by omega
          subst hteq
          have hmem : s - 1 ∈ Finset.Ico (s - j) s := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          have hsub : L.map (D' ^ (s - 1)) ≤ LinearMap.ker (D' ^ j) ⊔ ⨆ t ∈ Finset.Ico (s - j) s, L.map (D' ^ t) :=
            le_sup_of_le_right (le_biSup (fun t => L.map (D' ^ t)) hmem)
          refine (?_ : L.map (D' ^ (s - 1 + 1)) ≤ (L.map (D' ^ (s - 1))).map D').trans
            ((Submodule.map_mono hsub).trans le_sup_right)
          rw [map_map_end, ← pow_succ']
    rw [sup_eq_left.mpr hle, Nat.sub_self]
  refine ⟨flag, hflag0, hflags, hmono, ?_⟩
  have hsum_eq : (Finset.range s).sum (fun j => stepCost T (flag j) (flag (j + 1))) =
      stepCost T (flag 0) (flag 1) := by
    rw [Finset.sum_eq_single 0]
    · intro j hj hne
      exact hcost_pos j (Nat.pos_of_ne_zero hne) (Finset.mem_range.mp hj)
    · intro h; exact False.elim (h (Finset.mem_range.mpr hs))
  rw [hsum_eq]
  exact hcost0

end PEqualNP.Outside.L_pcx_381

theorem PEqualNP.Outside.L_pcx_381 :
    ∀ (n s : ℕ) (_ : 0 < s),
      let V := Fin n → ZMod 2
      let U := V →ₗ[ZMod 2] ZMod 2
      let transcript := fun (w : ℕ)
          (ask : List (Fin w → ZMod 2) → Fin w → U × ZMod 2 × ZMod 2)
          (layer : ZMod 2) (word : V) =>
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) []
      ∀ (T : V ≃ₗ[ZMod 2] V) (b : V),
        let feasible := fun K : ℕ =>
          ∃ (w : ℕ) (ask : List (Fin w → ZMod 2) → Fin w → U × ZMod 2 × ZMod 2),
            (∀ layer : ZMod 2, Function.Injective (transcript w ask layer)) ∧
            K ≤ (Finset.univ.filter (fun x : V =>
              transcript w ask 0 x = transcript w ask 1 (T x + b))).card
        let D : V →ₗ[ZMod 2] V := T.toLinearMap + LinearMap.id
        let W := LinearMap.range (D ^ s)
        let g := sSup {j : ℕ | ∃ p : Polynomial (ZMod 2), Irreducible p ∧
          j = Module.finrank (ZMod 2) (W ⊓ LinearMap.ker (Polynomial.aeval D p) : Submodule (ZMod 2) V) / p.natDegree}
        let h := max g ((Module.finrank (ZMod 2) W + s - 1) / s)
        ∀ K : ℕ, feasible K ↔ K * 2 ^ h ≤ 2 ^ n := by
  intro n s hs
  dsimp only
  intro T b K
  rw [PEqualNP.Outside.L_pcx_381.feasible_iff_flag n s T b K]
  let D := PEqualNP.Outside.L_pcx_381.Dprimal T
  let D' := PEqualNP.Outside.L_pcx_381.Ddual T
  let W := LinearMap.range (D ^ s)
  let W' := LinearMap.range (D' ^ s)
  let Sset : Set ℕ := {j : ℕ | ∃ p : Polynomial (ZMod 2), Irreducible p ∧
    j = Module.finrank (ZMod 2) (W ⊓ LinearMap.ker (Polynomial.aeval D p) : Submodule (ZMod 2) (Fin n → ZMod 2)) / p.natDegree}
  let g := sSup Sset
  let h := max g ((Module.finrank (ZMod 2) W + s - 1) / s)
  have hS_ne : Sset.Nonempty := ⟨_, Polynomial.X, Polynomial.irreducible_X, rfl⟩
  have hS_bdd : BddAbove Sset := by
    refine ⟨n, ?_⟩
    rintro j ⟨p, _, rfl⟩
    have h1 : Module.finrank (ZMod 2) (W ⊓ LinearMap.ker (Polynomial.aeval D p) : Submodule (ZMod 2) (Fin n → ZMod 2)) ≤ n := by
      have := Submodule.finrank_le (W ⊓ LinearMap.ker (Polynomial.aeval D p) : Submodule (ZMod 2) (Fin n → ZMod 2))
      simpa using this
    exact (Nat.div_le_self _ _).trans h1
  have hW_dim_eq : Module.finrank (ZMod 2) W' = Module.finrank (ZMod 2) W :=
    PEqualNP.Outside.L_pcx_381.finrank_W_dual_eq T s
  change (∃ flag : ℕ → Submodule (ZMod 2) (PEqualNP.Outside.L_pcx_381.Dual n),
    flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j + 1)) ∧
    K * 2 ^ ((Finset.range s).sum (fun j => PEqualNP.Outside.L_pcx_381.stepCost T (flag j) (flag (j + 1)))) ≤ 2 ^ n) ↔
    K * 2 ^ h ≤ 2 ^ n
  constructor
  · rintro ⟨flag, hflag0, hflags, _, hKbound⟩
    by_cases hK0 : K = 0
    · subst hK0; simp
    · set C := (Finset.range s).sum (fun j => PEqualNP.Outside.L_pcx_381.stepCost T (flag j) (flag (j + 1)))
      rcases PEqualNP.Outside.L_pcx_381.exists_generating_subspace_of_flag T flag hflag0 hflags
        with ⟨E, hEdim, hEspan⟩
      have hdim_bound : (Module.finrank (ZMod 2) W + s - 1) / s ≤ C := by
        have h1 : Module.finrank (ZMod 2) W' ≤ ∑ r ∈ Finset.range s, Module.finrank (ZMod 2) (E.map (D' ^ r)) :=
          (Submodule.finrank_mono hEspan).trans (PEqualNP.Outside.L_pcx_381.finrank_iSup_range_le s _)
        have h2 : ∑ r ∈ Finset.range s, Module.finrank (ZMod 2) (E.map (D' ^ r)) ≤ s * Module.finrank (ZMod 2) E := by
          calc ∑ r ∈ Finset.range s, Module.finrank (ZMod 2) (E.map (D' ^ r))
              ≤ ∑ _r ∈ Finset.range s, Module.finrank (ZMod 2) E :=
                Finset.sum_le_sum (fun r _ => Submodule.finrank_map_le (D' ^ r) E)
            _ = s * Module.finrank (ZMod 2) E := by simp
        have h3 : Module.finrank (ZMod 2) W ≤ s * C := by
          rw [← hW_dim_eq]
          exact h1.trans (h2.trans (Nat.mul_le_mul_left s hEdim))
        have hdiv := Nat.div_add_mod (Module.finrank (ZMod 2) W + s - 1) s
        by_contra hlt
        have hge : C + 1 ≤ (Module.finrank (ZMod 2) W + s - 1) / s := by omega
        have hmul : s * C + s ≤ s * ((Module.finrank (ZMod 2) W + s - 1) / s) := by nlinarith
        omega
      have hg_bound : g ≤ C := by
        refine csSup_le hS_ne ?_
        rintro j ⟨p, hp, rfl⟩
        have hp_deg_pos : 0 < p.natDegree := by
          by_contra h0
          have hpc := Polynomial.eq_C_of_natDegree_eq_zero (by omega : p.natDegree = 0)
          have hc1 : p.coeff 0 = 1 := PEqualNP.Outside.L_pcx_381.zmod2_eq_one_of_ne_zero
            (fun h => hp.ne_zero (by rw [hpc, h, map_zero]))
          exact hp.not_isUnit (by rw [hpc, hc1, map_one]; exact isUnit_one)
        have hsoc := PEqualNP.Outside.L_pcx_381.lower_bound_socle T E hEspan p hp
        rw [PEqualNP.Outside.L_pcx_381.transpose_socle_finrank T p] at hsoc
        have hle : Module.finrank (ZMod 2)
            (W ⊓ LinearMap.ker (Polynomial.aeval D p) : Submodule (ZMod 2) (Fin n → ZMod 2)) ≤
            p.natDegree * C := hsoc.trans (Nat.mul_le_mul_left _ hEdim)
        rw [Nat.div_le_iff_le_mul_add_pred hp_deg_pos]
        omega
      have hh_le_C : h ≤ C := max_le hg_bound hdim_bound
      exact (Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by omega) hh_le_C)).trans hKbound
  · intro hKh
    have hW'_inv : W'.map D' ≤ W' := by
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨D' u, by rw [← PEqualNP.Outside.L_pcx_381.end_mul_apply,
        ← PEqualNP.Outside.L_pcx_381.end_mul_apply, ← pow_succ', ← pow_succ]⟩
    rcases PEqualNP.Outside.L_pcx_381.exists_nonzero_ann_poly D' with ⟨q, hqmonic, hqann⟩
    have hsocle_W' : ∀ p : Polynomial (ZMod 2), Irreducible p →
        Module.finrank (ZMod 2) (W' ⊓ LinearMap.ker (Polynomial.aeval D' p) : Submodule (ZMod 2) (PEqualNP.Outside.L_pcx_381.Dual n)) /
          p.natDegree ≤ h := by
      intro p hp
      rw [PEqualNP.Outside.L_pcx_381.transpose_socle_finrank T p]
      exact (le_csSup hS_bdd ⟨p, hp, rfl⟩).trans (le_max_left _ _)
    rcases PEqualNP.Outside.L_pcx_381.cyclic_decomp_of_poly D' h q.natDegree q W' le_rfl
      hqmonic.ne_zero hW'_inv (fun x _ => by rw [hqann]; rfl) hsocle_W'
      with ⟨k, v, d, hk_le, hv, hspan_cyc, hsum_deg⟩
    let items : List (PEqualNP.Outside.L_pcx_381.PackItem n) :=
      (List.finRange h).map (fun i =>
        if hi : i.val < k then
          (v ⟨i.val, hi⟩, (d ⟨i.val, hi⟩).natDegree,
            PEqualNP.Outside.L_pcx_381.cycSpan D' (v ⟨i.val, hi⟩) (d ⟨i.val, hi⟩).natDegree)
        else (0, 0, ⊥))
    have hitems_len : items.length = h := by simp [items]
    have hitems_valid : ∀ it ∈ items, PEqualNP.Outside.L_pcx_381.ValidItem D' W' ⊥ it := by
      intro it hit
      rcases List.mem_map.mp hit with ⟨i, _, rfl⟩
      split_ifs with hi
      · refine ⟨PEqualNP.Outside.L_pcx_381.cycSpan_le_of_inv D' W' hW'_inv (v ⟨i.val, hi⟩) (hv ⟨i.val, hi⟩).1 _,
          PEqualNP.Outside.L_pcx_381.cycSpan_map_le D' (v ⟨i.val, hi⟩) (d ⟨i.val, hi⟩)
            (hv ⟨i.val, hi⟩).2.1 (hv ⟨i.val, hi⟩).2.2.1, ?_, le_sup_right⟩
        have hmem := PEqualNP.Outside.L_pcx_381.cycSpan_inv_of_ann D' (v ⟨i.val, hi⟩) (d ⟨i.val, hi⟩)
          (hv ⟨i.val, hi⟩).2.1 (hv ⟨i.val, hi⟩).2.2.1 (1 : Polynomial (ZMod 2))
        simpa using hmem
      · exact ⟨bot_le, by simp, Submodule.zero_mem _, bot_le⟩
    have hitems_sum : PEqualNP.Outside.L_pcx_381.listLenSum items ≤ s * items.length := by
      rw [PEqualNP.Outside.L_pcx_381.listLenSum_eq_map_sum, hitems_len]
      have hmap_eq : items.map (fun it => it.2.1) =
          (List.finRange h).map (fun i => if hi : i.val < k then (d ⟨i.val, hi⟩).natDegree else 0) := by
        simp only [items, List.map_map]
        refine List.map_congr_left (fun i _ => ?_)
        dsimp only [Function.comp]
        split_ifs <;> rfl
      rw [hmap_eq]
      have hsum_fin : ((List.finRange h).map (fun i : Fin h =>
          if hi : i.val < k then (d ⟨i.val, hi⟩).natDegree else 0)).sum =
          ∑ i : Fin h, (if hi : i.val < k then (d ⟨i.val, hi⟩).natDegree else 0) := by
        rw [← Fin.sum_univ_def]
      rw [hsum_fin]
      have hsum_k : ∑ i : Fin h, (if hi : i.val < k then (d ⟨i.val, hi⟩).natDegree else 0) =
          ∑ j : Fin k, (d j).natDegree :=
        PEqualNP.Outside.L_pcx_381.sum_fin_dite_eq hk_le (fun j => (d j).natDegree)
      rw [hsum_k, hsum_deg, hW_dim_eq]
      have h1 : (Module.finrank (ZMod 2) W + s - 1) / s ≤ h := le_max_right _ _
      have hdiv := Nat.div_add_mod (Module.finrank (ZMod 2) W + s - 1) s
      have hmod := Nat.mod_lt (Module.finrank (ZMod 2) W + s - 1) hs
      have hmul : s * ((Module.finrank (ZMod 2) W + s - 1) / s) ≤ s * h := Nat.mul_le_mul_left s h1
      omega
    rcases PEqualNP.Outside.L_pcx_381.balance_chains_pack hs D' W' h items ⊥ (le_of_eq hitems_len)
      hitems_valid hitems_sum with ⟨G, hGW, hGdim, hGcov⟩
    rw [hitems_len] at hGdim
    rw [bot_sup_eq] at hGcov
    have hW'_le_sup : W' ≤ PEqualNP.Outside.L_pcx_381.listSup items := by
      rw [← hspan_cyc]
      refine iSup_le (fun j => ?_)
      have hmem : (v j, (d j).natDegree, PEqualNP.Outside.L_pcx_381.cycSpan D' (v j) (d j).natDegree) ∈ items := by
        rw [List.mem_map]
        refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hk_le⟩, List.mem_finRange _, ?_⟩
        dsimp only
        rw [dif_pos j.isLt]
      have hmem_le : ∀ (l : List (PEqualNP.Outside.L_pcx_381.PackItem n)) (it : PEqualNP.Outside.L_pcx_381.PackItem n),
          it ∈ l → it.2.2 ≤ PEqualNP.Outside.L_pcx_381.listSup l := by
        intro l it hit
        induction l with
        | nil => exact False.elim (List.not_mem_nil hit)
        | cons a t ihl =>
          rcases List.mem_cons.mp hit with rfl | hmemt
          · exact le_sup_left
          · exact (ihl hmemt).trans le_sup_right
      exact hmem_le items _ hmem
    rcases PEqualNP.Outside.L_pcx_381.exists_flag_of_gen hs T G hGW (hW'_le_sup.trans hGcov)
      with ⟨flag, hflag0, hflags, hmono, hcost_le⟩
    refine ⟨flag, hflag0, hflags, hmono, ?_⟩
    exact (Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by omega) (hcost_le.trans hGdim))).trans hKh
