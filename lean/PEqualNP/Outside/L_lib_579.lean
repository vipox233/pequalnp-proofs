import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_579

open Finset

def SS {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)

theorem mem_SS {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n)) (v : Fin n) :
    v ∈ SS L R ↔ (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j := by
  simp [SS]

noncomputable def ext' {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (σ : ↥(SS L R) → Bool) (v : Fin n) : Bool :=
  if h : v ∈ SS L R then σ ⟨v, h⟩ else false

noncomputable def ptL {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (σ : ↥(SS L R) → Bool) : (i : Fin l) → ((↥(L i) → Bool) → Bool) :=
  fun _ y => by classical exact decide (∀ v, y v = ext' L R σ v.val)

noncomputable def ptR {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (σ : ↥(SS L R) → Bool) : (j : Fin r) → ((↥(R j) → Bool) → Bool) :=
  fun _ y => by classical exact decide (∀ v, y v = ext' L R σ v.val)

theorem point_count {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) (σ τ : ↥(SS L R) → Bool) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, ptL L R σ i (fun v => x v.val) = true) ∧
      (∀ j, ptR L R τ j (fun v => x v.val) = true))).card = if σ = τ then 1 else 0 := by
  classical
  have key : ∀ x : Fin n → Bool, ((∀ i, ptL L R σ i (fun v => x v.val) = true) ∧
      (∀ j, ptR L R τ j (fun v => x v.val) = true)) ↔ σ = τ ∧ x = ext' L R σ := by
    intro x
    simp only [ptL, ptR, decide_eq_true_eq]
    constructor
    · rintro ⟨hl, hr⟩
      have hst : σ = τ := by
        funext s
        obtain ⟨v, hv⟩ := s
        obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := (mem_SS L R v).1 hv
        have e1 : x v = σ ⟨v, hv⟩ := by
          have := hl i ⟨v, hi⟩
          simpa [ext', hv] using this
        have e2 : x v = τ ⟨v, hv⟩ := by
          have := hr j ⟨v, hj⟩
          simpa [ext', hv] using this
        exact e1.symm.trans e2
      subst hst
      refine ⟨rfl, funext fun v => ?_⟩
      rcases hcov v with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact hl i ⟨v, hi⟩
      · exact hr j ⟨v, hj⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun i v => rfl, fun j v => rfl⟩
  split_ifs with h
  · subst h
    rw [Finset.card_eq_one]
    refine ⟨ext' L R σ, ?_⟩
    ext x
    simp [key]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact h ((key x).1 hx).1

open Classical in
noncomputable def ya {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (p : (i : Fin l) → ((↥(L i) → Bool) → Bool)) (σ : ↥(SS L R) → Bool) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter (fun y =>
    (∀ v, ¬ (∃ i, v ∈ L i) → y v = false) ∧ (∀ s : ↥(SS L R), y s.val = σ s) ∧
      ∀ i, p i (fun v => y v.val) = true)

open Classical in
noncomputable def zb {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (q : (j : Fin r) → ((↥(R j) → Bool) → Bool)) (σ : ↥(SS L R) → Bool) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter (fun z =>
    (∀ v, ¬ (∃ j, v ∈ R j) → z v = false) ∧ (∀ s : ↥(SS L R), z s.val = σ s) ∧
      ∀ j, q j (fun v => z v.val) = true)

theorem split_count {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j)
    (p : (i : Fin l) → ((↥(L i) → Bool) → Bool)) (q : (j : Fin r) → ((↥(R j) → Bool) → Bool)) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, p i (fun v => x v.val) = true) ∧
      (∀ j, q j (fun v => x v.val) = true))).card =
      ∑ σ : ↥(SS L R) → Bool, (ya L R p σ).card * (zb L R q σ).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin n → Bool => fun s : ↥(SS L R) => x s.val)
    (t := univ) (fun _ _ => Finset.mem_coe.2 (mem_univ _))]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Finset.card_product]
  apply Finset.card_nbij'
    (fun x => ((fun v => if (∃ i, v ∈ L i) then x v else false),
      (fun v => if (∃ j, v ∈ R j) then x v else false)))
    (fun yz => fun v => if (∃ i, v ∈ L i) then yz.1 v else yz.2 v)
  · intro x hx
    have hx' := Finset.mem_coe.1 hx
    rw [mem_filter, mem_filter] at hx'
    obtain ⟨⟨_, hl, hr⟩, hσ⟩ := hx'
    apply Finset.mem_coe.2
    rw [mem_product]
    refine ⟨?_, ?_⟩
    · unfold ya
      rw [mem_filter]
      refine ⟨mem_univ _, fun v hv => if_neg hv, fun s => ?_, fun i => ?_⟩
      · have hs := (mem_SS L R s.val).1 s.2
        dsimp only
        rw [if_pos hs.1]
        exact congrFun hσ s
      · have e : ∀ v : ↥(L i), ∃ k, v.val ∈ L k := fun v => ⟨i, v.2⟩
        simpa [e] using hl i
    · unfold zb
      rw [mem_filter]
      refine ⟨mem_univ _, fun v hv => if_neg hv, fun s => ?_, fun j => ?_⟩
      · have hs := (mem_SS L R s.val).1 s.2
        dsimp only
        rw [if_pos hs.2]
        exact congrFun hσ s
      · have e : ∀ v : ↥(R j), ∃ k, v.val ∈ R k := fun v => ⟨j, v.2⟩
        simpa [e] using hr j
  · intro yz hyz
    obtain ⟨y, z⟩ := yz
    have hyz' := Finset.mem_coe.1 hyz
    rw [mem_product] at hyz'
    obtain ⟨hy, hz⟩ := hyz'
    unfold ya at hy
    unfold zb at hz
    rw [mem_filter] at hy hz
    obtain ⟨_, hy0, hyσ, hyp⟩ := hy
    obtain ⟨_, hz0, hzσ, hzq⟩ := hz
    apply Finset.mem_coe.2
    rw [mem_filter, mem_filter]
    refine ⟨⟨mem_univ _, fun i => ?_, fun j => ?_⟩, ?_⟩
    · have e : ∀ v : ↥(L i), ∃ k, v.val ∈ L k := fun v => ⟨i, v.2⟩
      simpa [e] using hyp i
    · have e : ∀ v : ↥(R j), (if (∃ k, v.val ∈ L k) then y v.val else z v.val) = z v.val := by
        intro v
        split_ifs with h
        · have hs : v.val ∈ SS L R := (mem_SS L R v.val).2 ⟨h, j, v.2⟩
          have h1 : y v.val = σ ⟨v.val, hs⟩ := hyσ ⟨v.val, hs⟩
          have h2 : z v.val = σ ⟨v.val, hs⟩ := hzσ ⟨v.val, hs⟩
          rw [h1, h2]
        · rfl
      simpa [e] using hzq j
    · funext s
      have hs := (mem_SS L R s.val).1 s.2
      dsimp only
      rw [if_pos hs.1]
      exact hyσ s
  · intro x hx
    have hx' := Finset.mem_coe.1 hx
    funext v
    dsimp only
    by_cases h1 : ∃ i, v ∈ L i
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1]
      have h2 : ∃ j, v ∈ R j := (hcov v).resolve_left h1
      rw [if_pos h2]
  · intro yz hyz
    obtain ⟨y, z⟩ := yz
    have hyz' := Finset.mem_coe.1 hyz
    rw [mem_product] at hyz'
    obtain ⟨hy, hz⟩ := hyz'
    unfold ya at hy
    unfold zb at hz
    rw [mem_filter] at hy hz
    obtain ⟨_, hy0, hyσ, hyp⟩ := hy
    obtain ⟨_, hz0, hzσ, hzq⟩ := hz
    refine Prod.ext ?_ ?_
    · funext v
      dsimp only
      by_cases h1 : ∃ i, v ∈ L i
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1]
        exact (hy0 v h1).symm
    · funext v
      dsimp only
      by_cases h2 : ∃ j, v ∈ R j
      · rw [if_pos h2]
        by_cases h1 : ∃ i, v ∈ L i
        · rw [if_pos h1]
          have hs : v ∈ SS L R := (mem_SS L R v).2 ⟨h1, h2⟩
          have e1 : y v = σ ⟨v, hs⟩ := hyσ ⟨v, hs⟩
          have e2 : z v = σ ⟨v, hs⟩ := hzσ ⟨v, hs⟩
          rw [e1, e2]
        · rw [if_neg h1]
      · rw [if_neg h2]
        exact (hz0 v h2).symm

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (A : Matrix ι (Fin d) K) (B : Matrix (Fin d) ι K) (h : A * B = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

section Generic

variable {F : Type} [Field F] {t : ℕ} {T : Fin t → Type}

def mix (i : ℕ) (τ σ : (j : Fin t) → T j) : (j : Fin t) → T j :=
  fun j => if j.val < i then τ j else σ j

theorem fold_congr {S : Type} (l : List (Fin t)) (g g' : Fin t → S → S)
    (h : ∀ x ∈ l, g x = g' x) (init : S) :
    l.foldl (fun cur st => g st cur) init = l.foldl (fun cur st => g' st cur) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy => h y (by simp [hy])) _

theorem fold_lin {V : Type} [AddCommGroup V] [Module F V] (l : List (Fin t))
    (f : Fin t → V →ₗ[F] V) :
    ∃ L : V →ₗ[F] V, ∀ v, l.foldl (fun cur st => f st cur) v = L v := by
  induction l with
  | nil => exact ⟨LinearMap.id, fun v => rfl⟩
  | cons x l ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L ∘ₗ f x, fun v => by simp only [List.foldl_cons]; rw [hL]; rfl⟩

theorem mem_take_lt {i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).take i) : x.val < i := by
  obtain ⟨n, hn, hx⟩ := List.mem_take_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show n < i
  omega

theorem mem_drop_ge {i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).drop i) : i ≤ x.val := by
  obtain ⟨n, hn, hx⟩ := List.mem_drop_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show i ≤ i + n
  omega

theorem lower {d : ℕ} (c : ((j : Fin t) → T j) → F) (s : Fin d → F)
    (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
    (out : (Fin d → F) →ₗ[F] F)
    (hc : ∀ tests : (j : Fin t) → T j,
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) = c tests)
    (i : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (τ σ : ι → (j : Fin t) → T j)
    (hδ : ∀ a b, c (mix i (τ a) (σ b)) = if a = b then 1 else 0) : Fintype.card ι ≤ d := by
  let u : ι → Fin d → F := fun a =>
    ((List.finRange t).take i).foldl (fun cur stage => step stage (τ a stage) cur) s
  have hL : ∀ b, ∃ L : (Fin d → F) →ₗ[F] (Fin d → F), ∀ v,
      ((List.finRange t).drop i).foldl (fun cur stage => step stage (σ b stage) cur) v = L v :=
    fun b => fold_lin _ (fun st => step st (σ b st))
  choose L hL using hL
  have key : ∀ a b, out (L b (u a)) = if a = b then 1 else 0 := by
    intro a b
    have e1 : ((List.finRange t).take i).foldl
        (fun cur stage => step stage (mix i (τ a) (σ b) stage) cur) s = u a :=
      fold_congr _ (fun st => ⇑(step st (mix i (τ a) (σ b) st))) (fun st => ⇑(step st (τ a st)))
        (fun x hx => by simp only [mix, if_pos (mem_take_lt hx)]) s
    have e2 : ∀ v, ((List.finRange t).drop i).foldl
        (fun cur stage => step stage (mix i (τ a) (σ b) stage) cur) v =
        ((List.finRange t).drop i).foldl (fun cur stage => step stage (σ b stage) cur) v :=
      fun v => fold_congr _ (fun st => ⇑(step st (mix i (τ a) (σ b) st)))
        (fun st => ⇑(step st (σ b st)))
        (fun x hx => by simp only [mix, if_neg (not_lt.2 (mem_drop_ge hx))]) v
    rw [← hδ a b, ← hc, ← hL b, ← e1, ← e2, ← List.foldl_append, List.take_append_drop]
  have hM : (Matrix.of fun (a : ι) (j : Fin d) => u a j) *
      (Matrix.of fun (j : Fin d) (b : ι) => out (L b (fun j' => if j = j' then 1 else 0))) = 1 := by
    ext a b
    have := LinearMap.pi_apply_eq_sum_univ (out ∘ₗ L b) (u a)
    simp only [LinearMap.comp_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← key a b, this]
    simp only [Matrix.of_apply, smul_eq_mul]
  exact rank_bound d _ _ hM

def row (c : ((j : Fin t) → T j) → F) (i : ℕ) (τ : (j : Fin t) → T j) :
    ((j : Fin t) → T j) → F :=
  fun σ => c (mix i τ σ)

def RS (c : ((j : Fin t) → T j) → F) (i : ℕ) : Submodule F (((j : Fin t) → T j) → F) :=
  Submodule.span F (Set.range (row c i))

theorem row_mem (c : ((j : Fin t) → T j) → F) (i : ℕ) (τ : (j : Fin t) → T j) :
    row c i τ ∈ RS c i :=
  Submodule.subset_span ⟨τ, rfl⟩

def shiftL (j : Fin t) (x : T j) :
    (((j : Fin t) → T j) → F) →ₗ[F] (((j : Fin t) → T j) → F) :=
  LinearMap.funLeft F F (fun σ => Function.update σ j x)

theorem mix_update (i : Fin t) (x : T i) (τ σ : (j : Fin t) → T j) :
    mix i.val τ (Function.update σ i x) = mix (i.val + 1) (Function.update τ i x) σ := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [mix]
  · have hne : l.val ≠ i.val := fun h => hl (Fin.ext h)
    simp only [mix, Function.update_of_ne hl]
    by_cases h1 : l.val < i.val
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem shift_row (c : ((j : Fin t) → T j) → F) (j : Fin t) (x : T j) (τ : (j : Fin t) → T j) :
    shiftL j x (row c j.val τ) = row c (j.val + 1) (Function.update τ j x) := by
  funext σ
  simp only [shiftL, LinearMap.funLeft_apply, row]
  rw [mix_update]

theorem shift_maps (c : ((j : Fin t) → T j) → F) (j : Fin t) (x : T j) :
    ∀ r ∈ RS c j.val, shiftL j x r ∈ RS c (j.val + 1) := by
  intro r hr
  have hle : RS c j.val ≤ (RS c (j.val + 1)).comap (shiftL j x) := by
    rw [RS, Submodule.span_le]
    rintro _ ⟨τ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [shift_row]
    exact row_mem _ _ _
  exact hle hr

theorem embed {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (d : ℕ)
    (h : Module.finrank F V ≤ d) :
    ∃ (e : V →ₗ[F] (Fin d → F)) (p : (Fin d → F) →ₗ[F] V), ∀ v, p (e v) = v := by
  let b := Module.finBasis F V
  let ins : (Fin (Module.finrank F V) → F) →ₗ[F] (Fin d → F) :=
    { toFun := fun v j => if hj : j.val < Module.finrank F V then v ⟨j.val, hj⟩ else 0
      map_add' := fun v w => by
        funext j
        by_cases hj : j.val < Module.finrank F V <;> simp [hj]
      map_smul' := fun a v => by
        funext j
        by_cases hj : j.val < Module.finrank F V <;> simp [hj] }
  let pr : (Fin d → F) →ₗ[F] (Fin (Module.finrank F V) → F) :=
    LinearMap.funLeft F F (Fin.castLE h)
  refine ⟨ins ∘ₗ b.equivFun.toLinearMap, b.equivFun.symm.toLinearMap ∘ₗ pr, fun v => ?_⟩
  have hpi : ∀ w, pr (ins w) = w := by
    intro w
    funext j
    simp [pr, ins, LinearMap.funLeft_apply, j.isLt]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpi, LinearEquiv.symm_apply_apply]

theorem upper {d : ℕ} [∀ j, Fintype (T j)] [∀ j, DecidableEq (T j)]
    (c : ((j : Fin t) → T j) → F) (τ0 : (j : Fin t) → T j)
    (hR : ∀ i, i ≤ t → Module.finrank F (RS c i) ≤ d) :
    ∃ (s : Fin d → F) (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
      (out : (Fin d → F) →ₗ[F] F), ∀ tests : (j : Fin t) → T j,
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
        c tests := by
  have hE : ∀ i, i ≤ t → ∃ (e : RS c i →ₗ[F] (Fin d → F)) (p : (Fin d → F) →ₗ[F] RS c i),
      ∀ v, p (e v) = v := fun i hi => embed d (hR i hi)
  choose e p hep using hE
  let st : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)) := fun j x =>
    e (j.val + 1) j.isLt ∘ₗ ((shiftL j x).restrict (shift_maps c j x)) ∘ₗ p j.val j.isLt.le
  let ev : (((j : Fin t) → T j) → F) →ₗ[F] F := LinearMap.proj τ0
  refine ⟨e 0 (Nat.zero_le _) ⟨row c 0 τ0, row_mem c 0 τ0⟩, st,
    ev ∘ₗ (RS c t).subtype ∘ₗ p t le_rfl, fun tests => ?_⟩
  have inv : ∀ i (hi : i ≤ t), ((List.finRange t).take i).foldl
      (fun cur stage => st stage (tests stage) cur)
      (e 0 (Nat.zero_le _) ⟨row c 0 τ0, row_mem c 0 τ0⟩) =
        e i hi ⟨row c i tests, row_mem c i tests⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simp only [List.take_zero, List.foldl_nil]
      congr 2
    | succ i ih =>
      intro hi
      have hget : (List.finRange t)[i]? = some ⟨i, by omega⟩ := by
        rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_finRange]
        rfl
      rw [List.take_add_one, List.foldl_append, ih (by omega), hget]
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
      simp only [st, LinearMap.comp_apply, hep]
      congr 1
      apply Subtype.ext
      rw [LinearMap.restrict_apply]
      show shiftL _ _ (row c i tests) = row c (i + 1) tests
      rw [shift_row]
      simp
  have h2 := inv t le_rfl
  rw [List.take_of_length_le (by simp)] at h2
  rw [h2]
  simp only [LinearMap.comp_apply, hep, ev, LinearMap.proj_apply, Submodule.subtype_apply, row]
  congr 1
  funext j
  simp [mix, j.isLt]

end Generic

section Scan

variable {n m t : ℕ}

abbrev Tab (m : ℕ) := (Fin m → Bool) → Bool

noncomputable def cnt (K : Type) [Field K] (pos : Fin t → Fin m → Fin n)
    (tests : Fin t → Tab m) : K :=
  (((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
    ∀ j, tests j (fun l => x (pos j l)) = true)).card : K)

def Pset (pos : Fin t → Fin m → Fin n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ j : Fin t, j.val < i ∧ ∃ l, pos j l = v)

def Qset (pos : Fin t → Fin m → Fin n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ j : Fin t, i ≤ j.val ∧ ∃ l, pos j l = v)

theorem mem_Pset (pos : Fin t → Fin m → Fin n) (i : ℕ) (v : Fin n) :
    v ∈ Pset pos i ↔ ∃ j : Fin t, j.val < i ∧ ∃ l, pos j l = v := by
  simp [Pset]

theorem mem_Qset (pos : Fin t → Fin m → Fin n) (i : ℕ) (v : Fin n) :
    v ∈ Qset pos i ↔ ∃ j : Fin t, i ≤ j.val ∧ ∃ l, pos j l = v := by
  simp [Qset]

abbrev LL (pos : Fin t → Fin m → Fin n) (i : ℕ) : Fin 1 → Finset (Fin n) := fun _ => Pset pos i

abbrev RR (pos : Fin t → Fin m → Fin n) (i : ℕ) : Fin 1 → Finset (Fin n) := fun _ => Qset pos i

theorem cover (pos : Fin t → Fin m → Fin n) (hc : ∀ v, ∃ j l, pos j l = v) (i : ℕ) :
    ∀ v : Fin n, (∃ k, v ∈ LL pos i k) ∨ ∃ k, v ∈ RR pos i k := by
  intro v
  obtain ⟨j, l, h⟩ := hc v
  by_cases hj : j.val < i
  · exact Or.inl ⟨0, (mem_Pset pos i v).2 ⟨j, hj, l, h⟩⟩
  · exact Or.inr ⟨0, (mem_Qset pos i v).2 ⟨j, not_lt.1 hj, l, h⟩⟩

noncomputable def pL (pos : Fin t → Fin m → Fin n) (i : ℕ) (τ : Fin t → Tab m) :
    (k : Fin 1) → ((↥(LL pos i k) → Bool) → Bool) :=
  fun _ z => by
    classical
    exact decide (∀ j : Fin t, ∀ hj : j.val < i,
      τ j (fun l => z ⟨pos j l, (mem_Pset pos i _).2 ⟨j, hj, l, rfl⟩⟩) = true)

noncomputable def qR (pos : Fin t → Fin m → Fin n) (i : ℕ) (σ : Fin t → Tab m) :
    (k : Fin 1) → ((↥(RR pos i k) → Bool) → Bool) :=
  fun _ z => by
    classical
    exact decide (∀ j : Fin t, ∀ hj : i ≤ j.val,
      σ j (fun l => z ⟨pos j l, (mem_Qset pos i _).2 ⟨j, hj, l, rfl⟩⟩) = true)

theorem cnt_mix (K : Type) [Field K] (pos : Fin t → Fin m → Fin n) (i : ℕ)
    (τ σ : Fin t → Tab m) :
    cnt K pos (mix (T := fun _ => Tab m) i τ σ) =
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ k, pL pos i τ k (fun v => x v.val) = true) ∧
        (∀ k, qR pos i σ k (fun v => x v.val) = true))).card : ℕ) : K) := by
  unfold cnt
  congr 2
  apply Finset.filter_congr
  intro x _
  simp only [pL, qR, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun _ j hj => ?_, fun _ j hj => ?_⟩
    · have := h j
      simp only [mix, if_pos hj] at this
      exact this
    · have := h j
      simp only [mix, if_neg (not_lt.2 hj)] at this
      exact this
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j.val < i
    · simp only [mix, if_pos hj]
      exact h1 0 j hj
    · simp only [mix, if_neg hj]
      exact h2 0 j (not_lt.1 hj)

noncomputable def pinT (pos : Fin t → Fin m → Fin n) (i : ℕ)
    (σ : ↥(SS (LL pos i) (RR pos i)) → Bool) : Fin t → Tab m :=
  fun j y => by
    classical
    exact decide (y = fun l => ext' (LL pos i) (RR pos i) σ (pos j l))

theorem pL_pin (pos : Fin t → Fin m → Fin n) (i : ℕ) (σ : ↥(SS (LL pos i) (RR pos i)) → Bool) :
    pL pos i (pinT pos i σ) = ptL (LL pos i) (RR pos i) σ := by
  funext k z
  rw [Bool.eq_iff_iff]
  simp only [pL, ptL, pinT, decide_eq_true_eq]
  constructor
  · intro h v
    obtain ⟨v0, hv⟩ := v
    obtain ⟨j, hj, l, rfl⟩ := (mem_Pset pos i v0).1 hv
    exact congrFun (h j hj) l
  · intro h j hj
    funext l
    exact h _

theorem qR_pin (pos : Fin t → Fin m → Fin n) (i : ℕ) (σ : ↥(SS (LL pos i) (RR pos i)) → Bool) :
    qR pos i (pinT pos i σ) = ptR (LL pos i) (RR pos i) σ := by
  funext k z
  rw [Bool.eq_iff_iff]
  simp only [qR, ptR, pinT, decide_eq_true_eq]
  constructor
  · intro h v
    obtain ⟨v0, hv⟩ := v
    obtain ⟨j, hj, l, rfl⟩ := (mem_Qset pos i v0).1 hv
    exact congrFun (h j hj) l
  · intro h j hj
    funext l
    exact h _

theorem low_cut (K : Type) [Field K] (pos : Fin t → Fin m → Fin n)
    (hc : ∀ v, ∃ j l, pos j l = v) (d : ℕ) (s : Fin d → K)
    (step : Fin t → Tab m → ((Fin d → K) →ₗ[K] (Fin d → K)))
    (out : (Fin d → K) →ₗ[K] K)
    (h : ∀ tests : Fin t → Tab m,
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
        cnt K pos tests) (i : ℕ) :
    2 ^ (SS (LL pos i) (RR pos i)).card ≤ d := by
  classical
  have := lower (T := fun _ => Tab m) (cnt K pos) s step out h i (pinT pos i) (pinT pos i)
    (fun a b => by
      rw [cnt_mix, pL_pin, qR_pin, point_count _ _ (cover pos hc i)]
      split_ifs <;> simp)
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at this

theorem up_cut (K : Type) [Field K] (pos : Fin t → Fin m → Fin n)
    (hc : ∀ v, ∃ j l, pos j l = v) (i : ℕ) :
    Module.finrank K (RS (T := fun _ => Tab m) (cnt K pos) i) ≤
      2 ^ (SS (LL pos i) (RR pos i)).card := by
  classical
  let B : (↥(SS (LL pos i) (RR pos i)) → Bool) → (Fin t → Tab m) → K := fun σ' σ =>
    ((zb (LL pos i) (RR pos i) (qR pos i σ) σ').card : K)
  have hrow : ∀ τ, row (T := fun _ => Tab m) (cnt K pos) i τ =
      ∑ σ', ((ya (LL pos i) (RR pos i) (pL pos i τ) σ').card : K) • B σ' := by
    intro τ
    funext σ
    simp only [row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B]
    rw [cnt_mix, split_count _ _ (cover pos hc i)]
    push_cast
    rfl
  have hle : RS (T := fun _ => Tab m) (cnt K pos) i ≤ Submodule.span K (Set.range B) := by
    rw [RS, Submodule.span_le]
    rintro _ ⟨τ, rfl⟩
    rw [SetLike.mem_coe, hrow]
    exact Submodule.sum_mem _ (fun σ' _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ', rfl⟩))
  calc Module.finrank K (RS (T := fun _ => Tab m) (cnt K pos) i)
      ≤ Module.finrank K (Submodule.span K (Set.range B)) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (↥(SS (LL pos i) (RR pos i)) → Bool) := finrank_range_le_card B
    _ = 2 ^ (SS (LL pos i) (RR pos i)).card := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

end Scan

section Comb

open Fin.CommRing

def wpos (a w : ℕ) (order : Equiv.Perm (Fin (a + 2))) : Fin (a + 2) → Fin (w + 1) → Fin (a + 2) :=
  fun j l => Fin.ofNat (a + 2) ((order j).val + l.val)

theorem wpos_eq (a w : ℕ) (order : Equiv.Perm (Fin (a + 2))) (j : Fin (a + 2)) (l : Fin (w + 1)) :
    wpos a w order j l = order j + ((l.val : ℕ) : Fin (a + 2)) := by
  rw [wpos, Fin.ofNat_eq_cast, Nat.cast_add, Fin.cast_val_eq_self]

theorem wpos_cover (a w : ℕ) (order : Equiv.Perm (Fin (a + 2))) :
    ∀ v, ∃ j l, wpos a w order j l = v := by
  intro v
  refine ⟨order.symm v, 0, ?_⟩
  rw [wpos_eq]
  simp

noncomputable def nearSet (a w : ℕ) (A : Finset (Fin (a + 2))) : Finset (Fin (a + 2)) := by
  classical
  exact A.filter (fun v => ∃ k : ℕ, 1 ≤ k ∧ k ≤ w ∧ v - (k : Fin (a + 2)) ∉ A)

theorem mem_nearSet (a w : ℕ) (A : Finset (Fin (a + 2))) (v : Fin (a + 2)) :
    v ∈ nearSet a w A ↔ v ∈ A ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ w ∧ v - (k : Fin (a + 2)) ∉ A := by
  classical
  unfold nearSet
  simp only [Finset.mem_filter]

theorem near (a w : ℕ) (A : Finset (Fin (a + 2))) (b : Fin (a + 2)) (hb : b ∉ A) :
    min w A.card ≤ (nearSet a w A).card := by
  classical
  by_cases hall : ∀ v ∈ A, ∃ k : ℕ, 1 ≤ k ∧ k ≤ w ∧ v - (k : Fin (a + 2)) ∉ A
  · have hsub : A ⊆ nearSet a w A := fun v hv => (mem_nearSet a w A v).2 ⟨hv, hall v hv⟩
    exact (min_le_right _ _).trans (Finset.card_le_card hsub)
  · push_neg at hall
    obtain ⟨p, hp, hpw⟩ := hall
    have hpb : 1 ≤ (p - b).val := by
      rcases Nat.eq_zero_or_pos (p - b).val with h0 | h0
      · exfalso
        have h1 : p - b = 0 := Fin.ext (by simp [h0])
        rw [sub_eq_zero] at h1
        exact hb (h1 ▸ hp)
      · exact h0
    have hpb2 : p - (((p - b).val : ℕ) : Fin (a + 2)) ∉ A := by
      rw [Fin.cast_val_eq_self, sub_sub_cancel]
      exact hb
    have hex : ∃ D : ℕ, 1 ≤ D ∧ p - (D : Fin (a + 2)) ∉ A := ⟨_, hpb, hpb2⟩
    have hD1 : 1 ≤ Nat.find hex := (Nat.find_spec hex).1
    have hDA : p - ((Nat.find hex : ℕ) : Fin (a + 2)) ∉ A := (Nat.find_spec hex).2
    have hmin : ∀ k, k < Nat.find hex → 1 ≤ k → p - (k : Fin (a + 2)) ∈ A := by
      intro k hk h1
      by_contra hc
      exact Nat.find_min hex hk ⟨h1, hc⟩
    have hwD : w < Nat.find hex := by
      by_contra hc
      push_neg at hc
      exact hDA (hpw _ hD1 hc)
    have hDn : Nat.find hex < a + 2 :=
      lt_of_le_of_lt (Nat.find_min' hex ⟨hpb, hpb2⟩) (p - b).isLt
    let f : ℕ → Fin (a + 2) := fun k => p - ((Nat.find hex : ℕ) : Fin (a + 2)) + (k : Fin (a + 2))
    have himg : (Finset.Icc 1 w).image f ⊆ nearSet a w A := by
      intro v hv
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hv
      rw [Finset.mem_Icc] at hk
      rw [mem_nearSet]
      refine ⟨?_, k, hk.1, hk.2, ?_⟩
      · have e : f k = p - ((Nat.find hex - k : ℕ) : Fin (a + 2)) := by
          simp only [f]
          rw [Nat.cast_sub (by omega)]
          ring
        rw [e]
        exact hmin _ (by omega) (by omega)
      · simp only [f]
        rw [add_sub_cancel_right]
        exact hDA
    have hinj : Set.InjOn f (Finset.Icc 1 w : Set ℕ) := by
      intro x hx y hy hxy
      have hx' := Finset.mem_Icc.1 (Finset.mem_coe.1 hx)
      have hy' := Finset.mem_Icc.1 (Finset.mem_coe.1 hy)
      have h2 : (x : Fin (a + 2)) = (y : Fin (a + 2)) := add_left_cancel hxy
      have h3 := congrArg Fin.val h2
      rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h3
      exact h3
    have hc := Finset.card_le_card himg
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at hc
    omega

theorem comb_lower (a w : ℕ) (order : Equiv.Perm (Fin (a + 2))) :
    min (a + 2) (2 * w) ≤ (SS (LL (wpos a w order) ((a + 2) / 2))
      (RR (wpos a w order) ((a + 2) / 2))).card := by
  classical
  let i := (a + 2) / 2
  have hi1 : 1 ≤ i := by omega
  have hi2 : i < a + 2 := by omega
  let A : Finset (Fin (a + 2)) := Finset.univ.filter (fun s => (order.symm s).val < i)
  have hA : A.card = i := by
    have e : A = (Finset.univ.filter (fun j : Fin (a + 2) => j.val < i)).map order.toEmbedding := by
      ext s
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.toEmbedding_apply]
      constructor
      · intro h
        exact ⟨order.symm s, h, by simp⟩
      · rintro ⟨j, hj, rfl⟩
        simpa using hj
    rw [e, Finset.card_map]
    have e2 : (Finset.univ.filter (fun j : Fin (a + 2) => j.val < i)) =
        Finset.Iio (⟨i, hi2⟩ : Fin (a + 2)) := by
      ext j
      simp [Fin.lt_def]
    rw [e2, Fin.card_Iio]
  have hAc : Aᶜ.card = a + 2 - i := by
    rw [Finset.card_compl, Fintype.card_fin, hA]
  have hb1 : order ⟨a + 1, by omega⟩ ∉ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    show ¬ (a + 1 < i)
    omega
  have hb2 : order ⟨0, by omega⟩ ∉ Aᶜ := by
    simp only [A, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply, not_not]
    show 0 < i
    omega
  have n1 := near a w A _ hb1
  have n2 := near a w Aᶜ _ hb2
  have hsub1 : nearSet a w A ⊆ SS (LL (wpos a w order) i) (RR (wpos a w order) i) := by
    intro v hv
    obtain ⟨hvA, k, hk1, hkw, hk⟩ := (mem_nearSet a w A v).1 hv
    rw [mem_SS]
    have hvA' : (order.symm v).val < i := by simpa [A] using hvA
    have hk' : ¬ (order.symm (v - (k : Fin (a + 2)))).val < i := by simpa [A] using hk
    refine ⟨⟨0, (mem_Pset _ _ _).2 ⟨order.symm v, hvA', 0, ?_⟩⟩,
      ⟨0, (mem_Qset _ _ _).2 ⟨order.symm (v - (k : Fin (a + 2))), not_lt.1 hk',
        ⟨k, by omega⟩, ?_⟩⟩⟩
    · rw [wpos_eq]
      simp
    · rw [wpos_eq]
      simp
  have hsub2 : nearSet a w Aᶜ ⊆ SS (LL (wpos a w order) i) (RR (wpos a w order) i) := by
    intro v hv
    obtain ⟨hvA, k, hk1, hkw, hk⟩ := (mem_nearSet a w Aᶜ v).1 hv
    rw [mem_SS]
    have hvA' : ¬ (order.symm v).val < i := by simpa [A] using hvA
    have hk' : (order.symm (v - (k : Fin (a + 2)))).val < i := by simpa [A] using hk
    refine ⟨⟨0, (mem_Pset _ _ _).2 ⟨order.symm (v - (k : Fin (a + 2))), hk',
        ⟨k, by omega⟩, ?_⟩⟩,
      ⟨0, (mem_Qset _ _ _).2 ⟨order.symm v, not_lt.1 hvA', 0, ?_⟩⟩⟩
    · rw [wpos_eq]
      simp
    · rw [wpos_eq]
      simp
  have hdis : Disjoint (nearSet a w A) (nearSet a w Aᶜ) :=
    Finset.disjoint_left.2 (fun v h1 h2 =>
      (Finset.mem_compl.1 ((mem_nearSet a w Aᶜ v).1 h2).1) ((mem_nearSet a w A v).1 h1).1)
  have hc := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
  rw [Finset.card_union_of_disjoint hdis] at hc
  rw [hA] at n1
  rw [hAc] at n2
  show min (a + 2) (2 * w) ≤ (SS (LL (wpos a w order) i) (RR (wpos a w order) i)).card
  omega

theorem arith (n w i j l j' l' v : ℕ) (hj : j < i) (hj' : i ≤ j') (hj'n : j' < n)
    (hl : l ≤ w) (hl' : l' ≤ w) (hv : v < n)
    (h1 : (j + l) % n = v) (h2 : (j' + l') % n = v) : v < w ∨ (i ≤ v ∧ v < i + w) := by
  by_cases hwn : w < n
  · have key : ∀ x, x < 2 * n → (x % n = x ∧ x < n) ∨ (x % n = x - n ∧ n ≤ x) := by
      intro x hx
      by_cases h : x < n
      · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
      · right
        refine ⟨?_, by omega⟩
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rcases key (j + l) (by omega) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases key (j' + l') (by omega) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> omega
  · left
    omega

theorem comb_upper (a w i : ℕ) :
    (SS (LL (wpos a w (Equiv.refl _)) i) (RR (wpos a w (Equiv.refl _)) i)).card ≤
      min (a + 2) (2 * w) := by
  classical
  apply le_min
  · exact (Finset.card_le_univ _).trans (by simp)
  · have hsub : SS (LL (wpos a w (Equiv.refl _)) i) (RR (wpos a w (Equiv.refl _)) i) ⊆
        Finset.univ.filter (fun v : Fin (a + 2) => v.val < w) ∪
          Finset.univ.filter (fun v : Fin (a + 2) => i ≤ v.val ∧ v.val < i + w) := by
      intro v hv
      rw [mem_SS] at hv
      obtain ⟨⟨_, hP⟩, ⟨_, hQ⟩⟩ := hv
      obtain ⟨j, hj, l, hl⟩ := (mem_Pset _ _ _).1 hP
      obtain ⟨j', hj', l', hl'⟩ := (mem_Qset _ _ _).1 hQ
      have e1 : (j.val + l.val) % (a + 2) = v.val := by
        rw [← hl, wpos, Fin.val_ofNat]
        rfl
      have e2 : (j'.val + l'.val) % (a + 2) = v.val := by
        rw [← hl', wpos, Fin.val_ofNat]
        rfl
      rcases arith (a + 2) w i j.val l.val j'.val l'.val v.val hj hj' j'.isLt
          (Nat.lt_succ_iff.1 l.isLt) (Nat.lt_succ_iff.1 l'.isLt) v.isLt e1 e2 with h | h
      · exact Finset.mem_union_left _ (by simp [h])
      · exact Finset.mem_union_right _ (by simp [h])
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have c1 : (Finset.univ.filter (fun v : Fin (a + 2) => v.val < w)).card ≤ w := by
      have := Finset.card_le_card_of_injOn
        (s := Finset.univ.filter (fun v : Fin (a + 2) => v.val < w)) (t := Finset.range w) Fin.val
        (by intro v hv; simpa using hv) Fin.val_injective.injOn
      simpa using this
    have c2 : (Finset.univ.filter (fun v : Fin (a + 2) => i ≤ v.val ∧ v.val < i + w)).card ≤ w := by
      have := Finset.card_le_card_of_injOn
        (s := Finset.univ.filter (fun v : Fin (a + 2) => i ≤ v.val ∧ v.val < i + w))
        (t := Finset.Ico i (i + w)) Fin.val
        (by intro v hv; simpa using hv) Fin.val_injective.injOn
      simpa using this
    omega

end Comb

end PEqualNP.Outside.L_lib_579

open PEqualNP.Outside.L_lib_579 in
theorem PEqualNP.Outside.L_lib_579 : ∀ (K : Type) [Field K] (a w d : ℕ),
  let n := a + 2
  let Table := (Fin (w + 1) → Bool) → Bool
  let count := fun (T : Fin n → Table) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, T i (fun j => x (Fin.ofNat (a + 2) (i.val + j.val))) = true)).card
  (∃ (order : Equiv.Perm (Fin n)) (s : Fin d → K)
      (step : Fin n → Table → (Fin d → K) →ₗ[K] (Fin d → K))
      (out : (Fin d → K) →ₗ[K] K),
    ∀ T : Fin n → Table,
      out ((List.finRange n).foldl (fun v j => step j (T (order j)) v) s) =
        (count T : K)) ↔
    2 ^ min n (2 * w) ≤ d := by
  intro K _ a w d
  dsimp only
  constructor
  · rintro ⟨order, s, step, out, h⟩
    have hsc : ∀ tests : Fin (a + 2) → Tab (w + 1),
        out ((List.finRange (a + 2)).foldl (fun cur stage => step stage (tests stage) cur) s) =
          cnt K (wpos a w order) tests := by
      intro tests
      have := h (fun p => tests (order.symm p))
      simp only [Equiv.symm_apply_apply] at this
      rw [this]
      unfold cnt
      congr 2
      apply Finset.filter_congr
      intro x _
      constructor
      · intro hx j
        have := hx (order j)
        simp only [Equiv.symm_apply_apply] at this
        exact this
      · intro hx p
        have := hx (order.symm p)
        simp only [wpos, Equiv.apply_symm_apply] at this
        exact this
    have hlow := low_cut K (wpos a w order) (wpos_cover a w order) d s step out hsc ((a + 2) / 2)
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (comb_lower a w order)) hlow
  · intro hd
    obtain ⟨s, step, out, h⟩ := upper (T := fun _ => Tab (w + 1))
      (cnt K (wpos a w (Equiv.refl _))) (fun _ _ => true)
      (fun i _ => (up_cut K _ (wpos_cover a w (Equiv.refl _)) i).trans
        ((Nat.pow_le_pow_right (by norm_num) (comb_upper a w i)).trans hd))
    refine ⟨Equiv.refl _, s, step, out, fun T => ?_⟩
    exact h T
