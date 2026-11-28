import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_833

open scoped BigOperators

abbrev F := ZMod 2

abbrev Vec (m : ℕ) := Fin m → F

def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

def good {m : ℕ} (w : List (Vec m)) (U : Submodule F (Vec w.length)) : Prop :=
  (∀ x ∈ U, ∀ a : Fin m, (∑ i, w.get i a * x i) = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)

noncomputable def count {m : ℕ} (d : ℕ) (w : List (Vec m)) : ℚ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  letI : Fintype (Submodule F (Vec w.length)) := Fintype.ofFinite _
  (((Finset.univ : Finset (Submodule F (Vec w.length))).filter
    (fun (U : Submodule F (Vec w.length)) => Module.finrank F U = d ∧ good w U)).card : ℚ)

def Fits {A : Type*} (g : List A → ℚ) (k : ℕ) (test : List A → Prop) : Prop :=
  ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
    ∀ w : List A, test w →
      (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) = g w

lemma count_zero {m : ℕ} (w : List (Vec m)) : count 0 w = 1 := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  letI : Fintype (Submodule F (Vec w.length)) := Fintype.ofFinite _
  unfold count
  have h : (Finset.univ : Finset (Submodule F (Vec w.length))).filter
        (fun (U : Submodule F (Vec w.length)) => Module.finrank F U = 0 ∧ good w U) = {⊥} := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun hU => Submodule.finrank_eq_zero.mp hU.1
    · rintro rfl
      simp [good]
  rw [h]
  simp

lemma fits_const_one {A : Type*} (k : ℕ) (test : List A → Prop)
    (htest : ∃ w : List A, test w) : Fits (fun _ => 1) k test ↔ 1 ≤ k := by
  classical
  constructor
  · rintro ⟨u, v, M, h⟩
    obtain ⟨w, hw⟩ := htest
    by_contra hn
    have hk : k = 0 := by omega
    subst k
    simpa using h w hw
  · intro hk
    let p : Fin k := ⟨0, by omega⟩
    refine ⟨fun i => if i = p then 1 else 0, fun i => if i = p then 1 else 0,
      fun _ => 1, ?_⟩
    intro w _
    have hM : (w.map (fun _ => (1 : Matrix (Fin k) (Fin k) ℚ))).prod = 1 := by
      induction w with
      | nil => simp
      | cons a w ih => simp [ih]
    rw [hM]
    simp [Matrix.one_apply, ite_mul, mul_ite]

lemma solve_zero (m k : ℕ) :
    (Fits (count (m := m) 0) k (fun w => 0 < w.length) ↔ 1 ≤ k) ∧
    (Fits (count (m := m) 0) k (fun _ => True) ↔ 1 ≤ k) := by
  have h : count (m := m) 0 = fun _ => (1 : ℚ) := funext count_zero
  rw [h]
  exact ⟨fits_const_one k _ ⟨[0], by simp⟩, fits_const_one k _ ⟨[], trivial⟩⟩

lemma two_cases (a : F) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  have h' : a.val = 0 ∨ a.val = 1 := by omega
  rcases h' with h0 | h1
  · exact Or.inl (ZMod.val_injective 2 (by simpa using h0))
  · exact Or.inr (ZMod.val_injective 2 (h1.trans (by decide)))

def dot {m : ℕ} (a b : Vec m) : F := ∑ i, a i * b i

def check {m : ℕ} (w : List (Vec m)) (x : Vec w.length) : Vec m :=
  fun a => ∑ i, w.get i a * x i

lemma check_zero {m : ℕ} (w : List (Vec m)) : check w 0 = 0 := by
  ext a
  simp [check]

lemma mem_span_binary {n : ℕ} {x y : Vec n} :
    x ∈ Submodule.span F {y} ↔ x = 0 ∨ x = y := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases two_cases a with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

lemma good_span_binary {m : ℕ} (w : List (Vec m)) (x : Vec w.length) :
    good w (Submodule.span F {x}) ↔ check w x = 0 := by
  constructor
  · intro h
    exact funext (h.1 x (Submodule.mem_span_singleton_self x))
  · intro h
    constructor
    · intro y hy a
      rcases mem_span_binary.mp hy with rfl | rfl
      · simp
      · exact congrFun h a
    · intro y hy z hz i
      rcases mem_span_binary.mp hy with rfl | rfl <;>
        rcases mem_span_binary.mp hz with rfl | rfl <;> simp [mul_comm]

lemma count_one {m : ℕ} (w : List (Vec m)) :
    count 1 w = (∑ x : Vec w.length, if check w x = 0 then (1 : ℚ) else 0) - 1 := by
  letI : Fintype (Vec w.length) := inferInstance
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  letI : Fintype (Submodule F (Vec w.length)) := Fintype.ofFinite _
  let s := (Finset.univ : Finset (Vec w.length)).filter (fun x => check w x = 0)
  have h0 : 0 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, check_zero w⟩
  have hs : (s.erase 0).card =
      ((Finset.univ : Finset (Submodule F (Vec w.length))).filter
        (fun (U : Submodule F (Vec w.length)) => Module.finrank F U = 1 ∧ good w U)).card := by
    apply Finset.card_bij (fun x _ => Submodule.span F {x})
    · intro x hx
      obtain ⟨hx0, hx⟩ := Finset.mem_erase.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, finrank_span_singleton hx0,
        (good_span_binary w x).mpr (Finset.mem_filter.mp hx).2⟩
    · intro x hx y _ h
      have hm : x ∈ Submodule.span F {y} := h ▸ Submodule.mem_span_singleton_self x
      exact (mem_span_binary.mp hm).resolve_left (Finset.mem_erase.mp hx).1
    · intro U hU
      have h := (Finset.mem_filter.mp hU).2
      have hne : U ≠ ⊥ := by
        intro he
        subst U
        exact Nat.zero_ne_one (by simpa using h.1)
      obtain ⟨x, hx, hx0⟩ := U.ne_bot_iff.mp hne
      have he := eq_span_singleton_of_mem_of_finrank_eq_one h.1 hx hx0
      have hc : check w x = 0 := (good_span_binary w x).mp (he ▸ h.2)
      exact ⟨x, Finset.mem_erase.mpr ⟨hx0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩, he.symm⟩
  unfold count
  rw [← hs, Finset.card_erase_of_mem h0, Nat.cast_sub (Finset.card_pos.mpr ⟨0, h0⟩)]
  congr 1
  refine (Finset.natCast_card_filter (R := ℚ) (fun x : Vec w.length => check w x = 0)
    Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : check w x = 0 <;> simp [hx]

def sign (x : F) : ℚ := if x = 0 then 1 else -1

lemma sign_add (a b : F) : sign (a + b) = sign a * sign b := by
  have h0 : sign (0 : F) = 1 := if_pos rfl
  have h1 : sign (1 : F) = -1 := if_neg one_ne_zero
  have h2 : (1 : F) + 1 = 0 := by decide
  rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl <;> simp [h0, h1, h2]

lemma sign_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => simp [ha, sign_add, ih]

lemma dot_add_left {m : ℕ} (a b c : Vec m) : dot (a+b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_single_left {m : ℕ} (a : Vec m) (i : Fin m) : dot (Pi.single i 1) a = a i := by
  unfold dot
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [Pi.single_eq_of_ne h]
  · simp

lemma card_vec (m : ℕ) : Fintype.card (Vec m) = 2 ^ m := by simp [Vec, F]

lemma sum_sign_dot {m : ℕ} (a : Vec m) :
    (∑ b : Vec m, sign (dot b a)) = if a = 0 then (2 : ℚ)^m else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [dot, sign, card_vec]
  · have hn : ∃ i : Fin m, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hn
    have hi' := (two_cases (a i)).resolve_left hi
    let e : Vec m ≃ Vec m := Equiv.addLeft (Pi.single i 1)
    have h := e.sum_comp (fun b => sign (dot b a))
    change (∑ b : Vec m, sign (dot ((Pi.single i (1 : F) : Vec m) + b) a)) = _ at h
    simp only [dot_add_left, dot_single_left, hi', sign_add, show sign (1 : F) = -1 by simp [sign],
      neg_one_mul, Finset.sum_neg_distrib] at h
    simp only [ha, if_false]
    linarith

lemma dot_check {m : ℕ} (w : List (Vec m)) (b : Vec m) (x : Vec w.length) :
    dot b (check w x) = ∑ i, dot b (w.get i) * x i := by
  simp only [dot, check, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

lemma sum_sign_mul (a : F) : (∑ t : F, sign (a*t)) = 1 + sign a := by
  have h : (Finset.univ : Finset F) = {0, 1} := by
    ext t
    simp [two_cases t]
  rw [h, Finset.sum_insert (by decide)]
  simp [sign]

def letter {m : ℕ} (b a : Vec m) : ℚ := 1 + sign (dot b a)

lemma sum_sign_check {m : ℕ} (w : List (Vec m)) (b : Vec m) :
    (∑ x : Vec w.length, sign (dot b (check w x))) = (w.map (letter b)).prod := by
  simp_rw [dot_check, sign_sum]
  rw [← Fintype.prod_sum (fun (i : Fin w.length) (t : F) => sign (dot b (w.get i) * t))]
  simp_rw [sum_sign_mul]
  change (∏ i, letter b (w.get i)) = _
  rw [← List.prod_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map w (letter b)

lemma count_one_fourier {m : ℕ} (w : List (Vec m)) :
    count 1 w = (2 : ℚ)⁻¹ ^ m * (∑ b : Vec m, (w.map (letter b)).prod) - 1 := by
  classical
  rw [count_one]
  congr 1
  have hp : (2 : ℚ) ^ m ≠ 0 := by positivity
  have h (x : Vec w.length) :
      (if check w x = 0 then (1 : ℚ) else 0) =
        (2 : ℚ)⁻¹ ^ m * (∑ b : Vec m, sign (dot b (check w x))) := by
    rw [sum_sign_dot, inv_pow]
    split <;> simp [hp]
  simp_rw [h, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_sign_check]

def wordProd {A V : Type*} [Monoid V] (M : A → V) (w : List A) : V := (w.map M).prod

lemma wordProd_append {A V : Type*} [Monoid V] (M : A → V) (u v : List A) :
    wordProd M (u ++ v) = wordProd M u * wordProd M v := by
  simp [wordProd]

lemma wordProd_hom {A V V' : Type*} [Monoid V] [Monoid V'] (M : A → V)
    (f : V →* V') (w : List A) : wordProd (f ∘ M) w = f (wordProd M w) := by
  induction w with
  | nil => simp [wordProd]
  | cons a w ih =>
    change f (M a) * wordProd (f ∘ M) w = f (M a * wordProd M w)
    rw [ih, map_mul]

lemma fits_alg_exact {A B : Type*} [Ring B] [Algebra ℚ B] [FiniteDimensional ℚ B]
    (M : A → B) (L : B →ₗ[ℚ] ℚ) {k : ℕ} (hk : Module.finrank ℚ B = k)
    {g : List A → ℚ} {T : List A → Prop} (hL : ∀ w, T w → L (wordProd M w) = g w) :
    Fits g k T := by
  classical
  let b : Module.Basis (Fin k) ℚ B := (Module.finBasis ℚ B).reindex (finCongr hk)
  let mapM := Algebra.leftMulMatrix b
  let v : Fin k → ℚ := b.repr 1
  refine ⟨fun i => L (b i), v, mapM ∘ M, ?_⟩
  intro w hw
  let x := wordProd M w
  have hprod : (w.map (mapM ∘ M)).prod = mapM x := wordProd_hom M mapM.toMonoidHom w
  have hv (i : Fin k) : (∑ j, mapM x i j * v j) = b.repr x i := by
    simpa only [mul_one, mapM, v, Matrix.mulVec, dotProduct] using congrFun (Algebra.leftMulMatrix_mulVec_repr b x (1 : B)) i
  rw [hprod, ← hL w hw]
  change (∑ i : Fin k, ∑ j : Fin k, L (b i) * mapM x i j * v j) = L x
  simp_rw [mul_assoc, ← Finset.mul_sum, hv, mul_comm (L (b _)), ← smul_eq_mul]
  simp_rw [← L.map_smul]
  rw [← map_sum, b.sum_repr]

lemma fits_alg {A B : Type*} [Ring B] [Algebra ℚ B] [FiniteDimensional ℚ B]
    (M : A → B) (L : B →ₗ[ℚ] ℚ) {k : ℕ} (hk : Module.finrank ℚ B ≤ k)
    {g : List A → ℚ} {T : List A → Prop} (hL : ∀ w, T w → L (wordProd M w) = g w) :
    Fits g k T := by
  let C := Fin (k - Module.finrank ℚ B) → ℚ
  let M' : A → B × C := fun a => (M a, 0)
  let fst : B × C →* B := MonoidHom.fst B C
  have hcard : Module.finrank ℚ (B × C) = k := by
    simp [C, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Nat.add_sub_of_le hk]
  refine fits_alg_exact M' (L.comp (LinearMap.fst ℚ B C)) hcard ?_
  intro w hw
  change L (fst (wordProd M' w)) = g w
  rw [← wordProd_hom]
  exact hL w hw

noncomputable def rowEval {W : Type*} {k : ℕ} (v : W → Fin k → ℚ) :
    (Fin k → ℚ) →ₗ[ℚ] (W → ℚ) where
  toFun r w := ∑ i, r i * v w i
  map_add' x y := by
    funext w
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext w
    simp [mul_assoc, Finset.mul_sum]

lemma row_eval_append {A : Type*} {k : ℕ}
    (M : A → Matrix (Fin k) (Fin k) ℚ) (u v : Fin k → ℚ) (p q : List A) :
    (∑ i : Fin k, ∑ j : Fin k, u i * (wordProd M (p ++ q)) i j * v j) =
      ∑ h : Fin k, (∑ i : Fin k, u i * (wordProd M p) i h) *
        (∑ j : Fin k, (wordProd M q) h j * v j) := by
  rw [wordProd_append]
  calc
    _ = ∑ i : Fin k, ∑ j : Fin k, ∑ h : Fin k,
        (u i * (wordProd M p) i h) * ((wordProd M q) h j * v j) := by
      simp_rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = ∑ i : Fin k, ∑ h : Fin k, ∑ j : Fin k,
        (u i * (wordProd M p) i h) * ((wordProd M q) h j * v j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ h : Fin k, ∑ i : Fin k, ∑ j : Fin k,
        (u i * (wordProd M p) i h) * ((wordProd M q) h j * v j) := Finset.sum_comm
    _ = _ := by simp_rw [Finset.sum_mul, Finset.mul_sum]

lemma fits_lower {A V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {g : List A → ℚ} {k : ℕ} {T P : List A → Prop}
    (φ : List A → V) (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hP : ∀ p q, P p → P q → T (p ++ q))
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hspan : Submodule.span ℚ (Set.range (fun p : {w // P w} => φ p.val)) = ⊤)
    (hmatch : ∀ p q, P p → P q → g (p ++ q) = B (φ p) (φ q))
    (hfit : Fits g k T) : Module.finrank ℚ V ≤ k := by
  rcases hfit with ⟨u, v, M, hfit⟩
  let W := {w // P w}
  let pairing : V →ₗ[ℚ] (W → ℚ) := LinearMap.pi (fun q : W => B.flip (φ q.val))
  let row := rowEval (fun (q : W) i => ∑ j, (wordProd M q.val) i j * v j)
  have hpinj : Function.Injective pairing := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    change x = 0
    apply hB
    have hker : Submodule.span ℚ (Set.range (fun p : W => φ p.val)) ≤ LinearMap.ker (B x) := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact congrFun hx q
    intro y
    exact hker (by rw [hspan]; trivial)
  have hrange : LinearMap.range pairing ≤ LinearMap.range row := by
    have hle : Submodule.span ℚ (Set.range (fun p : W => φ p.val)) ≤
        (LinearMap.range row).comap pairing := by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      refine ⟨fun i => ∑ j, u j * (wordProd M p.val) j i, ?_⟩
      funext q
      change (∑ i : Fin k, (∑ j : Fin k, u j * (wordProd M p.val) j i) *
        (∑ j : Fin k, (wordProd M q.val) i j * v j)) = B (φ p.val) (φ q.val)
      rw [← hmatch _ _ p.property q.property, ← hfit _ (hP _ _ p.property q.property)]
      exact (row_eval_append M u v p.val q.val).symm
    rintro _ ⟨x, rfl⟩
    exact hle (by rw [hspan]; trivial)
  rw [← LinearMap.finrank_range_of_inj hpinj]
  exact (Submodule.finrank_mono hrange).trans
    ((LinearMap.finrank_range_le _).trans_eq (by simp [Module.finrank_fintype_fun_eq_card]))

noncomputable def productPair {B : Type*} [Ring B] [Algebra ℚ B]
    (L : B →ₗ[ℚ] ℚ) : B →ₗ[ℚ] B →ₗ[ℚ] ℚ where
  toFun x := L.comp (Algebra.lmul ℚ B x)
  map_add' x y := by
    ext z
    change L ((x + y) * z) = L (x*z) + L (y*z)
    rw [add_mul, map_add]
  map_smul' r x := by
    ext z
    change L ((r • x) * z) = r • L (x*z)
    rw [smul_mul_assoc, map_smul]

lemma pos_word_span {A V : Type*} [Ring V] [Algebra ℚ V] [FiniteDimensional ℚ V]
    (M : A → V) (a : A) (hu : IsUnit (M a))
    (hgen : Algebra.adjoin ℚ (Set.range M) = ⊤) :
    Submodule.span ℚ (Set.range (fun p : {w : List A // 0 < w.length} => wordProd M p.val)) = ⊤ := by
  let S := NonUnitalAlgebra.adjoin ℚ (Set.range M)
  have hS : S.toSubmodule =
      Submodule.span ℚ (Set.range (fun p : {w : List A // 0 < w.length} => wordProd M p.val)) := by
    rw [NonUnitalAlgebra.adjoin_eq_span]
    congr 1
    ext x
    constructor
    · intro hx
      induction hx using Subsemigroup.closure_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        exact ⟨⟨[b], by simp⟩, by simp [wordProd]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨p, rfl⟩ := hx
        obtain ⟨q, rfl⟩ := hy
        exact ⟨⟨p.val ++ q.val, by simp only [List.length_append]; omega⟩,
          wordProd_append M p.val q.val⟩
    · rintro ⟨⟨w, hw⟩, rfl⟩
      induction w with
      | nil => simp at hw
      | cons b w ih =>
        have hb := Subsemigroup.subset_closure (s := Set.range M) (Set.mem_range_self b)
        cases w with
        | nil => simpa [wordProd] using hb
        | cons c w =>
          change M b * wordProd M (c :: w) ∈ _
          exact mul_mem hb (ih (by simp))
  have ha : M a ∈ S := NonUnitalAlgebra.subset_adjoin ℚ (Set.mem_range_self a)
  let l : S.toSubmodule →ₗ[ℚ] S.toSubmodule :=
    ((Algebra.lmul ℚ V (M a)).domRestrict S.toSubmodule).codRestrict S.toSubmodule
      (fun x => S.mul_mem ha x.property)
  have hl : Function.Injective l := by
    intro x y h
    apply Subtype.ext
    apply hu.mul_right_injective
    exact congrArg Subtype.val h
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hl) ⟨M a, ha⟩
  have hx' : M a * x.val = M a := congrArg Subtype.val hx
  have h1 : 1 ∈ S := by
    have h := hu.mul_right_inj.mp (hx'.trans (mul_one (M a)).symm)
    exact h ▸ x.property
  let R : Subalgebra ℚ V :=
    { carrier := S, add_mem' := S.add_mem
      mul_mem' := S.mul_mem
      algebraMap_mem' := fun c => by
        simpa [Algebra.smul_def] using S.toSubmodule.smul_mem c h1 }
  have hle : Algebra.adjoin ℚ (Set.range M) ≤ R := Algebra.adjoin_le (fun _ hx =>
    NonUnitalAlgebra.subset_adjoin ℚ hx)
  rw [hgen, top_le_iff] at hle
  rw [← hS]
  exact congrArg Subalgebra.toSubmodule hle

lemma pi_adjoin {ι A : Type*} [Fintype ι] (M : A → ι → ℚ)
    (hsep : ∀ i j, i ≠ j → ∃ a, M a i ≠ M a j) :
    Algebra.adjoin ℚ (Set.range M) = ⊤ := by
  classical
  let S := Algebra.adjoin ℚ (Set.range M)
  have hδ (i : ι) : Pi.single i (1 : ℚ) ∈ S := by
    let a (j : ι) (h : i ≠ j) := (hsep i j h).choose
    let e (j : ι) : ι → ℚ :=
      if h : i ≠ j then (M (a j h) i - M (a j h) j)⁻¹ •
        (M (a j h) - algebraMap ℚ (ι → ℚ) (M (a j h) j)) else 1
    have he (j : ι) : e j ∈ S := by
      dsimp [e]
      split
      · exact S.smul_mem (S.sub_mem (Algebra.subset_adjoin (Set.mem_range_self _))
          (S.algebraMap_mem _)) _
      · exact S.one_mem
    have hprod : (∏ j, e j) ∈ S := S.prod_mem (fun j _ => he j)
    have he_i (j : ι) : e j i = 1 := by
      dsimp [e]
      split
      · rename_i h
        simpa only [Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self_apply,
          smul_eq_mul] using inv_mul_cancel₀ (sub_ne_zero.mpr (hsep i j h).choose_spec)
      · rfl
    have he_j (j : ι) (h : i ≠ j) : e j j = 0 := by
      simp only [e, dif_pos h, Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply,
        Algebra.algebraMap_self_apply, sub_self, smul_zero]
    have h : (∏ j, e j) = Pi.single i (1 : ℚ) := by
      ext j
      rw [Finset.prod_apply]
      by_cases hij : i = j
      · subst j
        simp [he_i]
      · have hz : (∏ k, e k j) = 0 :=
          Finset.prod_eq_zero (f := fun k => e k j) (Finset.mem_univ j) (he_j j hij)
        rw [hz, Pi.single_eq_of_ne (Ne.symm hij)]
    rwa [← h]
  apply top_unique
  intro x _
  have hx : x = ∑ i : ι, x i • Pi.single i (1 : ℚ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply, smul_ite]
  rw [hx]
  exact S.sum_mem fun i _ => S.smul_mem (hδ i) _

noncomputable def weighted {ι : Type*} [Fintype ι] (c : ι → ℚ) : (ι → ℚ) →ₗ[ℚ] ℚ :=
  ∑ i, c i • LinearMap.proj i

lemma weighted_apply {ι : Type*} [Fintype ι] (c f : ι → ℚ) : weighted c f = ∑ i, c i * f i := by
  simp [weighted]

lemma weighted_pair_nondeg {ι : Type*} [Fintype ι] (c : ι → ℚ) (hc : ∀ i, c i ≠ 0)
    (f : ι → ℚ) (h : ∀ g, productPair (weighted c) f g = 0) : f = 0 := by
  classical
  ext i
  have hi := h (Pi.single i 1)
  change weighted c (f * Pi.single i 1) = 0 at hi
  rw [weighted_apply, Finset.sum_eq_single i] at hi
  · simpa only [Pi.mul_apply, Pi.single_eq_same, mul_one, mul_eq_zero, hc i, false_or, Pi.zero_apply] using hi
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

def oneLetter {m : ℕ} (a : Vec m) (b : Option (Vec m)) : ℚ :=
  b.elim 1 (fun x => letter x a)

def oneWeight (m : ℕ) (b : Option (Vec m)) : ℚ := b.elim (-1) (fun _ => (2 : ℚ)⁻¹ ^ m)

lemma wordProd_pi_apply {ι A : Type*} (M : A → ι → ℚ) (w : List A) (i : ι) :
    wordProd M w i = wordProd (fun a => M a i) w :=
  (wordProd_hom M (Pi.evalMonoidHom _ i) w).symm

lemma count_one_weighted {m : ℕ} (w : List (Vec m)) :
    count 1 w = weighted (oneWeight m) (wordProd oneLetter w) := by
  rw [count_one_fourier, weighted_apply, Fintype.sum_option]
  simp_rw [wordProd_pi_apply]
  have h : wordProd (fun _ : Vec m => (1 : ℚ)) w = 1 := by simp [wordProd]
  simp only [oneWeight, oneLetter, Option.elim_none, Option.elim_some, h, mul_one]
  simp only [wordProd, ← Finset.mul_sum]
  ring

lemma dot_comm {m : ℕ} (a b : Vec m) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma oneLetter_sep {m : ℕ} (i j : Option (Vec m)) (h : i ≠ j) :
    ∃ a, oneLetter a i ≠ oneLetter a j := by
  cases i with
  | none =>
    cases j with
    | none => exact (h rfl).elim
    | some j => exact ⟨0, by norm_num [oneLetter, letter, dot, sign]⟩
  | some i =>
    cases j with
    | none => exact ⟨0, by norm_num [oneLetter, letter, dot, sign]⟩
    | some j =>
      have he : ∃ a, i a ≠ j a := by
        by_contra hn
        push Not at hn
        exact h (congrArg some (funext hn))
      obtain ⟨a, ha⟩ := he
      refine ⟨Pi.single a 1, ?_⟩
      simp only [oneLetter, Option.elim_some, letter, dot_comm i (Pi.single a 1),
        dot_comm j (Pi.single a 1), dot_single_left, ne_eq, add_right_inj]
      rcases two_cases (i a) with hi | hi <;> rcases two_cases (j a) with hj | hj <;>
        first | exact (ha (hi.trans hj.symm)).elim | norm_num [sign, hi, hj]

lemma solve_one (m k : ℕ) :
    (Fits (count (m := m) 1) k (fun w => 0 < w.length) ↔ 2^m+1 ≤ k) ∧
    (Fits (count (m := m) 1) k (fun _ => True) ↔ 2^m+1 ≤ k) := by
  let V := Option (Vec m) → ℚ
  let L : V →ₗ[ℚ] ℚ := weighted (oneWeight m)
  have hc : Module.finrank ℚ V = 2^m+1 := by
    simp [V, Module.finrank_fintype_fun_eq_card, card_vec]
  have hu : IsUnit (oneLetter (0 : Vec m)) := by
    rw [Pi.isUnit_iff]
    intro i
    cases i <;> simp [oneLetter, letter, dot, sign, isUnit_iff_ne_zero]
  have hs := pos_word_span oneLetter 0 hu (pi_adjoin oneLetter oneLetter_sep)
  have hn : ∀ x : V, (∀ y : V, productPair L x y = 0) → x = 0 :=
    weighted_pair_nondeg _ (by intro i; cases i <;> simp [oneWeight])
  have hm (p q : List (Vec m)) :
      count 1 (p ++ q) = productPair L (wordProd oneLetter p) (wordProd oneLetter q) := by
    rw [count_one_weighted, wordProd_append]
    rfl
  have hub : ∀ (P : List (Vec m) → Prop), 2^m+1 ≤ k → Fits (count 1) k P := by
    intro P hk
    apply fits_alg oneLetter L (hc ▸ hk)
    exact fun w _ => (count_one_weighted w).symm
  have hlb (P : List (Vec m) → Prop)
      (hP : ∀ p q : List (Vec m), 0 < p.length → 0 < q.length → P (p ++ q))
      (hfit : Fits (count 1) k P) : 2^m+1 ≤ k := by
    rw [← hc]
    exact fits_lower (wordProd oneLetter) (productPair L) hP hn hs (fun p q _ _ => hm p q) hfit
  exact ⟨⟨hlb _ (by intro p q hp hq; simp; omega), hub _⟩, ⟨hlb _ (by simp), hub _⟩⟩

lemma path_prod {A V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (M : A → Matrix V V R) (w : List A) (x y : V) :
    wordProd M w x y = ∑ f : Fin w.length → V,
      if Fin.cons (α := fun _ => V) x f (Fin.last w.length) = y then
        ∏ i : Fin w.length, M (w.get i) (Fin.cons (α := fun _ => V) x f i.castSucc) (f i)
      else 0 := by
  induction w generalizing x with
  | nil =>
    simp [wordProd, Matrix.one_apply]
  | cons a w ih =>
    change (M a * wordProd M w) x y = _
    rw [Matrix.mul_apply]
    simp_rw [ih]
    let e := Fin.consEquiv (fun _ : Fin (w.length+1) => V)
    let g (f : Fin (w.length+1) → V) : R :=
      if Fin.cons (α := fun _ => V) x f (Fin.last (w.length+1)) = y then
        ∏ i : Fin (w.length+1), M ((a :: w).get i) (Fin.cons (α := fun _ => V) x f i.castSucc) (f i)
      else 0
    change _ = ∑ f, g f
    rw [← e.sum_comp g, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    dsimp [e, g, Fin.consEquiv]
    simp only [Fin.prod_univ_succ, List.get_cons_zero, List.get_cons_succ,
      Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, Fin.castSucc_succ, Fin.cons_last]
    split <;> simp_all

lemma snoc_last_wrap {V : Type*} {n : ℕ} (hn : 0 < n)
    (f : Fin n → V) (i : Fin n) :
    Fin.snoc (α := fun _ => V) f (f ⟨0, hn⟩) i.succ = f (next i) := by
  by_cases hi : i.val + 1 < n
  · have he : i.succ = (⟨i.val+1, hi⟩ : Fin n).castSucc := Fin.ext rfl
    rw [he, Fin.snoc_castSucc]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hi).symm
  · have he : i.val + 1 = n := by omega
    rw [show i.succ = Fin.last n from Fin.ext he, Fin.snoc_last]
    congr 1
    exact Fin.ext (by simp [next, he])

lemma trace_cycle {A V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (M : A → Matrix V V R) (w : List A) (hw : 0 < w.length) :
    Matrix.trace (wordProd M w) =
      ∑ f : Fin w.length → V, ∏ i : Fin w.length, M (w.get i) (f i) (f (next i)) := by
  let n := w.length
  let g : (Fin (n+1) → V) → R := fun f =>
    if f (Fin.last n) = f 0 then
      ∏ i : Fin n, M (w.get i) (f i.castSucc) (f i.succ)
    else 0
  let ec := Fin.consEquiv (fun _ : Fin (n+1) => V)
  let es := Fin.snocEquiv (fun _ : Fin (n+1) => V)
  have h0 (f : Fin n → V) (z : V) :
      Fin.snoc (α := fun _ => V) f z (0 : Fin (n+1)) = f ⟨0, hw⟩ := by
    rw [show (0 : Fin (n+1)) = (⟨0, hw⟩ : Fin n).castSucc from Fin.ext rfl,
      Fin.snoc_castSucc]
  calc
    Matrix.trace (wordProd M w) = ∑ f, g f := by
      rw [← ec.sum_comp, Fintype.sum_prod_type]
      unfold Matrix.trace Matrix.diag
      apply Finset.sum_congr rfl
      intro x _
      rw [path_prod]
      apply Finset.sum_congr rfl
      intro f _
      simp [ec, g, n]
    _ = ∑ z : V, ∑ f : Fin n → V, g (Fin.snoc (α := fun _ => V) f z) := by
      rw [← es.sum_comp, Fintype.sum_prod_type]
      rfl
    _ = ∑ f : Fin n → V, ∏ i : Fin n, M (w.get i) (f i) (f (next i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      simp only [g, Fin.snoc_last, h0, Fin.snoc_castSucc]
      rw [Finset.sum_eq_single (f ⟨0, hw⟩)]
      · simp [snoc_last_wrap hw]
      · intro z _ hz
        simp [hz]
      · simp

def compatible {j : ℕ} (x y : Vec j) : Prop := x = 0 ∨ y = 0 ∨ x = y

lemma cross_compatible {j : ℕ} (x y : Vec j) :
    (∀ u v, dot x u * dot y v = dot y u * dot x v) ↔ compatible x y := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ : ∃ i : Fin j, x i ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hx (funext hn)
      have hi' : x i = 1 := (two_cases (x i)).resolve_left hi
      have he (a : Fin j) := h (Pi.single i 1) (Pi.single a 1)
      simp only [dot_comm x, dot_comm y, dot_single_left, hi', one_mul] at he
      rcases two_cases (y i) with h0 | h1
      · exact Or.inr (Or.inl (funext (fun a => by simpa [h0] using he a)))
      · exact Or.inr (Or.inr (funext (fun a => by simpa [h1] using (he a).symm)))
  · rintro (rfl | rfl | rfl) <;> simp [dot]

def rowMap {j n : ℕ} (f : Fin n → Vec j) : Vec j →ₗ[F] Vec n :=
  Matrix.toLin' (Matrix.of f)

lemma rowMap_apply {j n : ℕ} (f : Fin n → Vec j) (x : Vec j) (i : Fin n) :
    rowMap f x i = dot (f i) x := rfl

lemma rowMap_single {j n : ℕ} (f : Fin n → Vec j) (i : Fin j) :
    rowMap f (Pi.single i 1) = fun a => f a i := by
  ext a
  rw [rowMap_apply, dot_comm, dot_single_left]

lemma rowMap_good {m j : ℕ} (w : List (Vec m)) (f : Fin w.length → Vec j) :
    good w (LinearMap.range (rowMap f)) ↔
      (∀ r : Fin j, check w (fun i => f i r) = 0) ∧
      (∀ i : Fin w.length, compatible (f i) (f (next i))) := by
  constructor
  · intro h
    constructor
    · intro r
      have hm : (fun i => f i r) ∈ LinearMap.range (rowMap f) :=
        ⟨Pi.single r 1, rowMap_single f r⟩
      exact funext (h.1 _ hm)
    · intro i
      apply (cross_compatible _ _).mp
      intro u v
      exact h.2 _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ i
  · rintro ⟨hcheck, hedges⟩
    constructor
    · rintro _ ⟨u, rfl⟩ a
      simp only [rowMap_apply, dot, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro r _
      simp only [← mul_assoc, ← Finset.sum_mul]
      have hr := congrFun (hcheck r) a
      change (∑ i, w.get i a * f i r) = 0 at hr
      rw [hr, zero_mul]
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ i
      exact (cross_compatible _ _).mpr (hedges i) u v

noncomputable def bit (p : Prop) : ℚ := by
  classical
  exact if p then 1 else 0

lemma bit_and (p q : Prop) : bit (p ∧ q) = bit p * bit q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

lemma bit_forall {ι : Type*} [Fintype ι] (p : ι → Prop) :
    bit (∀ i, p i) = ∏ i, bit (p i) := by
  classical
  unfold bit
  rw [Fintype.prod_ite_zero]
  simp

lemma bit_eq_fourier {m : ℕ} (x : Vec m) :
    bit (x = 0) = (2 : ℚ)⁻¹ ^ m * ∑ b : Vec m, sign (dot b x) := by
  classical
  rw [sum_sign_dot, inv_pow]
  by_cases h : x = 0 <;> simp [bit, h, show (2 : ℚ) ^ m ≠ 0 by positivity]

def syndrome {m j : ℕ} (b : Fin j → Vec m) : Vec j →ₗ[F] Vec m :=
  rowMap (fun a r => b r a)

lemma dot_syndrome {m j : ℕ} (b : Fin j → Vec m) (a : Vec m) (x : Vec j) :
    dot a (syndrome b x) = ∑ r, dot (b r) a * x r := by
  simp only [syndrome, rowMap_apply, dot, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma tuple_fourier {m j : ℕ} (w : List (Vec m)) (f : Fin w.length → Vec j) :
    bit (∀ r : Fin j, check w (fun i => f i r) = 0) =
      ((2 : ℚ)⁻¹ ^ m)^j * ∑ b : Fin j → Vec m,
        ∏ i : Fin w.length, sign (dot (w.get i) (syndrome b (f i))) := by
  classical
  rw [bit_forall]
  simp_rw [bit_eq_fourier]
  rw [Finset.prod_mul_distrib, Fin.prod_const, Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [dot_check, dot_syndrome, sign_sum]
  exact Finset.prod_comm

noncomputable def transfer {m j : ℕ} (b : Fin j → Vec m) (a : Vec m) :
    Matrix (Vec j) (Vec j) ℚ :=
  fun x y => sign (dot a (syndrome b x)) * bit (compatible x y)

noncomputable def mapCount {m : ℕ} (j : ℕ) (w : List (Vec m)) : ℚ :=
  ∑ f : Fin w.length → Vec j, bit (good w (LinearMap.range (rowMap f)))

lemma mapCount_fourier {m : ℕ} (j : ℕ) (w : List (Vec m)) (hw : 0 < w.length) :
    mapCount j w = ((2 : ℚ)⁻¹ ^ m)^j * ∑ b : Fin j → Vec m,
      Matrix.trace (wordProd (transfer b) w) := by
  classical
  unfold mapCount
  simp_rw [rowMap_good, bit_and, tuple_fourier, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply congrArg
  apply Finset.sum_congr rfl
  intro b _
  rw [trace_cycle _ _ hw]
  apply Finset.sum_congr rfl
  intro f _
  simp only [transfer, Finset.prod_mul_distrib, bit_forall]

open Polynomial

noncomputable def weightPoly (d : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range d, (X - C ((2 : ℚ)^i))

lemma weightPoly_succ (d : ℕ) :
    weightPoly (d+1) = weightPoly d * (X - C ((2 : ℚ)^d)) := by
  simp [weightPoly, Finset.prod_range_succ]

lemma weightPoly_degree_monic (d : ℕ) :
    (weightPoly d).natDegree = d ∧ (weightPoly d).Monic := by
  induction d with
  | zero => simp [weightPoly]
  | succ d ih =>
    rw [weightPoly_succ]
    exact ⟨by rw [natDegree_mul ih.2.ne_zero (monic_X_sub_C _).ne_zero,
      ih.1, natDegree_X_sub_C], ih.2.mul (monic_X_sub_C _)⟩

lemma weightPoly_eval (d : ℕ) (x : ℚ) :
    (weightPoly d).eval x = ∏ i ∈ Finset.range d, (x - (2 : ℚ)^i) := by
  unfold weightPoly
  rw [eval_prod]
  simp

lemma weightPoly_root {d i : ℕ} (hi : i < d) : (weightPoly d).eval ((2 : ℚ)^i) = 0 := by
  rw [weightPoly_eval]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self _)

lemma weightPoly_top (d : ℕ) : 0 < (weightPoly d).eval ((2 : ℚ)^d) := by
  rw [weightPoly_eval]
  apply Finset.prod_pos
  intro i hi
  exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) (Finset.mem_range.mp hi))

lemma weightPoly_eval_sum (d : ℕ) (x : ℚ) :
    (weightPoly d).eval x =
      ∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j * x^j := by
  simpa only [(weightPoly_degree_monic d).1] using eval_eq_sum_range (p := weightPoly d) x

lemma weightPoly_orthogonal (d r : ℕ) :
    (∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j * (weightPoly r).eval ((2 : ℚ)^j)) =
      if r = d then (weightPoly d).eval ((2 : ℚ)^d) else 0 := by
  by_cases hr : r ≤ d
  · simp_rw [weightPoly_eval_sum r, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h (i : ℕ) :
        (∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j *
          ((weightPoly r).coeff i * ((2 : ℚ)^j)^i)) =
        (weightPoly r).coeff i * (weightPoly d).eval ((2 : ℚ)^i) := by
      rw [weightPoly_eval_sum d, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, mul_comm ((weightPoly d).coeff j), mul_assoc,
        ← pow_mul, ← pow_mul, Nat.mul_comm j i]
    simp_rw [h]
    by_cases he : r = d
    · subst r
      rw [if_pos rfl, Finset.sum_eq_single d]
      · have ht := (weightPoly_degree_monic d).2.coeff_natDegree
        rw [(weightPoly_degree_monic d).1] at ht
        rw [ht, one_mul]
      · intro i hi hne
        rw [weightPoly_root (by have := Finset.mem_range.mp hi; omega), mul_zero]
      · simp
    · rw [if_neg he, Finset.sum_eq_zero]
      intro i hi
      rw [weightPoly_root (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · rw [if_neg (by omega : r ≠ d), Finset.sum_eq_zero]
    intro j hj
    rw [weightPoly_root (by have := Finset.mem_range.mp hj; omega), mul_zero]

noncomputable def rowEquiv (j n : ℕ) : (Fin n → Vec j) ≃ (Vec j →ₗ[F] Vec n) :=
  ((Matrix.ofLinearEquiv F).trans Matrix.toLin').toEquiv

lemma rowEquiv_apply {j n : ℕ} (f : Fin n → Vec j) : rowEquiv j n f = rowMap f := rfl

lemma surj_rowMap {j n : ℕ} (f : Fin n → Vec j) :
    Function.Surjective (rowMap f) ↔ LinearIndependent F f := by
  change Function.Surjective (Matrix.of f).mulVec ↔ LinearIndependent F f
  rw [Matrix.mulVec_surjective_iff_rank_eq_card, Matrix.rank_eq_finrank_span_row]
  change (Module.finrank F (Submodule.span F (Set.range f)) = Fintype.card (Fin n)) ↔ _
  rw [eq_comm]
  exact (linearIndependent_iff_card_eq_finrank_span (R := F) (b := f)).symm

lemma card_surj {V : Type*} [AddCommGroup V] [Module F V] [Finite V] (j : ℕ) :
    (Nat.card {f : Vec j →ₗ[F] V // Function.Surjective f} : ℚ) =
      (weightPoly (Module.finrank F V)).eval ((2 : ℚ)^j) := by
  classical
  let r := Module.finrank F V
  haveI : Module.Finite F V := Module.Finite.of_finite
  by_cases hr : r ≤ j
  · let b : V ≃ₗ[F] Vec r := (Module.finBasis F V).equivFun
    let e' : (Vec j →ₗ[F] V) ≃ (Fin r → Vec j) :=
      ((LinearEquiv.refl F (Vec j)).arrowCongr b).toEquiv.trans (rowEquiv j r).symm
    have he (f : Vec j →ₗ[F] V) :
        Function.Surjective f ↔ LinearIndependent F (e' f) := by
      rw [← surj_rowMap, ← rowEquiv_apply]
      have he' : rowEquiv j r (e' f) = b.toLinearMap.comp f := by
        simp [e']
        rfl
      rw [he']
      change Function.Surjective f ↔ Function.Surjective (b ∘ f)
      exact ⟨fun h => b.surjective.comp h, fun h y =>
        let ⟨x, hx⟩ := h (b y)
        ⟨x, b.injective hx⟩⟩
    let e'' : {f : Vec j →ₗ[F] V // Function.Surjective f} ≃
        {g : Fin r → Vec j // LinearIndependent F g} :=
      @Equiv.subtypeEquiv _ _ (fun f : Vec j →ₗ[F] V => Function.Surjective f)
        (fun g : Fin r → Vec j => LinearIndependent F g) e' he
    rw [Nat.card_congr e'',
      card_linearIndependent (K := F) (V := Vec j) (by simpa [Module.finrank_fintype_fun_eq_card] using hr),
      Nat.cast_prod, weightPoly_eval, ← Fin.prod_univ_eq_prod_range]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ZMod.card]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide : 0 < 2)
      ((Fin.isLt i).le.trans hr)), Nat.cast_pow, Nat.cast_pow]
    norm_num
  · haveI : IsEmpty {f : Vec j →ₗ[F] V // Function.Surjective f} := ⟨fun f => by
      have h := LinearMap.finrank_le_finrank_of_surjective f.property
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      exact hr h⟩
    letI : Fintype {f : Vec j →ₗ[F] V // Function.Surjective f} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, Nat.cast_zero, weightPoly_root (by omega : j < r)]

lemma card_row_range {n : ℕ} (j : ℕ) (U : Submodule F (Vec n)) :
    (Nat.card {f : Fin n → Vec j // LinearMap.range (rowMap f) = U} : ℚ) =
      (weightPoly (Module.finrank F U)).eval ((2 : ℚ)^j) := by
  classical
  let g (f : Vec j →ₗ[F] U) : Fin n → Vec j :=
    (rowEquiv j n).symm (U.subtype.comp f)
  have hg (f : Vec j →ₗ[F] U) : rowMap (g f) = U.subtype.comp f :=
    (rowEquiv j n).apply_symm_apply _
  let lift : {f : Vec j →ₗ[F] U // Function.Surjective f} →
      {f : Fin n → Vec j // LinearMap.range (rowMap f) = U} := fun f =>
    ⟨g f.val, by
      rw [hg, LinearMap.range_comp_of_range_eq_top U.subtype
        (LinearMap.range_eq_top.mpr f.property), Submodule.range_subtype]⟩
  have hl : Function.Bijective lift := by
    constructor
    · intro f h he
      have he' : U.subtype.comp f.val = U.subtype.comp h.val := by
        rw [← hg, ← hg]
        exact congrArg rowMap (congrArg Subtype.val he)
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun he' x
    · rintro ⟨f, hf⟩
      let p : Vec j →ₗ[F] U := (rowMap f).codRestrict U
        (fun x => hf ▸ LinearMap.mem_range_self (rowMap f) x)
      have hp : Function.Surjective p := by
        intro y
        obtain ⟨x, hx⟩ : y.val ∈ LinearMap.range (rowMap f) := hf.symm ▸ y.property
        exact ⟨x, Subtype.ext hx⟩
      refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
      change g p = f
      apply (rowEquiv j n).injective
      change rowMap (g p) = rowMap f
      rw [hg]
      rfl
  rw [← Nat.card_congr (Equiv.ofBijective lift hl), card_surj]

lemma mapCount_grouped {m : ℕ} (j : ℕ) (w : List (Vec m)) :
    letI : Fintype (Submodule F (Vec w.length)) := Fintype.ofFinite _
    mapCount j w =
      ∑ U : Submodule F (Vec w.length), bit (good w U) *
        (weightPoly (Module.finrank F U)).eval ((2 : ℚ)^j) := by
  classical
  letI : Fintype (Submodule F (Vec w.length)) := Fintype.ofFinite _
  unfold mapCount
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Fin w.length → Vec j))
    (fun f => LinearMap.range (rowMap f)) (fun U => bit (good w U))]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm, ← card_row_range]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma count_extract {m : ℕ} (d : ℕ) (w : List (Vec m)) :
    (∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j * mapCount j w) =
      (weightPoly d).eval ((2 : ℚ)^d) * count d w := by
  classical
  letI : Fintype (Submodule F (Vec w.length)) := Fintype.ofFinite _
  have h₁ (j : ℕ) := mapCount_grouped j w
  simp_rw [h₁, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h₂ (U : Submodule F (Vec w.length)) :
      (∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j *
        (bit (good w U) * (weightPoly (Module.finrank F U)).eval ((2 : ℚ)^j))) =
      bit (good w U) *
        (∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j *
          (weightPoly (Module.finrank F U)).eval ((2 : ℚ)^j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h₂, weightPoly_orthogonal]
  have h₃ (U : Submodule F (Vec w.length)) :
      bit (good w U) *
        (if Module.finrank F U = d then (weightPoly d).eval ((2 : ℚ)^d) else 0) =
      (weightPoly d).eval ((2 : ℚ)^d) * bit (Module.finrank F U = d ∧ good w U) := by
    rw [bit_and]
    by_cases h : Module.finrank F U = d <;> simp [h, bit, mul_comm]
  simp_rw [h₃, ← Finset.mul_sum]
  unfold count bit
  congr 1
  let P (U : Submodule F (Vec w.length)) := Module.finrank F U = d ∧ good w U
  letI : DecidablePred P := fun p => Classical.propDecidable (P p)
  exact Finset.sum_boole (R := ℚ) P Finset.univ

lemma mapCount_nil {m : ℕ} (j : ℕ) : mapCount j ([] : List (Vec m)) = 1 := by
  classical
  unfold mapCount
  simp_rw [rowMap_good]
  have hx (f : Fin ([] : List (Vec m)).length → Vec j) :
      ∀ r : Fin j, check ([] : List (Vec m)) (fun i => f i r) = 0 := by
    intro r
    funext a
    simp [check]
  have h (f : Fin ([] : List (Vec m)).length → Vec j) : bit
      ((∀ r : Fin j, check ([] : List (Vec m)) (fun i => f i r) = 0) ∧
        (∀ i, compatible (f i) (f (next i)))) = 1 := by
    unfold bit
    exact if_pos ⟨hx f, fun i => Fin.elim0 i⟩
  simp_rw [h]
  simp

lemma count_empty {m d : ℕ} (hd : 0 < d) : count (m := m) d [] = 0 := by
  have h := count_extract d ([] : List (Vec m))
  simp_rw [mapCount_nil, mul_one] at h
  have h' := weightPoly_eval_sum d 1
  simp only [one_pow, mul_one] at h'
  rw [← h', show (1 : ℚ) = 2^0 by simp, weightPoly_root hd] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (weightPoly_top d).ne'

lemma wordProd_intertwine {A X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C]
    (D : A → Matrix X X ℚ) (E : A → Matrix C C ℚ) (J : Matrix X C ℚ)
    (h : ∀ a, D a * J = J * E a) (w : List A) :
    wordProd D w * J = J * wordProd E w := by
  induction w with
  | nil => simp [wordProd]
  | cons a w ih =>
    change (D a * wordProd D w) * J = J * (E a * wordProd E w)
    rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h a, Matrix.mul_assoc]

lemma compressed_trace {A X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C]
    (D : A → Matrix X X ℚ) (D' : A → Matrix C C ℚ)
    (J : Matrix X C ℚ) (K : Matrix C X ℚ) (E : Matrix C C ℚ)
    (hKJ : K * J = 1) (hJ : ∀ a, D a * J = J * D' a) (hK : ∀ a, D' a * K = K * D a)
    (w : List A) :
    Matrix.trace (wordProd (fun a => D a * (1 + J * E * K)) w) =
    Matrix.trace (wordProd (fun a => D' a * (1 + E)) w) +
      Matrix.trace (wordProd D w) - Matrix.trace (wordProd D' w) := by
  let M : A → Matrix X X ℚ := fun a => D a * (1 + J * E * K)
  let N : A → Matrix C C ℚ := fun a => D' a * (1 + E)
  let P := J * K
  have hE (a : A) : M a * J = J * N a := by
    simp only [M, N, Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul, hKJ, Matrix.mul_one]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hJ a, ← Matrix.mul_assoc,
      Matrix.mul_add, Matrix.mul_one]
  have hz : K * (1 - P) = 0 := by
    simp [P, Matrix.mul_sub, ← Matrix.mul_assoc, hKJ]
  have hmix (u : List A) : wordProd M u * (1 - P) = wordProd D u * (1 - P) := by
    induction u with
    | nil => rfl
    | cons a u ih =>
      change (M a * wordProd M u) * (1 - P) = (D a * wordProd D u) * (1 - P)
      simp only [Matrix.mul_assoc, ih]
      have hk := wordProd_intertwine D' D K hK u
      have hzero : K * (wordProd D u * (1 - P)) = 0 := by
        rw [← Matrix.mul_assoc, ← hk, Matrix.mul_assoc, hz, Matrix.mul_zero]
      simp [M, Matrix.add_mul, Matrix.mul_assoc, hzero]
  have htr (B : Matrix C C ℚ) : Matrix.trace (J * B * K) = Matrix.trace B := by
    rw [Matrix.trace_mul_cycle, hKJ, Matrix.one_mul]
  have hf : wordProd M w = J * wordProd N w * K + wordProd D w - J * wordProd D' w * K := by
    calc
      wordProd M w = wordProd M w * P + wordProd M w * (1-P) := by
        rw [← Matrix.mul_add]
        simp
      _ = J * wordProd N w * K + (wordProd D w - J * wordProd D' w * K) := by
        rw [hmix, Matrix.mul_sub, Matrix.mul_one]
        simp only [P, ← Matrix.mul_assoc, wordProd_intertwine _ _ _ hE,
          wordProd_intertwine _ _ _ hJ]
      _ = _ := by abel
  change Matrix.trace (wordProd M w) = Matrix.trace (wordProd N w) +
    Matrix.trace (wordProd D w) - Matrix.trace (wordProd D' w)
  rw [hf, Matrix.trace_sub, Matrix.trace_add, htr, htr]

noncomputable def fibreSize {X C : Type*} [Fintype X] (π : X → C) (c : C) : ℚ :=
  ∑ x, bit (π x = c)

noncomputable def inclusionMatrix {X C : Type*} (π : X → C) : Matrix X C ℚ :=
  fun x c => bit (π x = c)

noncomputable def averageMatrix {X C : Type*} [Fintype X] (π : X → C) : Matrix C X ℚ := by
  classical
  exact fun c x => if π x = c then (fibreSize π c)⁻¹ else 0

lemma inclusion_apply {X C Y : Type*} [Fintype C]
    (π : X → C) (B : Matrix C Y ℚ) (x : X) (y : Y) :
    (inclusionMatrix π * B) x y = B (π x) y := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (π x)]
  · simp [inclusionMatrix, bit]
  · intro c _ hc
    simp [inclusionMatrix, bit, Ne.symm hc]
  · simp

lemma average_apply {X C Y : Type*} [Fintype X] [Fintype C]
    (π : X → C) (B : Matrix Y C ℚ) (y : Y) (x : X) :
    (B * averageMatrix π) y x = B y (π x) * (fibreSize π (π x))⁻¹ := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (π x)]
  · simp [averageMatrix]
  · intro c _ hc
    simp [averageMatrix, Ne.symm hc]
  · simp

lemma fibreSize_pos {X C : Type*} [Fintype X] (π : X → C)
    (hπ : Function.Surjective π) (c : C) : 0 < fibreSize π c := by
  classical
  obtain ⟨x, hx⟩ := hπ c
  have h₁ : bit (π x = c) = 1 := by simp [bit, hx]
  have h₂ : ∀ y : X, 0 ≤ bit (π y = c) := by intro y; unfold bit; split <;> norm_num
  rw [fibreSize]
  have hle := Finset.single_le_sum (fun (y : X) _ => h₂ y) (Finset.mem_univ x)
  rw [h₁] at hle
  positivity

lemma average_inclusion {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (π : X → C) (hπ : Function.Surjective π) :
    averageMatrix π * inclusionMatrix π = 1 := by
  classical
  ext c d
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases h : c = d
  · subst d
    have h' (x : X) : averageMatrix π c x * inclusionMatrix π x c =
        bit (π x = c) * (fibreSize π c)⁻¹ := by
      by_cases hx : π x = c <;> simp [averageMatrix, inclusionMatrix, bit, hx]
    simp_rw [h', ← Finset.sum_mul]
    change fibreSize π c * (fibreSize π c)⁻¹ = 1
    exact mul_inv_cancel₀ (fibreSize_pos π hπ c).ne'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : π x = c
    · simp [averageMatrix, inclusionMatrix, bit, hx, h]
    · simp [averageMatrix, hx]

lemma inclusion_diagonal {X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C] (π : X → C) (f : C → ℚ) :
    Matrix.diagonal (f ∘ π) * inclusionMatrix π = inclusionMatrix π * Matrix.diagonal f := by
  ext x c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : π x = c <;> simp [inclusionMatrix, bit, hx]

lemma average_diagonal {X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C] (π : X → C) (f : C → ℚ) :
    Matrix.diagonal f * averageMatrix π = averageMatrix π * Matrix.diagonal (f ∘ π) := by
  ext c x
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : π x = c <;> simp [averageMatrix, hx, mul_comm]

def starEdges {C : Type*} (s : C → ℚ) : Matrix (Option C) (Option C) ℚ :=
  fun x y => match x, y with
    | none, some b => s b
    | some _, none => 1
    | _, _ => 0

lemma centre_fibreSize {X C : Type*} [Fintype X] (z : X) (π : X → Option C)
    (h : ∀ x, π x = none ↔ x = z) :
    fibreSize π none = 1 := by
  classical
  unfold fibreSize
  simp_rw [h, bit]
  simp

lemma compression_edges {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C]
    (z : X) (π : X → Option C) (hsurj : Function.Surjective π)
    (h : ∀ x, π x = none ↔ x = z) :
    Matrix.of (fun x y => bit (x = z ∨ y = z ∨ x = y)) =
      (1 : Matrix X X ℚ) + inclusionMatrix π * starEdges (fun c => fibreSize π (some c)) * averageMatrix π := by
  classical
  ext x y
  rw [Matrix.add_apply, average_apply, inclusion_apply, Matrix.one_apply]
  have hz := centre_fibreSize z π h
  have hs (c : C) : fibreSize π (some c) ≠ 0 := (fibreSize_pos π hsurj _).ne'
  generalize hx : π x = xi
  generalize hy : π y = yi
  cases xi with
  | none =>
    have hx' := (h x).mp hx
    cases yi with
    | none => simp [bit, hx', (h y).mp hy, starEdges, hz]
    | some c =>
      have hy' : y ≠ z := fun hy' => by simpa [hy] using (h y).mpr hy'
      simp [bit, hx', hy', Ne.symm hy', starEdges, hs]
  | some c =>
    have hx' : x ≠ z := fun hx' => by simpa [hx] using (h x).mpr hx'
    cases yi with
    | none => simp [bit, (h y).mp hy, hx', starEdges, hz]
    | some b =>
      have hy' : y ≠ z := fun hy' => by simpa [hy] using (h y).mpr hy'
      by_cases hxy : x = y <;> simp [bit, hx', hy', hxy, starEdges]

lemma trace_diag_words {A X : Type*} [Fintype X] [DecidableEq X]
    (f : A → X → ℚ) (w : List A) :
    Matrix.trace (wordProd (fun a => Matrix.diagonal (f a)) w) =
    ∑ x : X, wordProd (fun a => f a x) w := by
  let D : (X → ℚ) →ₐ[ℚ] Matrix X X ℚ := Matrix.diagonalAlgHom ℚ
  have he := wordProd_hom f D.toMonoidHom w
  change Matrix.trace (wordProd (D ∘ f) w) = _
  change wordProd (D ∘ f) w = D (wordProd f w) at he
  rw [he]
  simp [D, Matrix.trace, Matrix.diag, wordProd_pi_apply]

lemma compressed_words {A X C : Type*} [Fintype X] [DecidableEq X]
    [Fintype C] [DecidableEq C] (z : X) (π : X → Option C)
    (hsurj : Function.Surjective π) (h : ∀ x, π x = none ↔ x = z)
    (f : A → Option C → ℚ) (w : List A) :
    Matrix.trace (wordProd (fun a => Matrix.of (fun x y =>
      f a (π x) * bit (x = z ∨ y = z ∨ x = y))) w) =
      Matrix.trace (wordProd (fun a => Matrix.diagonal (f a) *
        (1 + starEdges (fun c => fibreSize π (some c)))) w) +
      ∑ x : X, wordProd (fun a => f a (π x)) w -
      ∑ c : Option C, wordProd (fun a => f a c) w := by
  change _ = _ + (∑ x : X, wordProd (fun a => (f a ∘ π) x) w) -
    (∑ c : Option C, wordProd (fun a => f a c) w)
  rw [← trace_diag_words (fun a => f a ∘ π) w, ← trace_diag_words f w]
  have he (a : A) : Matrix.of (fun x y => f a (π x) * bit (x = z ∨ y = z ∨ x = y)) =
      Matrix.diagonal (f a ∘ π) *
        (1 + inclusionMatrix π * starEdges (fun c => fibreSize π (some c)) * averageMatrix π) := by
    rw [← compression_edges z π hsurj h]
    ext x y
    rw [Matrix.diagonal_mul]
    rfl
  simp_rw [he]
  apply compressed_trace _ _ _ _ _ (average_inclusion π hsurj)
    (fun a => inclusion_diagonal π (f a)) (fun a => average_diagonal π (f a))

abbrev Labels {m : ℕ} (j : ℕ) (H : Submodule F (Vec m)) :=
  {b : Vec m // b ∈ H ∧ (b ≠ 0 ∨ Module.finrank F H < j)}

noncomputable def labelsFintype {m : ℕ} (j : ℕ) (H : Submodule F (Vec m)) :
    Fintype (Labels j H) := Fintype.ofFinite _

def cellLabel {m j : ℕ} {H : Submodule F (Vec m)} (i : Option (Labels j H)) : Vec m :=
  i.elim 0 Subtype.val

lemma rank_ker_sum {m j : ℕ} (S : Vec j →ₗ[F] Vec m) :
    Module.finrank F S.range + Module.finrank F S.ker = j := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    S.finrank_range_add_finrank_ker

lemma rank_range_le {m j : ℕ} (S : Vec j →ₗ[F] Vec m) : Module.finrank F S.range ≤ j := by
  have h := rank_ker_sum S
  omega

lemma exists_ker_nonzero {m j : ℕ} (S : Vec j →ₗ[F] Vec m)
    (h : Module.finrank F S.range < j) : ∃ x ∈ S.ker, x ≠ 0 := by
  apply (S.ker.ne_bot_iff).mp
  intro he
  have h' := rank_ker_sum S
  rw [he, finrank_bot, add_zero] at h'
  omega

noncomputable def cellOf {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (x : Vec j) :
    Option (Labels j S.range) :=
  if hx : x = 0 then none else some ⟨S x, LinearMap.mem_range_self S x, by
    by_cases hs : S x = 0
    · right
      have h : S.ker ≠ ⊥ := (S.ker.ne_bot_iff).mpr ⟨x, hs, hx⟩
      have h' : Module.finrank F S.ker ≠ 0 := fun hr => h (Submodule.finrank_eq_zero.mp hr)
      have he := rank_ker_sum S
      omega
    · exact Or.inl hs⟩

lemma cellOf_none {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (x : Vec j) :
    cellOf S x = none ↔ x = 0 := by
  by_cases hx : x = 0 <;> simp [cellOf, hx]

lemma cellOf_label {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (x : Vec j) :
    cellLabel (cellOf S x) = S x := by
  by_cases hx : x = 0 <;> simp [cellOf, cellLabel, hx]

lemma cellOf_some {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (x : Vec j)
    (c : Labels j S.range) :
    cellOf S x = some c ↔ x ≠ 0 ∧ S x = c.val := by
  by_cases hx : x = 0 <;> simp [cellOf, hx, Subtype.ext_iff]

lemma cellOf_surj {m j : ℕ} (S : Vec j →ₗ[F] Vec m) : Function.Surjective (cellOf S) := by
  intro c
  cases c with
  | none => exact ⟨0, (cellOf_none S 0).mpr rfl⟩
  | some c =>
    apply Exists.imp (fun x h => (cellOf_some S x c).mpr h)
    rcases c.property.2 with hc | hc
    · obtain ⟨x, hx⟩ := c.property.1
      exact ⟨x, fun he => hc (by simpa [he] using hx.symm), hx⟩
    · by_cases he : c.val = 0
      · obtain ⟨x, hx, hx0⟩ := exists_ker_nonzero S hc
        exact ⟨x, hx0, hx.trans he.symm⟩
      · obtain ⟨x, hx⟩ := c.property.1
        exact ⟨x, fun h => he (by simpa [h] using hx.symm), hx⟩

lemma fibreSize_eq_card {X C : Type*} [Fintype X] (π : X → C) (c : C) :
    fibreSize π c = (Nat.card {x : X // π x = c} : ℚ) := by
  classical
  unfold fibreSize bit
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

noncomputable def linearFibreEquiv {U V : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] (S : U →ₗ[F] V) (b : V) (hb : b ∈ S.range) :
    {x : U // S x = b} ≃ S.ker :=
  let x := hb.choose
  let hx := hb.choose_spec
  { toFun := fun y => ⟨y.val - x, by
      change S (y.val - x) = 0
      rw [map_sub, hx, y.property, sub_self]⟩
    invFun := fun z => ⟨z.val + x, by rw [map_add, z.property, hx, zero_add]⟩
    left_inv := fun y => Subtype.ext (sub_add_cancel _ _)
    right_inv := fun z => Subtype.ext (add_sub_cancel_right _ _) }

lemma fibreSize_linear {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (b : Vec m) (hb : b ∈ S.range) :
    fibreSize S b = (2 : ℚ)^(j - Module.finrank F S.range) := by
  classical
  let r := Module.finrank F S.ker
  have h : r = j - Module.finrank F S.range := by have := rank_ker_sum S; omega
  rw [fibreSize_eq_card, Nat.card_congr (linearFibreEquiv S b hb),
    Nat.card_congr (Module.finBasis F S.ker).equivFun.toEquiv, Nat.card_eq_fintype_card, card_vec]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using congrArg (fun k => (2 : ℚ)^k) h

noncomputable def labelSize {m : ℕ} (j : ℕ) (H : Submodule F (Vec m))
    (c : Labels j H) : ℚ := (2 : ℚ)^(j - Module.finrank F H) - bit (c.val = 0)

lemma fibreSize_cellOf {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (c : Labels j S.range) :
    fibreSize (cellOf S) (some c) = labelSize j S.range c := by
  have h (x : Vec j) : bit (cellOf S x = some c) =
      bit (S x = c.val) - bit (x = 0) * bit (c.val = 0) := by
    rw [cellOf_some]
    by_cases hx : x = 0
    · subst x
      by_cases hc : c.val = 0 <;> simp [bit, hc, eq_comm]
    · simp [bit_and, bit, hx]
  have h0 : (∑ x : Vec j, bit (x = 0)) = 1 := by
    classical
    unfold bit
    rw [Finset.sum_eq_single (0 : Vec j)]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  unfold labelSize
  rw [fibreSize]
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.sum_mul, h0, one_mul]
  exact congrArg (fun t => t - bit (c.val = 0)) (fibreSize_linear S c.val c.property.1)

def phase {m : ℕ} (b a : Vec m) : ℚ := sign (dot a b)

noncomputable def condensed {m : ℕ} (j : ℕ) (H : Submodule F (Vec m)) (a : Vec m) :
    Matrix (Option (Labels j H)) (Option (Labels j H)) ℚ :=
  letI := labelsFintype j H
  Matrix.diagonal (fun c => phase (cellLabel c) a) * (1 + starEdges (labelSize j H))

lemma transfer_condensed {m j : ℕ} (b : Fin j → Vec m) (w : List (Vec m)) :
    let H := (syndrome b).range
    letI := labelsFintype j H
    Matrix.trace (wordProd (transfer b) w) =
      Matrix.trace (wordProd (condensed j H) w) +
        ∑ x : Vec j, wordProd (phase (syndrome b x)) w -
          ∑ c : Option (Labels j H), wordProd (phase (cellLabel c)) w := by
  let S := syndrome b
  letI := labelsFintype j S.range
  have h := compressed_words (0 : Vec j) (cellOf S) (cellOf_surj S) (cellOf_none S)
    (fun a c => phase (cellLabel c) a) w
  simp_rw [cellOf_label, fibreSize_cellOf] at h
  exact h

lemma sum_fibreSize {X C : Type*} [Fintype X] [Fintype C] (π : X → C) :
    (∑ c, fibreSize π c) = (Fintype.card X : ℚ) := by
  classical
  simp_rw [fibreSize]
  rw [Finset.sum_comm]
  simp [bit]

lemma sum_labelSize_range {m j : ℕ} (S : Vec j →ₗ[F] Vec m) :
    letI := labelsFintype j S.range
    (∑ c, labelSize j S.range c) = (2 : ℚ)^j - 1 := by
  letI := labelsFintype j S.range
  have h := sum_fibreSize (cellOf S)
  rw [Fintype.sum_option, centre_fibreSize 0 (cellOf S) (cellOf_none S), card_vec] at h
  simp_rw [fibreSize_cellOf] at h
  push_cast at h
  linarith

def transposeEquiv (m j : ℕ) : (Fin j → Vec m) ≃ (Fin m → Vec j) :=
  ⟨fun x a r => x r a, fun x a r => x r a, fun _ => rfl, fun _ => rfl⟩

lemma exists_range {m j : ℕ} (H : Submodule F (Vec m)) (hj : Module.finrank F H ≤ j) :
    ∃ S : Vec j →ₗ[F] Vec m, S.range = H := by
  have hp : 0 < (weightPoly (Module.finrank F H)).eval ((2 : ℚ)^j) := by
    rw [weightPoly_eval]
    apply Finset.prod_pos
    intro i hi
    exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) ((Finset.mem_range.mp hi).trans_le hj))
  rw [← card_row_range j H] at hp
  have hpos : 0 < Nat.card {f : Fin m → Vec j // LinearMap.range (rowMap f) = H} := by exact_mod_cast hp
  have hn := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨⟨f, hf⟩⟩ := hn
  exact ⟨rowMap f, hf⟩

lemma labelSize_pos {m j : ℕ} (H : Submodule F (Vec m)) (hj : Module.finrank F H ≤ j)
    (c : Labels j H) : 0 < labelSize j H c := by
  obtain ⟨S, rfl⟩ := exists_range H hj
  rw [← fibreSize_cellOf]
  exact fibreSize_pos (cellOf S) (cellOf_surj S) _

lemma sum_labelSize {m j : ℕ} (H : Submodule F (Vec m)) (hj : Module.finrank F H ≤ j) :
    letI := labelsFintype j H
    (∑ c, labelSize j H c) = (2 : ℚ)^j - 1 := by
  obtain ⟨S, rfl⟩ := exists_range H hj
  exact sum_labelSize_range S

lemma card_submodule {m : ℕ} (H : Submodule F (Vec m)) :
    Nat.card H = 2^(Module.finrank F H) := by
  rw [Nat.card_congr (Module.finBasis F H).equivFun.toEquiv, Nat.card_eq_fintype_card, card_vec]

lemma card_labels {m j : ℕ} (H : Submodule F (Vec m)) (hj : Module.finrank F H ≤ j) :
    letI := labelsFintype j H
    Fintype.card (Option (Labels j H)) =
      2^(Module.finrank F H) + (if Module.finrank F H = j then 0 else 1) := by
  classical
  letI := labelsFintype j H
  have h1 : Fintype.card (Option (Labels j H)) = Nat.card (Labels j H) + 1 := by
    rw [Fintype.card_option, Nat.card_eq_fintype_card]
  rw [h1]
  by_cases he : Module.finrank F H = j
  · have hn : ¬Module.finrank F H < j := by omega
    have e : Labels j H ≃ {x : H // x ≠ 0} :=
      { toFun := fun x => ⟨⟨x.val, x.property.1⟩, fun hx =>
          (x.property.2.resolve_right hn) (congrArg Subtype.val hx)⟩
        invFun := fun x => ⟨x.val.val, x.val.property,
          Or.inl (fun hx => x.property (Subtype.ext hx))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    letI : Fintype H := Fintype.ofFinite _
    have h := Fintype.card_subtype_compl (fun x : H => x = 0)
    rw [Fintype.card_subtype_eq] at h
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, h, ← Nat.card_eq_fintype_card,
      card_submodule, if_pos he, add_zero]
    have : 0 < (2 : ℕ)^(Module.finrank F H) := by positivity
    omega
  · have hlt : Module.finrank F H < j := by omega
    have e : Labels j H ≃ H :=
      { toFun := fun x => ⟨x.val, x.property.1⟩
        invFun := fun x => ⟨x.val, x.property, Or.inr hlt⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, card_submodule, if_neg he]

lemma mapCount_zero {m : ℕ} (w : List (Vec m)) : mapCount 0 w = 1 := by
  classical
  unfold mapCount
  simp_rw [rowMap_good]
  have h (f : Fin w.length → Vec 0) : ∀ i, compatible (f i) (f (next i)) :=
    fun i => Or.inl (Subsingleton.elim _ _)
  simp [h, bit]

lemma compatible_one (x y : Vec 1) : compatible x y := by
  rcases two_cases (x 0) with hx | hx <;> rcases two_cases (y 0) with hy | hy
  · exact Or.inl (funext (fun i => by simpa only [Subsingleton.elim i 0, Pi.zero_apply] using hx))
  · exact Or.inl (funext (fun i => by simpa only [Subsingleton.elim i 0, Pi.zero_apply] using hx))
  · exact Or.inr (Or.inl (funext (fun i => by simpa only [Subsingleton.elim i 0, Pi.zero_apply] using hy)))
  · exact Or.inr (Or.inr (funext (fun i => by simpa only [Subsingleton.elim i 0, Pi.zero_apply] using hx.trans hy.symm)))

lemma mapCount_one {m : ℕ} (w : List (Vec m)) :
    mapCount 1 w = (2 : ℚ)⁻¹ ^ m * (∑ b : Vec m, wordProd (letter b) w) := by
  classical
  let e : Vec w.length ≃ (Fin w.length → Vec 1) :=
    { toFun := fun x i _ => x i
      invFun := fun x i => x i 0
      left_inv := fun _ => rfl
      right_inv := fun x => funext fun i => funext fun k => congrArg (x i) (Subsingleton.elim 0 k) }
  unfold mapCount
  rw [← e.sum_comp]
  simp_rw [rowMap_good, compatible_one, implies_true, and_true]
  have h (x : Vec w.length) :
      (∀ (r : Fin 1), check w (fun i => e x i r) = 0) ↔ check w x = 0 := by simp [e]
  simp_rw [h, bit_eq_fourier, ← Finset.mul_sum, Finset.sum_comm (γ := Vec w.length)]
  simp_rw [sum_sign_check, wordProd]

lemma sum_by_fibre {X C : Type*} [Fintype X] [Fintype C] (p : X → C) (g : C → ℚ) :
    (∑ x, g (p x)) = ∑ c, fibreSize p c * g c := by
  classical
  calc
    _ = ∑ x, ∑ c, bit (p x = c) * g c := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (p x)]
      · simp [bit]
      · intro c _ hc
        simp [bit, Ne.symm hc]
      · simp
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [fibreSize, Finset.sum_mul]

lemma sum_bit_subtype {X : Type*} [Fintype X] (P : X → Prop) [Fintype {x // P x}] (b : X) :
    (∑ x : {x // P x}, bit (x.val = b)) = bit (P b) := by
  classical
  by_cases hb : P b
  · rw [Finset.sum_eq_single (⟨b, hb⟩ : {x // P x})]
    · simp [bit, hb]
    · intro x _ hx
      have he : x.val ≠ b := fun he => hx (Subtype.ext he)
      simp [bit, he]
    · simp
  · rw [show bit (P b) = 0 from by simp [bit, hb]]
    apply Finset.sum_eq_zero
    intro x _
    have h : x.val ≠ b := fun he => hb (he ▸ x.property)
    simp [bit, h]

lemma fibreSize_cellLabel {m j : ℕ} (H : Submodule F (Vec m)) (b : Vec m) :
    letI := labelsFintype j H
    fibreSize (cellLabel (j := j) (H := H)) b =
      bit (b ∈ H) + bit (b = 0) * bit (Module.finrank F H < j) := by
  classical
  letI := labelsFintype j H
  unfold fibreSize
  rw [Fintype.sum_option]
  change bit ((0 : Vec m) = b) + (∑ c : Labels j H, bit (c.val = b)) = _
  rw [sum_bit_subtype]
  by_cases h0 : b = 0
  · subst b
    by_cases h : Module.finrank F H < j <;> simp [bit, h]
  · simp [bit, h0, Ne.symm h0]

noncomputable def residual {m j : ℕ} (S : Vec j →ₗ[F] Vec m) (b : Vec m) : ℚ :=
  fibreSize S b - bit (b ∈ S.range) - bit (b = 0) * bit (Module.finrank F S.range < j)

lemma transfer_residual {m j : ℕ} (b : Fin j → Vec m) (w : List (Vec m)) :
    let H := (syndrome b).range
    letI := labelsFintype j H
    Matrix.trace (wordProd (transfer b) w) =
      Matrix.trace (wordProd (condensed j H) w) +
        ∑ c : Vec m, residual (syndrome b) c * wordProd (phase c) w := by
  let H := (syndrome b).range
  letI := labelsFintype j H
  have h : Matrix.trace (wordProd (transfer b) w) =
      Matrix.trace (wordProd (condensed j H) w) +
        (∑ x : Vec j, wordProd (phase (syndrome b x)) w) -
        (∑ c : Option (Labels j H), wordProd (phase (cellLabel c)) w) := transfer_condensed b w
  rw [sum_by_fibre (syndrome b) (fun c => wordProd (phase c) w),
    sum_by_fibre cellLabel (fun c => wordProd (phase c) w)] at h
  simp_rw [fibreSize_cellLabel] at h
  rw [h, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  unfold residual
  ring

lemma residual_small {m j : ℕ} (hj : j ≤ 1) (S : Vec j →ₗ[F] Vec m) (b : Vec m) :
    residual S b = 0 := by
  letI := labelsFintype j S.range
  have h : Function.Injective (cellOf S) := by
    intro x y he
    by_cases hx : x = 0
    · exact hx.trans ((cellOf_none S y).mp (he.symm.trans ((cellOf_none S x).mpr hx))).symm
    · have hy : y ≠ 0 := fun hy => hx ((cellOf_none S x).mp (he.trans ((cellOf_none S y).mpr hy)))
      interval_cases j
      · exact Subsingleton.elim x y
      · have hx0 : x 0 ≠ 0 := fun h => hx (funext fun i => by simpa only [Subsingleton.elim i 0, Pi.zero_apply] using h)
        have hy0 : y 0 ≠ 0 := fun h => hy (funext fun i => by simpa only [Subsingleton.elim i 0, Pi.zero_apply] using h)
        funext i
        simpa only [Subsingleton.elim i 0] using
          ((two_cases (x 0)).resolve_left hx0).trans ((two_cases (y 0)).resolve_left hy0).symm
  let e := Equiv.ofBijective (cellOf S) ⟨h, cellOf_surj S⟩
  have he := e.sum_comp (fun c => bit (cellLabel c = b))
  change (∑ x, bit (cellLabel (cellOf S x) = b)) = _ at he
  simp_rw [cellOf_label] at he
  change fibreSize S b = fibreSize (cellLabel (j := j) (H := S.range)) b at he
  rw [fibreSize_cellLabel] at he
  unfold residual
  linarith

lemma star_sq_apply {C : Type*} [Fintype C] (s : C → ℚ) (i j : Option C) :
    (starEdges s * starEdges s) i j =
      match i, j with
      | none, none => ∑ c, s c
      | some _, some b => s b
      | _, _ => 0 := by
  cases i <;> cases j <;> simp [Matrix.mul_apply, Fintype.sum_option, starEdges]

lemma star_cube {C : Type*} [Fintype C] (s : C → ℚ) :
    starEdges s * starEdges s * starEdges s = (∑ c, s c) • starEdges s := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_option]
  cases i <;> cases j <;> simp [star_sq_apply, starEdges, Matrix.smul_apply, Finset.sum_mul]

lemma star_unit {C : Type*} [Fintype C] [DecidableEq C] (s : C → ℚ)
    (hs : (∑ c, s c) ≠ 1) :
    IsUnit ((1 : Matrix (Option C) (Option C) ℚ) + starEdges s) := by
  let E := starEdges s
  let q : ℚ := ∑ c, s c
  let N : Matrix (Option C) (Option C) ℚ := 1 + (q - 1)⁻¹ • (E - E*E)
  have hAN : (1+E)*N = 1 := by
    let a := (q-1)⁻¹
    have he : E*E*E = q • E := star_cube s
    have ha : a * (q-1) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hs)
    have h : a * q = 1 + a := by
      rw [mul_sub, mul_one] at ha
      linarith
    calc
      (1+E)*N = 1 + E + a • ((E-E*E) + (E*E-E*E*E)) := by
        change (1+E)*(1+a • (E-E*E)) = _
        rw [mul_add, mul_one, Algebra.mul_smul_comm, add_mul, one_mul, mul_sub, ← mul_assoc]
      _ = 1 + E + a • (E - q • E) := by rw [he]; abel
      _ = 1 := by rw [smul_sub, smul_smul, h, add_smul, one_smul]; abel

  exact ⟨⟨1+E, N, hAN, mul_eq_one_comm.mp hAN⟩, rfl⟩

lemma algebra_unit_inverse {V : Type*} [Ring V] [Algebra ℚ V] [FiniteDimensional ℚ V]
    (R : Subalgebra ℚ V) (x : V) (hx : x ∈ R) (hu : IsUnit x) :
    ∃ y ∈ R, x*y = 1 := by
  let L : R.toSubmodule →ₗ[ℚ] R.toSubmodule :=
    ((Algebra.lmul ℚ V x).domRestrict R.toSubmodule).codRestrict R.toSubmodule
      (fun z => R.mul_mem hx z.property)
  have h : Function.Injective L := by
    intro a b he
    apply Subtype.ext
    exact hu.mul_right_injective (congrArg Subtype.val he)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp h) ⟨1, R.one_mem⟩
  exact ⟨y.val, y.property, congrArg Subtype.val hy⟩

lemma dot_add_right {m : ℕ} (a b c : Vec m) : dot a (b+c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

lemma vec_add_zero {m : ℕ} (a b : Vec m) : a+b=0 ↔ a=b := by
  have h (x : Vec m) : x+x=0 := by
    funext i
    change x i + x i = 0
    rcases two_cases (x i) with hx | hx <;> rw [hx] <;> decide
  constructor
  · intro he
    exact add_right_cancel (he.trans (h b).symm)
  · rintro rfl
    exact h _

noncomputable def labelProjection {m j : ℕ} {H : Submodule F (Vec m)} (b : Vec m) :
    Matrix (Option (Labels j H)) (Option (Labels j H)) ℚ :=
  Matrix.diagonal (fun c => bit (cellLabel c = b))

lemma labelProjection_fourier {m j : ℕ} (H : Submodule F (Vec m)) (b : Vec m) :
    labelProjection (j := j) (H := H) b =
      ((2 : ℚ)⁻¹ ^ m) • ∑ a : Vec m, phase b a •
        (Matrix.diagonal (fun c : Option (Labels j H) => phase (cellLabel c) a)) := by
  classical
  ext x y
  simp only [labelProjection, Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst y
    simp only [ite_true, phase, smul_eq_mul]
    simp_rw [← sign_add, ← dot_add_right]
    rw [← bit_eq_fourier, vec_add_zero]
    exact congrArg bit (propext eq_comm)
  · simp [h]

lemma proj_leave_minus_centre {m j : ℕ} {H : Submodule F (Vec m)} (c : Labels j H) :
    labelProjection (j := j) (H := H) c.val -
      bit (c.val = 0) • Matrix.single none none 1 =
      Matrix.single (some c) (some c) 1 := by
  classical
  ext i k
  simp only [labelProjection, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.single_apply, smul_eq_mul]
  cases i with
  | none =>
    cases k <;> by_cases hc : c.val = 0 <;> simp [cellLabel, bit, hc, eq_comm]
  | some i =>
    cases k with
    | none => simp
    | some k =>
      by_cases h : i = k
      · subst k
        simp [cellLabel, bit, Subtype.ext_iff, eq_comm]
      · have hn : ¬(c = i ∧ c = k) := fun h' => h (h'.1.symm.trans h'.2)
        simp [h, hn]

lemma proj_star_centre_leave {m j : ℕ} (H : Submodule F (Vec m)) (c : Labels j H)
    (hc : c.val ≠ 0) :
    letI := labelsFintype j H
    labelProjection (0 : Vec m) * starEdges (labelSize j H) * labelProjection c.val =
      Matrix.single none (some c) (labelSize j H c) := by
  classical
  letI := labelsFintype j H
  ext i k
  unfold labelProjection
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases i with
  | none =>
    cases k with
    | none => simp [starEdges, Matrix.single_apply]
    | some d =>
      by_cases h : d = c
      · subst d
        simp [starEdges, Matrix.single_apply, cellLabel, bit]
      · have hn : d.val ≠ c.val := fun hd => h (Subtype.ext hd)
        simp [starEdges, Matrix.single_apply, cellLabel, bit, h, hn, Ne.symm h]
  | some i =>
    cases k <;> simp [starEdges, Matrix.single_apply, cellLabel, bit, Ne.symm hc]

lemma proj_star_leave_centre {m j : ℕ} (H : Submodule F (Vec m)) (c : Labels j H)
    (hc : c.val ≠ 0) :
    letI := labelsFintype j H
    labelProjection c.val * starEdges (labelSize j H) * labelProjection (0 : Vec m) =
      Matrix.single (some c) none 1 := by
  classical
  letI := labelsFintype j H
  ext i k
  unfold labelProjection
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases i with
  | none => cases k <;> simp [starEdges, Matrix.single_apply, cellLabel, bit, Ne.symm hc]
  | some i =>
    cases k with
    | none =>
      by_cases h : i = c
      · subst i
        simp [starEdges, Matrix.single_apply, cellLabel, bit]
      · have hn : i.val ≠ c.val := fun hi => h (Subtype.ext hi)
        simp [starEdges, Matrix.single_apply, cellLabel, bit, h, hn, Ne.symm h]
    | some k => simp [starEdges, Matrix.single_apply]

lemma matrix_single_scale {I J : Type*} [DecidableEq I] [DecidableEq J]
    (i : I) (j : J) (q : ℚ) :
    q • Matrix.single i j (1 : ℚ) = Matrix.single i j q := by
  ext x y
  simp [Matrix.smul_apply, Matrix.single_apply, smul_ite]

lemma matrix_single_chain {I : Type*} [Fintype I] [DecidableEq I]
    (i j k : I) (x y : ℚ) :
    Matrix.single i j x * Matrix.single j k y = Matrix.single i k (x*y) :=
  Matrix.single_mul_single_same x i j k y

lemma matrix_single_sandwich {I : Type*} [Fintype I] [DecidableEq I]
    (i j : I) (A : Matrix I I ℚ) :
    Matrix.single i i 1 * A * Matrix.single j j 1 = Matrix.single i j (A i j) := by
  simpa only [one_mul, mul_one] using Matrix.single_mul_mul_single i i j j 1 A 1

lemma condensed_zero {m j : ℕ} (H : Submodule F (Vec m)) :
    letI := labelsFintype j H
    condensed j H 0 = 1 + starEdges (labelSize j H) := by
  letI := labelsFintype j H
  unfold condensed
  have h : (fun c : Option (Labels j H) => phase (cellLabel c) 0) = 1 := by
    funext c
    simp [phase, dot, sign]
  rw [h]
  change Matrix.diagonal (fun _ => (1 : ℚ)) * _ = _
  rw [Matrix.diagonal_one, one_mul]

lemma condensed_zero_unit {m j : ℕ} (H : Submodule F (Vec m))
    (hj : 2 ≤ j) (hr : Module.finrank F H ≤ j) :
    letI := labelsFintype j H
    IsUnit (condensed j H 0) := by
  letI := labelsFintype j H
  rw [condensed_zero]
  apply star_unit
  rw [sum_labelSize H hr]
  have h : (2 : ℚ)^2 ≤ (2 : ℚ)^j := pow_le_pow_right₀ (by norm_num) hj
  norm_num at h
  linarith

set_option maxHeartbeats 1000000 in
lemma condensed_adjoin {m j : ℕ} (H : Submodule F (Vec m)) (hj : 2 ≤ j)
    (hr : Module.finrank F H ≤ j) (hpos : 0 < Module.finrank F H) :
    letI := labelsFintype j H
    Algebra.adjoin ℚ (Set.range (condensed j H)) = ⊤ := by
  classical
  letI := labelsFintype j H
  let I := Option (Labels j H)
  let R : Subalgebra ℚ (Matrix I I ℚ) := Algebra.adjoin ℚ (Set.range (condensed j H))
  have hm (a : Vec m) : condensed j H a ∈ R := Algebra.subset_adjoin (Set.mem_range_self a)
  obtain ⟨N, hN, hTN⟩ := algebra_unit_inverse R (condensed j H 0) (hm 0)
    (condensed_zero_unit H hj hr)
  have hd (a : Vec m) : Matrix.diagonal (fun c : I => phase (cellLabel c) a) ∈ R := by
    have h := R.mul_mem (hm a) hN
    change (Matrix.diagonal _ * (1 + starEdges (labelSize j H))) * N ∈ R at h
    rw [Matrix.mul_assoc, ← condensed_zero, hTN, Matrix.mul_one] at h
    exact h
  have hproj (b : Vec m) : labelProjection (j := j) (H := H) b ∈ R := by
    rw [labelProjection_fourier]
    exact R.smul_mem (R.sum_mem fun a _ => R.smul_mem (hd a) _) _
  have hE : starEdges (labelSize j H) ∈ R := by
    have h := R.sub_mem (hm 0) R.one_mem
    rw [condensed_zero] at h
    simpa using h
  have hH : H ≠ ⊥ := by intro he; rw [he, finrank_bot] at hpos; omega
  obtain ⟨b, hb, hb0⟩ := H.ne_bot_iff.mp hH
  let c : Labels j H := ⟨b, hb, Or.inl hb0⟩
  have hcb : c.val ≠ 0 := hb0
  have h0c : Matrix.single (none : I) (some c) (1 : ℚ) ∈ R := by
    have h := R.mul_mem (R.mul_mem (hproj 0) hE) (hproj c.val)
    rw [proj_star_centre_leave H c hcb, ← matrix_single_scale] at h
    have hp := R.smul_mem h (labelSize j H c)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ (labelSize_pos H hr c).ne', one_smul] at hp
  have hc0 : Matrix.single (some c : I) none (1 : ℚ) ∈ R := by
    have h := R.mul_mem (R.mul_mem (hproj c.val) hE) (hproj 0)
    rwa [proj_star_leave_centre H c hcb] at h
  have h00 : Matrix.single (none : I) none (1 : ℚ) ∈ R := by
    simpa [matrix_single_chain] using R.mul_mem h0c hc0
  have hii (i : I) : Matrix.single i i (1 : ℚ) ∈ R := by
    cases i with
    | none => exact h00
    | some a =>
      have h := R.sub_mem (hproj a.val) (R.smul_mem h00 (bit (a.val = 0)))
      rwa [proj_leave_minus_centre] at h
  have hi0 (i : I) : Matrix.single i none (1 : ℚ) ∈ R := by
    cases i with
    | none => exact h00
    | some a =>
      have h := R.mul_mem (R.mul_mem (hii (some a)) hE) h00
      rwa [matrix_single_sandwich, starEdges] at h
  have h0j (k : I) : Matrix.single none k (1 : ℚ) ∈ R := by
    cases k with
    | none => exact h00
    | some a =>
      have h := R.mul_mem (R.mul_mem h00 hE) (hii (some a))
      rw [matrix_single_sandwich, starEdges, ← matrix_single_scale] at h
      have hp := R.smul_mem h (labelSize j H a)⁻¹
      rwa [smul_smul, inv_mul_cancel₀ (labelSize_pos H hr a).ne', one_smul] at hp
  apply top_unique
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  exact R.sum_mem fun i _ => R.sum_mem fun k _ => by
    rw [← matrix_single_scale]
    exact R.smul_mem (by simpa [matrix_single_chain] using R.mul_mem (hi0 i) (h0j k)) _

def starMass (j : ℕ) : ℚ := (2 : ℚ)^j - 1

abbrev Quad (j : ℕ) := QuadraticAlgebra ℚ (starMass j) 0

lemma starMass_not_square {j : ℕ} (hj : 2 ≤ j) : ¬IsSquare (starMass j) := by
  let n : ℤ := (2 : ℤ)^j - 1
  have hn : (n : ℚ) = starMass j := by simp [n, starMass]
  intro h
  rw [← hn] at h
  obtain ⟨q, hq⟩ := h
  have hs : ∃ x : ℚ, x*x = n := ⟨q, hq.symm⟩
  have he := (Rat.exists_mul_self (n : ℚ)).mp hs
  rw [Rat.sqrt_intCast] at he
  have hm : (Int.sqrt n)^2 = n := by
    rw [sq]
    exact_mod_cast he
  have hmod := congrArg (fun x : ℤ => x % 4) hm
  have hn' : n % 4 = 3 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
    have hp : (2 : ℤ)^(2+k) = 4 * (2 : ℤ)^k := by rw [pow_add]; norm_num
    change ((2 : ℤ)^j - 1) % 4 = 3
    rw [hk, hp, Int.sub_emod, Int.mul_emod]
    norm_num
  rw [Int.sq_emod_four, hn'] at hmod
  omega

lemma quad_simple {j : ℕ} (hj : 2 ≤ j) : IsSimpleRing (Quad j) := by
  letI : Fact (¬IsSquare (starMass j)) := ⟨starMass_not_square hj⟩
  infer_instance

def quadLetter (j : ℕ) : Quad j := 1 + QuadraticAlgebra.omega

lemma quadLetter_re (j : ℕ) : (quadLetter j).re = 1 := by
  change (1 : ℚ) + 0 = 1
  simp

lemma quadLetter_im (j : ℕ) : (quadLetter j).im = 1 := by
  change (0 : ℚ) + 1 = 1
  simp

lemma quadLetter_unit {j : ℕ} (hj : 2 ≤ j) : IsUnit (quadLetter j) := by
  letI : Fact (¬IsSquare (starMass j)) := ⟨starMass_not_square hj⟩
  apply isUnit_iff_ne_zero.mpr
  intro h
  have he := congrArg QuadraticAlgebra.im h
  rw [quadLetter_im] at he
  exact one_ne_zero he

noncomputable def quadTrace (j : ℕ) : Quad j →ₗ[ℚ] ℚ :=
  2 • QuadraticAlgebra.reₗ _ _

lemma quadTrace_pair {j : ℕ} (hj : 2 ≤ j) (x : Quad j)
    (hx : ∀ y, quadTrace j (x*y) = 0) : x = 0 := by
  letI : Fact (¬IsSquare (starMass j)) := ⟨starMass_not_square hj⟩
  by_contra h
  have he := hx x⁻¹
  rw [mul_inv_cancel₀ h] at he
  change (2 : ℚ) * 1 = 0 at he
  norm_num at he

lemma quad_adjoin {A : Type*} (a : A) (j : ℕ) :
    Algebra.adjoin ℚ (Set.range (fun _ : A => quadLetter j)) = ⊤ := by
  let R := Algebra.adjoin ℚ (Set.range (fun _ : A => quadLetter j))
  have hT : quadLetter j ∈ R := Algebra.subset_adjoin (Set.mem_range_self a)
  have hω : (QuadraticAlgebra.omega : Quad j) ∈ R := by
    have h := R.sub_mem hT R.one_mem
    simpa [quadLetter] using h
  apply top_unique
  intro x _
  rw [← QuadraticAlgebra.re_smul_add_im_smul x]
  exact R.add_mem (R.smul_mem R.one_mem _) (R.smul_mem hω _)

lemma bot_label_zero {m j : ℕ} (c : Labels j (⊥ : Submodule F (Vec m))) : c.val = 0 :=
  by simpa using c.property.1

lemma bot_star_sq {m j : ℕ} (hj : 2 ≤ j) :
    letI := labelsFintype j (⊥ : Submodule F (Vec m))
    starEdges (labelSize j (⊥ : Submodule F (Vec m))) *
      starEdges (labelSize j (⊥ : Submodule F (Vec m))) =
      starMass j • (1 : Matrix (Option (Labels j (⊥ : Submodule F (Vec m))))
        (Option (Labels j (⊥ : Submodule F (Vec m)))) ℚ) := by
  let H : Submodule F (Vec m) := ⊥
  letI := labelsFintype j H
  have hr : Module.finrank F H = 0 := finrank_bot F (Vec m)
  have hsize (c : Labels j H) : labelSize j H c = starMass j := by
    simp [labelSize, hr, starMass, bot_label_zero c, bit]
  have hsum := sum_labelSize (j := j) H (hr ▸ Nat.zero_le j)
  have hs (c d : Labels j H) : c = d := Subtype.ext ((bot_label_zero c).trans (bot_label_zero d).symm)
  ext i k
  rw [star_sq_apply, Matrix.smul_apply, Matrix.one_apply]
  cases i with
  | none =>
    cases k with
    | none => simpa [starMass] using hsum
    | some k => simp
  | some i =>
    cases k with
    | none => simp
    | some k =>
      have e : i = k := hs i k
      subst k
      simpa using hsize i

noncomputable def quadLift (m j : ℕ) (hj : 2 ≤ j) :
    let H : Submodule F (Vec m) := ⊥
    letI := labelsFintype j H
    Quad j →ₐ[ℚ] Matrix (Option (Labels j H)) (Option (Labels j H)) ℚ :=
  letI := labelsFintype j (⊥ : Submodule F (Vec m))
  QuadraticAlgebra.lift ⟨starEdges (labelSize j ⊥), by
    simpa only [zero_smul, add_zero] using bot_star_sq (m := m) hj⟩

lemma condensed_bot_trace {m j : ℕ} (hj : 2 ≤ j) (w : List (Vec m)) :
    let H : Submodule F (Vec m) := ⊥
    letI := labelsFintype j H
    Matrix.trace (wordProd (condensed j H) w) =
      quadTrace j (wordProd (fun _ : Vec m => quadLetter j) w) := by
  let H : Submodule F (Vec m) := ⊥
  letI := labelsFintype j H
  let L : Quad j →ₐ[ℚ] Matrix (Option (Labels j H)) (Option (Labels j H)) ℚ := quadLift m j hj
  have hL (x : Quad j) : L x = x.re • 1 + x.im • starEdges (labelSize j H) := rfl
  have hletter (a : Vec m) : condensed j H a = L (quadLetter j) := by
    have h (c : Option (Labels j H)) : cellLabel c = (0 : Vec m) := by
      cases c with
      | none => rfl
      | some c => exact bot_label_zero c
    have hf : (fun c : Option (Labels j H) => phase (cellLabel c) a) = fun _ => 1 := by
      funext c
      simp [h c, phase, dot, sign]
    unfold condensed
    rw [hf, Matrix.diagonal_one, one_mul, hL]
    simp only [quadLetter_re, quadLetter_im, one_smul]
  change Matrix.trace (wordProd (condensed j H) w) = _
  rw [show condensed j H = (fun _ : Vec m => L (quadLetter j)) from funext hletter]
  have hp := wordProd_hom (fun _ : Vec m => quadLetter j) L.toMonoidHom w
  change wordProd (fun _ : Vec m => L (quadLetter j)) w =
    L (wordProd (fun _ : Vec m => quadLetter j) w) at hp
  rw [hp, hL, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  have ht : Matrix.trace (starEdges (labelSize j H)) = 0 := by
    unfold Matrix.trace Matrix.diag
    apply Finset.sum_eq_zero
    intro c _
    cases c <;> rfl
  have hc : Fintype.card (Option (Labels j H)) = 2 := by
    have hr : Module.finrank F H = 0 := finrank_bot F (Vec m)
    rw [card_labels H (hr ▸ Nat.zero_le j), hr]
    norm_num [show 0 ≠ j by omega]
  rw [ht, Matrix.trace_one, hc]
  simp [quadTrace, mul_comm]

lemma matrix_trace_pair {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℚ) (h : ∀ Y, Matrix.trace (X*Y) = 0) : X = 0 := by
  classical
  ext i j
  have he := h (Matrix.single j i 1)
  have hz : Matrix.trace (X * Matrix.single j i 1) = X i j := by
    unfold Matrix.trace Matrix.diag
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp only [Matrix.mul_single_apply_of_ne (hbj := hk)]
    · simp
  simpa [hz] using he

lemma lift_one_from_ideal {A B : Type*} [Ring A] [Ring B] [IsSimpleRing B]
    (f : A →+* B) (hf : Function.Surjective f) (I : TwoSidedIdeal A)
    (x : A) (hx : x ∈ I) (hfx : f x ≠ 0) : ∃ y ∈ I, f y = 1 := by
  let J : TwoSidedIdeal B := TwoSidedIdeal.mk' {b | ∃ a ∈ I, f a = b}
    ⟨0, I.zero_mem, map_zero _⟩
    (by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a+b, I.add_mem ha hb, map_add _ _ _⟩)
    (by rintro _ ⟨a, ha, rfl⟩; exact ⟨-a, I.neg_mem ha, map_neg _ _⟩)
    (by
      rintro b _ ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := hf b
      exact ⟨c*a, I.mul_mem_left _ _ ha, map_mul _ _ _⟩)
    (by
      rintro _ b ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := hf b
      exact ⟨a*c, I.mul_mem_right _ _ ha, map_mul _ _ _⟩)
  have h : f x ∈ J := by simpa only [J, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq] using ⟨x, hx, rfl⟩
  have h1 := IsSimpleRing.one_mem_of_ne_zero_mem J hfx h
  simpa only [J, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq] using h1

lemma adjoin_of_simple_factors {A V ι : Type*} [Ring V] [Algebra ℚ V] [Fintype ι]
    {B : ι → Type*} [∀ i, Ring (B i)] [∀ i, Algebra ℚ (B i)] [∀ i, IsSimpleRing (B i)]
    (M : A → V) (e : ∀ i, V →ₐ[ℚ] B i)
    (hj : ∀ x y, (∀ i, e i x = e i y) → x = y)
    (hg : ∀ i, Algebra.adjoin ℚ (Set.range (e i ∘ M)) = ⊤)
    (hs : ∀ i j, i ≠ j →
      ∃ x ∈ Algebra.adjoin ℚ (Set.range M),
        (e i x ≠ 0 ∧ e j x = 0) ∨ (e i x = 0 ∧ e j x ≠ 0)) :
    Algebra.adjoin ℚ (Set.range M) = ⊤ := by
  classical
  let R := Algebra.adjoin ℚ (Set.range M)
  let E (i : ι) : R →ₐ[ℚ] B i := (e i).comp R.val
  have hE (i : ι) : Function.Surjective (E i) := by
    have h : R.map (e i) = ⊤ := by
      simp only [R, AlgHom.map_adjoin, ← Set.range_comp]
      exact hg i
    intro y
    have hy : y ∈ R.map (e i) := by rw [h]; trivial
    obtain ⟨x, hx, he⟩ := Subalgebra.mem_map.mp hy
    exact ⟨⟨x, hx⟩, he⟩
  have hp (i j : ι) (hij : i ≠ j) : ∃ x : R, E i x = 1 ∧ E j x = 0 := by
    obtain ⟨x, hx, h | h⟩ := hs i j hij
    · have hx' : (⟨x, hx⟩ : R) ∈ TwoSidedIdeal.ker (E j).toRingHom :=
        (TwoSidedIdeal.mem_ker _).mpr h.2
      obtain ⟨y, hy, h⟩ := lift_one_from_ideal (E i).toRingHom (hE i) _ ⟨x, hx⟩ hx' h.1
      exact ⟨y, h, (TwoSidedIdeal.mem_ker _).mp hy⟩
    · have hx' : (⟨x, hx⟩ : R) ∈ TwoSidedIdeal.ker (E i).toRingHom :=
        (TwoSidedIdeal.mem_ker _).mpr h.1
      obtain ⟨y, hy, h⟩ := lift_one_from_ideal (E j).toRingHom (hE j) _ ⟨x, hx⟩ hx' h.2
      have hy' : E i y = 0 := (TwoSidedIdeal.mem_ker _).mp hy
      have h' : E j y = 1 := h
      exact ⟨1-y, by simp [hy'], by simp [h']⟩
  have hδ (i : ι) : ∃ z : R, E i z = 1 ∧ ∀ j, j ≠ i → E j z = 0 := by
    let y (j : ι) : R := if h : i ≠ j then (hp i j h).choose else 1
    let w := (Finset.univ : Finset ι).toList
    refine ⟨wordProd y w, ?_, ?_⟩
    · have he := wordProd_hom y (E i).toMonoidHom w
      change wordProd (fun j => E i (y j)) w = E i (wordProd y w) at he
      rw [← he]
      have h (j : ι) : E i (y j) = 1 := by
        by_cases he : i ≠ j
        · simpa [y, he] using (hp i j he).choose_spec.1
        · rw [show y j = 1 from dif_neg he, map_one]
      change (w.map (fun j => E i (y j))).prod = 1
      simp [h]
    · intro j hji
      have he := wordProd_hom y (E j).toMonoidHom w
      change wordProd (fun k => E j (y k)) w = E j (wordProd y w) at he
      rw [← he]
      change (w.map (fun k => E j (y k))).prod = 0
      apply List.prod_eq_zero
      apply List.mem_map.mpr
      exact ⟨j, by simp [w], by simpa [y, Ne.symm hji] using (hp i j (Ne.symm hji)).choose_spec.2⟩
  apply top_unique
  intro x _
  have h (i : ι) : ∃ z : R, E i z = e i x ∧ ∀ j, j ≠ i → E j z = 0 := by
    obtain ⟨y, hy⟩ := hE i (e i x)
    obtain ⟨z, h1, h0⟩ := hδ i
    exact ⟨z*y, by simp [h1, hy], fun j hj => by simp [h0 j hj]⟩
  let z (i : ι) := (h i).choose
  have hz : (↑(∑ i, z i) : V) = x := by
    apply hj
    intro i
    change E i (∑ j, z j) = e i x
    rw [map_sum, Finset.sum_eq_single i]
    · exact (h i).choose_spec.1
    · intro j _ hji
      exact (h j).choose_spec.2 i (Ne.symm hji)
    · simp
  rw [← hz]
  exact (∑ i, z i).property

def inverseAlphabet (m : ℕ) : ℚ := ((2 : ℚ)^m)⁻¹

lemma inverseAlphabet_pos (m : ℕ) : 0 < inverseAlphabet m := by
  unfold inverseAlphabet
  positivity

noncomputable def columnMean (m j : ℕ) : ((Fin j → Vec m) → ℚ) →ₗ[ℚ] ℚ :=
  (inverseAlphabet m)^j • ∑ b : Fin j → Vec m, LinearMap.proj b

lemma columnMean_apply (m j : ℕ) (f : (Fin j → Vec m) → ℚ) :
    columnMean m j f = (inverseAlphabet m)^j * ∑ b, f b := by
  simp [columnMean]

lemma card_columns (m j : ℕ) :
    (Fintype.card (Fin j → Vec m) : ℚ) = ((2 : ℚ)^m)^j := by
  simp [Fintype.card_fun, card_vec]

lemma columnMean_const (m j : ℕ) (c : ℚ) : columnMean m j (fun _ => c) = c := by
  rw [columnMean_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_columns]
  rw [← mul_assoc, ← mul_pow]
  simp [inverseAlphabet, show (2 : ℚ)^m ≠ 0 by positivity]

lemma columnMean_cons (m j : ℕ) (f : (Fin (j+1) → Vec m) → ℚ) :
    columnMean m (j+1) f =
      columnMean m j (fun b => inverseAlphabet m * ∑ a : Vec m, f (Fin.cons a b)) := by
  let e := Fin.consEquiv (fun _ : Fin (j+1) => Vec m)
  rw [columnMean_apply, columnMean_apply, ← e.sum_comp f, Fintype.sum_prod_type]
  simp only [e, Fin.consEquiv_apply]
  rw [Finset.sum_comm, pow_succ, mul_assoc, Finset.mul_sum]

lemma char_two_add_self {m : ℕ} (a : Vec m) : a+a=0 := (vec_add_zero a a).mpr rfl

lemma sum_bit_mem {m : ℕ} (H : Submodule F (Vec m)) :
    (∑ a : Vec m, bit (a ∈ H)) = (2 : ℚ)^(Module.finrank F H) := by
  classical
  letI : Fintype H := Fintype.ofFinite _
  have h : (↑(Fintype.card H) : ℚ) = (2 : ℚ)^(Module.finrank F H) := by
    rw [← Nat.card_eq_fintype_card, card_submodule]
    push_cast
    rfl
  unfold bit
  rw [Finset.sum_boole, ← Fintype.card_subtype (fun a : Vec m => a ∈ H)]
  exact h

lemma sum_bit_translated {m : ℕ} (H : Submodule F (Vec m)) (b : Vec m) :
    ∑ a : Vec m, bit (b+a ∈ H) = (2 : ℚ)^(Module.finrank F H) := by
  let e : Vec m ≃ Vec m := Equiv.addLeft b
  rw [← sum_bit_mem H]
  exact e.sum_comp (fun a => bit (a ∈ H))

lemma syndrome_range {m j : ℕ} (b : Fin j → Vec m) :
    (syndrome b).range = Submodule.span F (Set.range b) := by
  rw [syndrome, rowMap, Matrix.toLin'_apply', Matrix.range_mulVecLin]
  rfl

lemma syndrome_cons {m j : ℕ} (a : Vec m) (b : Fin j → Vec m) :
    (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range =
      (syndrome b).range ⊔ Submodule.span F {a} := by
  rw [syndrome_range, syndrome_range, Fin.range_cons, Submodule.span_insert, sup_comm]

lemma syndrome_rank_cons {m j : ℕ} (a : Vec m) (b : Fin j → Vec m) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    Module.finrank F (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range =
      Module.finrank F (syndrome b).range + (if a ∈ (syndrome b).range then 0 else 1) := by
  classical
  rw [syndrome_cons]
  let H := (syndrome b).range
  change Module.finrank F ((H ⊔ Submodule.span F {a} : Submodule F (Vec m)) : Type) =
    Module.finrank F H + (if a ∈ H then 0 else 1)
  by_cases ha : a ∈ H
  · have hs := (Submodule.span_singleton_le_iff_mem a H).mpr ha
    rw [sup_eq_left.mpr hs]
    simp only [if_pos ha, add_zero]
  · have hi : H ⊓ Submodule.span F {a} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rcases mem_span_binary.mp hx.2 with he | he
      · exact he
      · exact (ha (he ▸ hx.1)).elim
    have he := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span F {a})
    have ha0 : a ≠ 0 := fun e => ha (e.symm ▸ H.zero_mem)
    rw [hi, finrank_bot, add_zero, finrank_span_singleton ha0] at he
    simpa only [if_neg ha] using he

lemma syndrome_empty {m : ℕ} (b : Fin 0 → Vec m) : (syndrome b).range = ⊥ := by
  rw [syndrome_range]
  simp

lemma mem_sup_binary {m : ℕ} (H : Submodule F (Vec m)) (a c : Vec m) :
    c ∈ H ⊔ Submodule.span F {a} ↔ c ∈ H ∨ c+a ∈ H := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rcases mem_span_binary.mp hy with rfl | rfl
    · left
      simpa using hx
    · right
      simpa [add_assoc, char_two_add_self] using hx
  · rintro (hc | hc)
    · exact ⟨c, hc, 0, Submodule.zero_mem _, add_zero c⟩
    · exact ⟨c+a, hc, a, Submodule.mem_span_singleton_self a, by simp [add_assoc, char_two_add_self]⟩

noncomputable def fullRankMean (m j : ℕ) : ℚ :=
  columnMean m j (fun b => bit (Module.finrank F (syndrome b).range = j))

lemma fullRankMean_zero (m : ℕ) : fullRankMean m 0 = 1 := by
  have h (b : Fin 0 → Vec m) : bit (Module.finrank F (syndrome b).range = 0) = 1 :=
    by simp [syndrome_empty, bit]
  unfold fullRankMean
  simp_rw [h]
  exact columnMean_const m 0 1

lemma fullRankMean_succ (m j : ℕ) :
    fullRankMean m (j+1) = (1 - inverseAlphabet m * (2 : ℚ)^j) * fullRankMean m j := by
  classical
  unfold fullRankMean
  rw [columnMean_cons]
  have h (b : Fin j → Vec m) :
      inverseAlphabet m * ∑ a : Vec m,
        bit (Module.finrank F (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range = j+1) =
        (1 - inverseAlphabet m * (2 : ℚ)^j) * bit (Module.finrank F (syndrome b).range = j) := by
    let H := (syndrome b).range
    let r := Module.finrank F H
    have hr := rank_range_le (syndrome b)
    change r ≤ j at hr
    by_cases he : r = j
    · have hb (a : Vec m) : bit (Module.finrank F (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range = j+1)
          = 1 - bit (a ∈ H) := by
        rw [syndrome_rank_cons, show Module.finrank F (syndrome b).range = j from he]
        by_cases ha : a ∈ H <;> simp [H, ha, bit]
      simp_rw [hb, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, sum_bit_mem, show Module.finrank F H = j from he]
      have hc : (Fintype.card (Vec m) : ℚ) = (2 : ℚ)^m := by simp [card_vec]
      have hi : inverseAlphabet m * (2 : ℚ)^m = 1 := by
        exact inv_mul_cancel₀ (by positivity)
      rw [hc, mul_sub, hi]
      simp [bit, show Module.finrank F (syndrome b).range = j from he]
    · have hb (a : Vec m) : bit (Module.finrank F (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range = j+1) = 0 := by
        rw [syndrome_rank_cons]
        change bit (r + (if a ∈ H then 0 else 1) = j+1) = 0
        have hne : r + (if a ∈ H then 0 else 1) ≠ j+1 := by split_ifs <;> omega
        simp [bit, hne]
      simp_rw [hb]
      simp [bit, show Module.finrank F (syndrome b).range ≠ j from he]
  simp_rw [h]
  exact (columnMean m j).map_smul _ _

noncomputable def missingMoment {m : ℕ} (c : Vec m) (t j : ℕ) : ℚ :=
  columnMean m j (fun b => bit (c ∉ (syndrome b).range) *
    ((2 : ℚ)^(Module.finrank F (syndrome b).range))^t)

lemma missingMoment_zero {m : ℕ} {c : Vec m} (hc : c ≠ 0) (t : ℕ) :
    missingMoment c t 0 = 1 := by
  have h (b : Fin 0 → Vec m) :
      bit (c ∉ (syndrome b).range) * ((2 : ℚ)^(Module.finrank F (syndrome b).range))^t = 1 :=
    by rw [syndrome_empty b, finrank_bot]; simp [bit, hc]
  unfold missingMoment
  simp_rw [h]
  exact columnMean_const m 0 1

lemma missingMoment_succ {m : ℕ} (c : Vec m) (t j : ℕ) :
    missingMoment c t (j+1) =
      (2 : ℚ)^t * missingMoment c t j -
        (((2 : ℚ)^(t+1)-1) * inverseAlphabet m) * missingMoment c (t+1) j := by
  classical
  unfold missingMoment
  rw [columnMean_cons]
  have h (b : Fin j → Vec m) :
      inverseAlphabet m * ∑ a : Vec m,
        bit (c ∉ (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range) *
          ((2 : ℚ)^(Module.finrank F (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range))^t =
      (2 : ℚ)^t * (bit (c ∉ (syndrome b).range) * ((2 : ℚ)^(Module.finrank F (syndrome b).range))^t) -
        (((2 : ℚ)^(t+1)-1) * inverseAlphabet m) *
          (bit (c ∉ (syndrome b).range) * ((2 : ℚ)^(Module.finrank F (syndrome b).range))^(t+1)) := by
    let H := (syndrome b).range
    let r := Module.finrank F H
    let q := (2 : ℚ)^r
    by_cases hc : c ∈ H
    · have hc' (a : Vec m) : c ∈ (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range := by
        rw [syndrome_cons]
        exact Submodule.mem_sup_left hc
      simp [hc', hc, H, bit]
    · have hsum (a : Vec m) :
          bit (c ∉ (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range) *
            ((2 : ℚ)^(Module.finrank F (syndrome (Fin.cons (α := fun _ => Vec m) a b)).range))^t =
            q^t * (bit (a ∈ H) + (2 : ℚ)^t * (1 - bit (a ∈ H) - bit (c+a ∈ H))) := by
        rw [syndrome_rank_cons, syndrome_cons, mem_sup_binary]
        change bit (¬(c ∈ H ∨ c+a ∈ H)) *
          ((2 : ℚ)^(r+(if a ∈ H then 0 else 1)))^t = _
        by_cases ha : a ∈ H
        · have hn : c+a ∉ H := fun h => hc (by simpa [add_assoc, char_two_add_self] using H.add_mem h ha)
          simp [bit, ha, hc, hn, q]
        · by_cases hn : c+a ∈ H
          · simp [bit, ha, hc, hn, q]
          · simp [bit, ha, hc, hn, q, pow_succ, mul_pow]
      simp_rw [hsum]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_bit_mem, sum_bit_translated,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hcard : (Fintype.card (Vec m) : ℚ) = (2 : ℚ)^m := by simp [card_vec]
      rw [hcard]
      change inverseAlphabet m * (q^t * (q + (2 : ℚ)^t * ((2 : ℚ)^m-q-q))) =
        (2 : ℚ)^t * (bit (c ∉ H) * q^t) - _ * (bit (c ∉ H) * q^(t+1))
      simp only [bit, hc, not_false_eq_true, ite_true, one_mul, pow_succ]
      unfold inverseAlphabet
      field_simp
      ring
  simp_rw [h]
  let f (b : Fin j → Vec m) := bit (c ∉ (syndrome b).range) *
    ((2 : ℚ)^(Module.finrank F (syndrome b).range))^t
  let g (b : Fin j → Vec m) := bit (c ∉ (syndrome b).range) *
    ((2 : ℚ)^(Module.finrank F (syndrome b).range))^(t+1)
  change columnMean m j ((2 : ℚ)^t • f - (((2 : ℚ)^(t+1)-1) * inverseAlphabet m) • g) =
    _ * columnMean m j f - _ * columnMean m j g
  simp [smul_eq_mul]

noncomputable def coeffExtract (d : ℕ) : (ℕ → ℚ) →ₗ[ℚ] ℚ :=
  ∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j • LinearMap.proj j

lemma coeffExtract_apply (d : ℕ) (f : ℕ → ℚ) :
    coeffExtract d f = ∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j * f j := by
  simp [coeffExtract]

lemma weight_coeff_zero_succ (d : ℕ) :
    (weightPoly (d+1)).coeff 0 = -(2 : ℚ)^d * (weightPoly d).coeff 0 := by
  rw [weightPoly_succ,mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C]
  ring

lemma weight_coeff_succ_succ (d t : ℕ) :
    (weightPoly (d+1)).coeff (t+1) =
      (weightPoly d).coeff t - (2 : ℚ)^d * (weightPoly d).coeff (t+1) := by
  rw [weightPoly_succ, mul_sub, coeff_sub, coeff_mul_X, coeff_mul_C]
  ring

lemma weight_coeff_pos_signed {d j : ℕ} (hj : j ≤ d) :
    0 < (-1 : ℚ)^d * (-1 : ℚ)^j * (weightPoly d).coeff j := by
  induction d generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp [weightPoly]
  | succ d ih =>
    cases j with
    | zero =>
      have h := ih (j := 0) (Nat.zero_le d)
      rw [weight_coeff_zero_succ, pow_succ]
      convert mul_pos (pow_pos (by norm_num : (0 : ℚ)<2) d) h using 1
      ring
    | succ j =>
      have h : j ≤ d := by omega
      have h₁ := ih h
      have h₂ : 0 ≤ (-1 : ℚ)^d * (-1 : ℚ)^(j+1) * (weightPoly d).coeff (j+1) := by
        by_cases hj' : j+1 ≤ d
        · exact (ih hj').le
        · rw [coeff_eq_zero_of_natDegree_lt (by rw [(weightPoly_degree_monic d).1]; omega), mul_zero]
      rw [weight_coeff_succ_succ]
      convert add_pos_of_pos_of_nonneg h₁
        (mul_nonneg (pow_nonneg (by norm_num : (0 : ℚ)≤2) d) h₂) using 1
      simp only [pow_succ]
      ring

lemma weight_coeff_ne_zero {d j : ℕ} (h : j ≤ d) : (weightPoly d).coeff j ≠ 0 := by
  intro hz
  have h' := weight_coeff_pos_signed h
  rw [hz, mul_zero] at h'
  exact (lt_irrefl _ h')

lemma coeffExtract_pow (d : ℕ) (x : ℚ) :
    coeffExtract d (fun j => x^j) = (weightPoly d).eval x := by
  rw [coeffExtract_apply, weightPoly_eval_sum]

lemma coeffExtract_const {d : ℕ} (hd : 0 < d) (c : ℚ) : coeffExtract d (fun _ => c) = 0 := by
  have h : coeffExtract d (fun _ => (1 : ℚ)) = 0 := by
    simpa only [one_pow, pow_zero] using
      (coeffExtract_pow d 1).trans (by simpa only [pow_zero] using weightPoly_root (i := 0) hd)
  have he : (fun _ : ℕ => c) = c • (fun _ : ℕ => (1 : ℚ)) := by
    funext j
    simp
  rw [he, map_smul, h, smul_zero]

lemma coeffExtract_succ (d : ℕ) (f : ℕ → ℚ) :
    coeffExtract (d+1) f = coeffExtract d (fun j => f (j+1)) - (2 : ℚ)^d * coeffExtract d f := by
  simp only [coeffExtract_apply]
  rw [Finset.sum_range_succ', weight_coeff_zero_succ]
  simp_rw [weight_coeff_succ_succ, sub_mul]
  have h : (weightPoly d).coeff (d+1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [(weightPoly_degree_monic d).1]; omega)
  have he :
      (∑ j ∈ Finset.range (d+1), (2 : ℚ)^d * (weightPoly d).coeff (j+1) * f (j+1)) +
        (2 : ℚ)^d * (weightPoly d).coeff 0 * f 0 =
        (2 : ℚ)^d * ∑ j ∈ Finset.range (d+1), (weightPoly d).coeff j * f j := by
    rw [← Finset.sum_range_succ' (f := fun j => (2 : ℚ)^d * (weightPoly d).coeff j * f j),
      Finset.sum_range_succ, h]
    simp only [mul_zero, zero_mul, add_zero, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  linarith

noncomputable def differences : ℕ → (ℕ → ℚ) → ℕ → ℚ
  | 0, f, s => f s
  | d+1, f, s => differences d f (s+1) - (2 : ℚ)^d * differences d f s

lemma differences_extract (d : ℕ) (f : ℕ → ℚ) (s : ℕ) :
    differences d f s = coeffExtract d (fun j => f (s+j)) := by
  induction d generalizing s with
  | zero => simp [differences, coeffExtract_apply, weightPoly]
  | succ d ih =>
    rw [differences, ih, ih, coeffExtract_succ]
    simp only [Nat.add_assoc, Nat.add_comm 1]

noncomputable def missingCoef (m : ℕ) : ℕ → ℚ
  | 0 => 1
  | d+1 => -(((2 : ℚ)^(d+1)-1) * inverseAlphabet m) * missingCoef m d

lemma missingCoef_ne_zero (m d : ℕ) : missingCoef m d ≠ 0 := by
  induction d with
  | zero => simp [missingCoef]
  | succ d ih =>
    have h : (1 : ℚ)<(2 : ℚ)^(d+1) := one_lt_pow₀ (by norm_num) (by omega)
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (sub_pos.mpr h).ne'
      (inverseAlphabet_pos m).ne')) ih

lemma missing_extract {m : ℕ} (c : Vec m) (d s : ℕ) :
    differences d (missingMoment c 0) s = missingCoef m d * missingMoment c d s := by
  induction d generalizing s with
  | zero => simp [differences, missingCoef]
  | succ d ih =>
    rw [differences, ih, ih, missingMoment_succ, missingCoef]
    ring

lemma fullRank_extract (m d s : ℕ) :
    differences d (fullRankMean m) s =
      (inverseAlphabet m)^d * (weightPoly d).coeff 0 *
        (2 : ℚ)^(d*s) * fullRankMean m s := by
  induction d generalizing s with
  | zero => simp [differences, weightPoly]
  | succ d ih =>
    rw [differences, ih, ih, fullRankMean_succ, weight_coeff_zero_succ]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, pow_add, pow_succ]
    ring

def evaluateColumn {m j : ℕ} (x : Vec j) : (Fin j → Vec m) →ₗ[F] Vec m where
  toFun b := syndrome b x
  map_add' b c := by
    funext a
    change (∑ r, (b r a + c r a) * x r) = (∑ r, b r a * x r) + (∑ r, c r a * x r)
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' k b := by
    funext a
    change (∑ r, (k * b r a) * x r) = k * ∑ r, b r a * x r
    simp [Finset.mul_sum, mul_assoc]

lemma evaluateColumn_surj {m j : ℕ} {x : Vec j} (hx : x ≠ 0) :
    Function.Surjective (evaluateColumn (m := m) x) := by
  classical
  have h : ∃ r, x r ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (funext hn)
  obtain ⟨r, hr⟩ := h
  have h1 := (two_cases (x r)).resolve_left hr
  intro y
  refine ⟨Pi.single r y, ?_⟩
  funext a
  change (∑ s, (Pi.single r y : Fin j → Vec m) s a * x s) = y a
  rw [Finset.sum_eq_single r]
  · simp [h1]
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

lemma mean_evaluateColumn {m j : ℕ} {x : Vec j} (hx : x ≠ 0) (c : Vec m) :
    columnMean m j (fun b => bit (syndrome b x = c)) = inverseAlphabet m := by
  classical
  let S := evaluateColumn (m := m) x
  have h (b : Vec m) : fibreSize S b = (Nat.card S.ker : ℚ) := by
    rw [fibreSize_eq_card, Nat.card_congr (linearFibreEquiv S b (evaluateColumn_surj hx b))]
  have hs := sum_fibreSize S
  simp_rw [h] at hs
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_columns] at hs
  have hc : (Fintype.card (Vec m) : ℚ) = (2 : ℚ)^m := by simp [card_vec]
  rw [hc] at hs
  rw [columnMean_apply]
  change (inverseAlphabet m)^j * fibreSize S c = _
  rw [h]
  have hn : (2 : ℚ)^m ≠ 0 := by positivity
  unfold inverseAlphabet
  rw [inv_pow, ← div_eq_inv_mul]
  exact (div_eq_iff (pow_ne_zero j hn)).2 (by
    rw [← hs, ← mul_assoc, inv_mul_cancel₀ hn, one_mul])

lemma mean_fibre {m j : ℕ} (c : Vec m) :
    columnMean m j (fun b => fibreSize (syndrome b) c) =
      bit (c=0) + inverseAlphabet m * ((2 : ℚ)^j - 1) := by
  classical
  have he : (fun b : Fin j → Vec m => fibreSize (syndrome b) c) =
      ∑ x : Vec j, (fun b : Fin j → Vec m => bit (syndrome b x = c)) := by
    funext b
    simp [fibreSize, Finset.sum_apply]
  rw [he]
  rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Vec j))]
  have hz : columnMean m j (fun b => bit (syndrome b 0 = c)) = bit (c=0) := by
    simp_rw [map_zero]
    rw [columnMean_const]
    exact congrArg bit (propext eq_comm)
  rw [hz]
  congr 1
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (Vec j)).erase 0, inverseAlphabet m := by
      apply Finset.sum_congr rfl
      intro x hx
      exact mean_evaluateColumn (Finset.mem_erase.mp hx).1 c
    _ = _ := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        card_vec, nsmul_eq_mul, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
      simp [mul_comm]

lemma mean_residual_zero (m j : ℕ) :
    columnMean m j (fun b => residual (syndrome b) (0 : Vec m)) =
      inverseAlphabet m * ((2 : ℚ)^j - 1) - 1 + fullRankMean m j := by
  classical
  have h (b : Fin j → Vec m) :
      residual (syndrome b) (0 : Vec m) = fibreSize (syndrome b) (0 : Vec m) - 2 +
        bit (Module.finrank F (syndrome b).range = j) := by
    have hr := rank_range_le (syndrome b)
    unfold residual
    by_cases he : Module.finrank F (syndrome b).range = j
    · have hn : ¬Module.finrank F (syndrome b).range < j := by omega
      simp [bit, he, hn]
      ring
    · have hlt : Module.finrank F (syndrome b).range < j := by omega
      simp [bit, he, hlt]
      ring
  simp_rw [h]
  change columnMean m j ((fun b => fibreSize (syndrome b) (0 : Vec m)) -
    (fun _ => (2 : ℚ)) + (fun b => bit (Module.finrank F (syndrome b).range = j))) = _
  rw [map_add, map_sub, mean_fibre, columnMean_const]
  simp [bit, fullRankMean]
  ring

lemma mean_residual_nonzero {m j : ℕ} {c : Vec m} (hc : c ≠ 0) :
    columnMean m j (fun b => residual (syndrome b) c) =
      inverseAlphabet m * ((2 : ℚ)^j - 1) - 1 + missingMoment c 0 j := by
  classical
  have h (b : Fin j → Vec m) :
      residual (syndrome b) c = fibreSize (syndrome b) c - 1 +
        bit (c ∉ (syndrome b).range) := by
    unfold residual
    by_cases he : c ∈ (syndrome b).range <;> simp [bit, he, hc]
  simp_rw [h]
  change columnMean m j ((fun b => fibreSize (syndrome b) c) -
    (fun _ => (1 : ℚ)) + (fun b => bit (c ∉ (syndrome b).range))) = _
  rw [map_add, map_sub, mean_fibre, columnMean_const]
  simp [bit, hc, missingMoment]

lemma coeffExtract_base {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    coeffExtract d (fun j => inverseAlphabet m * ((2 : ℚ)^j-1) - 1) = 0 := by
  change coeffExtract d (inverseAlphabet m • ((fun j : ℕ => (2 : ℚ)^j) -
    (fun _ => (1 : ℚ))) - (fun _ => (1 : ℚ))) = 0
  have hz : (weightPoly d).eval 2 = 0 := by
    simpa only [pow_one] using weightPoly_root (i := 1) (by omega : 1 < d)
  rw [map_sub, map_smul, map_sub, coeffExtract_pow, hz, coeffExtract_const (by omega)]
  simp

noncomputable def scalarWeight {m : ℕ} (d : ℕ) (c : Vec m) : ℚ :=
  (weightPoly d).coeff 0 * bit (c=0) +
    coeffExtract d (fun j => columnMean m j (fun b => residual (syndrome b) c))

lemma scalarWeight_ne_zero {m d : ℕ} (hd : 2 ≤ d) (c : Vec m) : scalarWeight d c ≠ 0 := by
  classical
  unfold scalarWeight
  by_cases hc : c = 0
  · subst c
    simp only [bit, ite_true, mul_one, mean_residual_zero]
    change (weightPoly d).coeff 0 + coeffExtract d
      ((fun j => inverseAlphabet m * ((2 : ℚ)^j-1)-1) + fullRankMean m) ≠ 0
    rw [map_add, coeffExtract_base hd, zero_add]
    have h := differences_extract d (fullRankMean m) 0
    simp only [zero_add] at h
    rw [← h, fullRank_extract, fullRankMean_zero, mul_zero, pow_zero, mul_one]
    have he : (weightPoly d).coeff 0 + (inverseAlphabet m)^d * (weightPoly d).coeff 0 =
        (1+(inverseAlphabet m)^d) * (weightPoly d).coeff 0 := by ring
    simp only [mul_one, he]
    exact mul_ne_zero (by have := inverseAlphabet_pos m; positivity)
      (weight_coeff_ne_zero (Nat.zero_le _))
  · simp only [bit, hc, ite_false, mul_zero, zero_add, mean_residual_nonzero hc]
    change coeffExtract d ((fun j => inverseAlphabet m * ((2 : ℚ)^j-1)-1) +
      missingMoment c 0) ≠ 0
    rw [map_add, coeffExtract_base hd, zero_add]
    have h := differences_extract d (missingMoment c 0) 0
    simp only [zero_add] at h
    rw [← h, missing_extract, missingMoment_zero hc, mul_one]
    exact missingCoef_ne_zero m d

def dotForm (m : ℕ) : LinearMap.BilinForm F (Vec m) where
  toFun a :=
    { toFun b := dot a b
      map_add' := dot_add_right a
      map_smul' k b := by
        simp [dot, Pi.smul_apply, mul_comm, mul_left_comm, Finset.mul_sum] }
  map_add' a b := by
    apply LinearMap.ext
    exact dot_add_left a b
  map_smul' k a := by
    apply LinearMap.ext
    intro b
    simp [dot, Pi.smul_apply, Finset.mul_sum, mul_assoc]

lemma dotForm_nondeg (m : ℕ) : (dotForm m).Nondegenerate := by
  have h (a : Vec m) (ha : ∀ b, dot a b = 0) : a = 0 := by
    funext i
    change a i = 0
    rw [← dot_single_left a i, dot_comm]
    exact ha _
  exact ⟨h, fun a ha => h a (fun b => (dot_comm a b).trans (ha b))⟩

lemma dotForm_refl (m : ℕ) : (dotForm m).IsRefl := fun a b h => (dot_comm b a).trans h

def annihilatorEquiv (m : ℕ) : Submodule F (Vec m) ≃ Submodule F (Vec m) where
  toFun := (dotForm m).orthogonal
  invFun := (dotForm m).orthogonal
  left_inv := LinearMap.BilinForm.orthogonal_orthogonal (dotForm_nondeg m) (dotForm_refl m)
  right_inv := LinearMap.BilinForm.orthogonal_orthogonal (dotForm_nondeg m) (dotForm_refl m)

lemma finrank_annihilator {m : ℕ} (H : Submodule F (Vec m)) :
    Module.finrank F (annihilatorEquiv m H) = m - Module.finrank F H := by
  exact (LinearMap.BilinForm.finrank_orthogonal (dotForm_nondeg m) H).trans
    (by simp [Module.finrank_fintype_fun_eq_card])

lemma sign_eq_one (x : F) : sign x = 1 ↔ x = 0 := by
  by_cases h : x = 0 <;> norm_num [sign, h]

lemma condensed_eq_zeroLetter {m j : ℕ} (H : Submodule F (Vec m))
    (hj : 2 ≤ j) (hr : Module.finrank F H ≤ j) (a : Vec m) :
    condensed j H a = condensed j H 0 ↔ a ∈ annihilatorEquiv m H := by
  letI := labelsFintype j H
  let I := Option (Labels j H)
  let D : Matrix I I ℚ := Matrix.diagonal (fun c => phase (cellLabel c) a)
  have h : condensed j H a = D * condensed j H 0 := by
    rw [condensed_zero]
    rfl
  have he : condensed j H a = condensed j H 0 ↔ D = 1 := by
    constructor
    · intro he
      apply (condensed_zero_unit H hj hr).mul_left_inj.mp
      rw [one_mul, ← h, he]
    · intro he
      rw [h, he, one_mul]
  rw [he]
  change D = 1 ↔ a ∈ (dotForm m).orthogonal H
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hD b hb
    change dot b a = 0
    by_cases h0 : b = 0
    · simp [h0, dot]
    · let c : Labels j H := ⟨b, hb, Or.inl h0⟩
      have he := congrArg (fun x : Matrix I I ℚ => x (some c) (some c)) hD
      have hv : sign (dot a b) = 1 := by
        simpa [D, phase, cellLabel, c, Matrix.one_apply] using he
      exact (dot_comm b a).trans ((sign_eq_one _).mp hv)
  · intro h
    have hv (c : I) : phase (cellLabel c) a = 1 := by
      cases c with
      | none => simp [phase, cellLabel, dot, sign]
      | some c =>
        exact (sign_eq_one _).mpr ((dot_comm a c.val).trans (h c.val c.property.1))
    have he : (fun c : I => phase (cellLabel c) a) = fun _ => 1 := funext hv
    unfold D
    rw [he, Matrix.diagonal_one]

abbrev Degree (d : ℕ) := ↥(Finset.Icc (2 : ℕ) d)

abbrev ActiveSubmodule (m j : ℕ) :=
  {H : Submodule F (Vec m) // 0 < Module.finrank F H ∧ Module.finrank F H ≤ j}

abbrev MatrixFactor (m d : ℕ) := Σ j : Degree d, ActiveSubmodule m j.val

abbrev Factor (m d : ℕ) := (Vec m ⊕ Vec m) ⊕ (Degree d ⊕ MatrixFactor m d)

noncomputable def activeFintype (m j : ℕ) : Fintype (ActiveSubmodule m j) := Fintype.ofFinite _

noncomputable def factorFintype (m d : ℕ) : Fintype (Factor m d) :=
  letI : ∀ j : Degree d, Fintype (ActiveSubmodule m j.val) := fun j => activeFintype m j.val
  inferInstance

lemma sum_factors {R : Type*} [AddCommMonoid R] {m d : ℕ} (f : Factor m d → R) :
    letI : ∀ j : Degree d, Fintype (ActiveSubmodule m j.val) := fun j => activeFintype m j.val
    letI := factorFintype m d
    (∑ i : Factor m d, f i) =
      ((∑ a : Vec m, f (.inl (.inl a))) + ∑ a : Vec m, f (.inl (.inr a))) +
      ((∑ j : Degree d, f (.inr (.inl j))) +
        ∑ j : Degree d, ∑ H : ActiveSubmodule m j.val, f (.inr (.inr ⟨j,H⟩))) := by
  letI : ∀ j : Degree d, Fintype (ActiveSubmodule m j.val) := fun j => activeFintype m j.val
  have h := Fintype.sum_sum_type f
  change (∑ i : Factor m d, f i) = _
  rw [h, Fintype.sum_sum_type (fun a : Vec m ⊕ Vec m => f (.inl a)),
    Fintype.sum_sum_type (fun a : Degree d ⊕ MatrixFactor m d => f (.inr a)),
    Fintype.sum_sigma (fun a : MatrixFactor m d => f (.inr (.inr a)))]

noncomputable def factorAlg (m d : ℕ) : Factor m d → AlgCat ℚ
  | .inl _ => AlgCat.of ℚ ℚ
  | .inr (.inl j) => AlgCat.of ℚ (Quad j.val)
  | .inr (.inr ⟨j,H⟩) =>
    letI := labelsFintype j.val H.val
    AlgCat.of ℚ (Matrix (Option (Labels j.val H.val)) (Option (Labels j.val H.val)) ℚ)

abbrev Model (m d : ℕ) := (i : Factor m d) → factorAlg m d i

noncomputable def modelLetter (m d : ℕ) (a : Vec m) : Model m d
  | .inl (.inl c) => phase c a
  | .inl (.inr c) => letter c a
  | .inr (.inl j) => quadLetter j.val
  | .inr (.inr ⟨j,H⟩) => condensed j.val H.val a

noncomputable def factorTrace (m d : ℕ) (i : Factor m d) : factorAlg m d i →ₗ[ℚ] ℚ :=
  match i with
  | .inl _ => LinearMap.id
  | .inr (.inl j) => quadTrace j.val
  | .inr (.inr ⟨j,H⟩) =>
    letI := labelsFintype j.val H.val
    Matrix.traceLinearMap _ ℚ ℚ

lemma factor_finite (m d : ℕ) (i : Factor m d) : Module.Finite ℚ (factorAlg m d i) := by
  rcases i with a | (j | ⟨j,H⟩)
  · change Module.Finite ℚ ℚ
    infer_instance
  · change Module.Finite ℚ (Quad j.val)
    infer_instance
  · change Module.Finite ℚ (Matrix (Option (Labels j.val H.val)) (Option (Labels j.val H.val)) ℚ)
    infer_instance

lemma factor_simple (m d : ℕ) (i : Factor m d) : IsSimpleRing (factorAlg m d i) := by
  rcases i with a | (j | ⟨j,H⟩)
  · change IsSimpleRing ℚ
    infer_instance
  · exact quad_simple (Finset.mem_Icc.mp j.property).1
  · letI := labelsFintype j.val H.val
    change IsSimpleRing (Matrix (Option (Labels j.val H.val)) (Option (Labels j.val H.val)) ℚ)
    infer_instance

lemma factorTrace_pair (m d : ℕ) (i : Factor m d) (x : factorAlg m d i)
    (h : ∀ y, factorTrace m d i (x*y) = 0) : x = 0 := by
  rcases i with a | (j | ⟨j,H⟩)
  · change (x : ℚ) = 0
    have he := h 1
    change (x : ℚ) * 1 = 0 at he
    simpa using he
  · exact quadTrace_pair (Finset.mem_Icc.mp j.property).1 _ h
  · letI := labelsFintype j.val H.val
    exact matrix_trace_pair _ h

lemma word_model_apply (m d : ℕ) (w : List (Vec m)) (i : Factor m d) :
    wordProd (modelLetter m d) w i = wordProd (fun a => modelLetter m d a i) w :=
  (wordProd_hom (modelLetter m d) (Pi.evalMonoidHom _ i) w).symm

lemma letter_zero {m : ℕ} (b : Vec m) : letter b 0 = 2 := by
  norm_num [letter, dot, sign]

lemma phase_zero {m : ℕ} (b : Vec m) : phase b 0 = 1 := by simp [phase, dot, sign]

lemma modelLetter_zero_unit (m d : ℕ) : IsUnit (modelLetter m d 0) := by
  rw [Pi.isUnit_iff]
  rintro ((a | a) | (j | ⟨j,H⟩))
  · change IsUnit (phase a 0)
    rw [phase_zero]
    exact isUnit_one
  · change IsUnit (letter a 0)
    rw [letter_zero]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · exact quadLetter_unit (Finset.mem_Icc.mp j.property).1
  · exact condensed_zero_unit H.val (Finset.mem_Icc.mp j.property).1 H.property.2

lemma eval_factor_adjoin (m d : ℕ) (i : Factor m d) :
    Algebra.adjoin ℚ (Set.range (fun a => modelLetter m d a i)) = ⊤ := by
  rcases i with a | (j | ⟨j,H⟩)
  · have : (factorAlg m d (.inl a) : Type) = ℚ := rfl
    apply top_unique
    intro x _
    exact (Algebra.adjoin ℚ _).algebraMap_mem (show ℚ from x)
  · exact quad_adjoin (0 : Vec m) j.val
  · exact condensed_adjoin H.val (Finset.mem_Icc.mp j.property).1 H.property.2 H.property.1

noncomputable def imageMass {m : ℕ} (j : ℕ) (H : Submodule F (Vec m)) : ℚ :=
  (inverseAlphabet m)^j * (weightPoly (Module.finrank F H)).eval ((2 : ℚ)^j)

lemma imageMass_pos {m j : ℕ} (H : Submodule F (Vec m)) (hj : Module.finrank F H ≤ j) :
    0 < imageMass j H := by
  unfold imageMass
  rw [weightPoly_eval]
  apply mul_pos (pow_pos (inverseAlphabet_pos _) _) (Finset.prod_pos _)
  intro i hi
  exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) ((Finset.mem_range.mp hi).trans_le hj))

noncomputable def factorWeight (m d : ℕ) : Factor m d → ℚ
  | .inl (.inl c) => scalarWeight d c
  | .inl (.inr _) => (weightPoly d).coeff 1 * inverseAlphabet m
  | .inr (.inl j) => (weightPoly d).coeff j.val * imageMass j.val (⊥ : Submodule F (Vec m))
  | .inr (.inr ⟨j,H⟩) => (weightPoly d).coeff j.val * imageMass j.val H.val

lemma factorWeight_ne_zero {m d : ℕ} (hd : 2 ≤ d) (i : Factor m d) : factorWeight m d i ≠ 0 := by
  rcases i with (b | b) | (j | ⟨j,H⟩)
  · exact scalarWeight_ne_zero hd b
  · exact mul_ne_zero (weight_coeff_ne_zero (by omega)) (inverseAlphabet_pos _).ne'
  · exact mul_ne_zero (weight_coeff_ne_zero (Finset.mem_Icc.mp j.property).2)
      (imageMass_pos _ (by rw [finrank_bot]; exact Nat.zero_le _)).ne'
  · exact mul_ne_zero (weight_coeff_ne_zero (Finset.mem_Icc.mp j.property).2)
      (imageMass_pos H.val H.property.2).ne'

noncomputable def modelTrace (m d : ℕ) : Model m d →ₗ[ℚ] ℚ :=
  letI := factorFintype m d
  ∑ i : Factor m d, factorWeight m d i • (factorTrace m d i).comp (LinearMap.proj i)

lemma modelTrace_apply {m d : ℕ} (x : Model m d) :
    letI := factorFintype m d
    modelTrace m d x = ∑ i : Factor m d, factorWeight m d i * factorTrace m d i (x i) := by
  letI := factorFintype m d
  simp [modelTrace]

lemma modelTrace_pair {m d : ℕ} (hd : 2 ≤ d) (x : Model m d)
    (h : ∀ y, modelTrace m d (x*y) = 0) : x = 0 := by
  classical
  letI := factorFintype m d
  funext i
  change x i = 0
  apply factorTrace_pair m d i
  intro y
  have he := h (Pi.single i y)
  rw [modelTrace_apply, Finset.sum_eq_single i] at he
  · simp only [Pi.mul_apply, Pi.single_eq_same] at he
    exact (mul_eq_zero.mp he).resolve_left (factorWeight_ne_zero hd i)
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

noncomputable def shiftedLetter (m d : ℕ) : Model m d := modelLetter m d 0 - 1

noncomputable def scalarTest (m d : ℕ) (t : Bool) : Model m d :=
  shiftedLetter m d - (if t then (1 : ℚ) else 0) • 1

def scalarTag {m d : ℕ} : Factor m d → Option Bool
  | .inl (.inl _) => some false
  | .inl (.inr _) => some true
  | .inr _ => none

lemma shifted_quad (m d : ℕ) (j : Degree d) :
    shiftedLetter m d (.inr (.inl j)) = (QuadraticAlgebra.omega : Quad j.val) := by
  change quadLetter j.val - 1 = _
  simp [quadLetter]

lemma shifted_matrix (m d : ℕ) (j : Degree d) (H : ActiveSubmodule m j.val) :
    shiftedLetter m d (.inr (.inr ⟨j,H⟩)) = starEdges (labelSize j.val H.val) := by
  letI := labelsFintype j.val H.val
  change condensed j.val H.val 0 - 1 = _
  rw [condensed_zero, add_sub_cancel_left]

lemma label_nonempty {m j : ℕ} {H : Submodule F (Vec m)} (hH : 0 < Module.finrank F H) :
    Nonempty (Labels j H) := by
  have hne : H ≠ ⊥ := by intro h; rw [h, finrank_bot] at hH; omega
  obtain ⟨a, ha, ha0⟩ := H.ne_bot_iff.mp hne
  exact ⟨⟨a, ha, Or.inl ha0⟩⟩

lemma star_minus_scalar_ne_zero {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (s : C → ℚ) (q : ℚ) : starEdges s - q • (1 : Matrix (Option C) (Option C) ℚ) ≠ 0 := by
  obtain ⟨c⟩ := ‹Nonempty C›
  intro h
  have he := congrArg (fun x : Matrix (Option C) (Option C) ℚ => x (some c) none) h
  norm_num [starEdges, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at he

lemma star_ne_zero {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C] (s : C → ℚ) :
    starEdges s ≠ 0 := by simpa using star_minus_scalar_ne_zero s 0

lemma omega_minus_scalar_ne_zero (j : ℕ) (q : ℚ) :
    (QuadraticAlgebra.omega : Quad j) - q • 1 ≠ 0 := by
  intro h
  have he := congrArg QuadraticAlgebra.im h
  change (1 : ℚ) - q*0 = 0 at he
  norm_num at he

lemma omega_ne_zero (j : ℕ) : (QuadraticAlgebra.omega : Quad j) ≠ 0 := by
  simpa using omega_minus_scalar_ne_zero j 0

lemma scalarTest_zero {m d : ℕ} (t : Bool) (i : Factor m d) :
    scalarTest m d t i = 0 ↔ scalarTag i = some t := by
  rcases i with (c | c) | (j | ⟨j,H⟩)
  · change phase c 0 - 1 - (if t then (1 : ℚ) else 0) • 1 = 0 ↔ some false = some t
    cases t <;> norm_num [phase_zero, smul_eq_mul]
  · change letter c 0 - 1 - (if t then (1 : ℚ) else 0) • 1 = 0 ↔ some true = some t
    cases t <;> norm_num [letter_zero, smul_eq_mul]
  · simp only [scalarTest, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, shifted_quad, scalarTag]
    exact ⟨fun h => (omega_minus_scalar_ne_zero _ _ h).elim, fun h => by cases h⟩
  · simp only [scalarTest, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, shifted_matrix, scalarTag]
    letI := labelsFintype j.val H.val
    haveI := label_nonempty (j := j.val) H.property.1
    exact ⟨fun h => (star_minus_scalar_ne_zero _ _ h).elim, fun h => by cases h⟩

lemma starMass_strict : StrictMono starMass := by
  intro j k h
  unfold starMass
  exact sub_lt_sub_right (pow_lt_pow_right₀ (by norm_num) h) _

lemma omega_sq (j : ℕ) :
    (QuadraticAlgebra.omega : Quad j) * QuadraticAlgebra.omega = starMass j • 1 := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_add, zero_smul, add_zero]

lemma omega_cube (j : ℕ) :
    (QuadraticAlgebra.omega : Quad j) * QuadraticAlgebra.omega * QuadraticAlgebra.omega =
      starMass j • QuadraticAlgebra.omega := by
  rw [omega_sq, smul_mul_assoc, one_mul]

noncomputable def cubicTest (m d j : ℕ) : Model m d :=
  shiftedLetter m d * shiftedLetter m d * shiftedLetter m d - starMass j • shiftedLetter m d

noncomputable def squareTest (m d j : ℕ) : Model m d :=
  shiftedLetter m d * shiftedLetter m d - starMass j • 1

lemma cubicTest_quad {m d : ℕ} (k : ℕ) (j : Degree d) :
    cubicTest m d k (.inr (.inl j)) = 0 ↔ j.val = k := by
  simp only [cubicTest, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, shifted_quad]
  let e : Quad j.val := QuadraticAlgebra.omega
  change e*e*e - starMass k • e = 0 ↔ j.val = k
  have he : e*e*e = starMass j.val • e := omega_cube _
  rw [he, ← sub_smul, smul_eq_zero, or_iff_left (omega_ne_zero _), sub_eq_zero,
    starMass_strict.injective.eq_iff]

lemma cubicTest_matrix {m d : ℕ} (k : ℕ) (j : Degree d) (H : ActiveSubmodule m j.val) :
    cubicTest m d k (.inr (.inr ⟨j,H⟩)) = 0 ↔ j.val = k := by
  letI := labelsFintype j.val H.val
  haveI := label_nonempty (j := j.val) H.property.1
  simp only [cubicTest, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, shifted_matrix]
  let e := starEdges (labelSize j.val H.val)
  change e*e*e - starMass k • e = 0 ↔ j.val = k
  have he : e*e*e = starMass j.val • e := by
    change _ = ((2 : ℚ)^j.val - 1) • e
    rw [star_cube, sum_labelSize H.val H.property.2]
  rw [he, ← sub_smul, smul_eq_zero, or_iff_left (star_ne_zero _), sub_eq_zero,
    starMass_strict.injective.eq_iff]

lemma squareTest_quad {m d : ℕ} (j : Degree d) :
    squareTest m d j.val (.inr (.inl j)) = 0 := by
  simp only [squareTest, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, Pi.one_apply, shifted_quad]
  let e : Quad j.val := QuadraticAlgebra.omega
  change e*e - starMass j.val • (1 : Quad j.val) = (0 : Quad j.val)
  exact sub_eq_zero.mpr (omega_sq j.val)

lemma labels_two {m j : ℕ} {H : Submodule F (Vec m)} (hj : 2 ≤ j)
    (hH : 0 < Module.finrank F H) (hr : Module.finrank F H ≤ j) :
    Nontrivial (Labels j H) := by
  classical
  letI := labelsFintype j H
  have he := card_labels H hr
  rw [Fintype.card_option] at he
  apply Fintype.one_lt_card_iff_nontrivial.mp
  by_cases h : Module.finrank F H = j
  · have hp : (2 : ℕ)^2 ≤ 2^Module.finrank F H :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    simp only [h, ite_true, add_zero] at he hp
    omega
  · have hp : (2 : ℕ)^1 ≤ 2^Module.finrank F H :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hH
    simp only [h, ite_false, pow_one] at he hp
    omega

lemma squareTest_matrix {m d : ℕ} (k : ℕ) (j : Degree d) (H : ActiveSubmodule m j.val) :
    squareTest m d k (.inr (.inr ⟨j,H⟩)) ≠ 0 := by
  letI := labelsFintype j.val H.val
  haveI := labels_two (Finset.mem_Icc.mp j.property).1 H.property.1 H.property.2
  obtain ⟨c, b, hcb⟩ := exists_pair_ne (Labels j.val H.val)
  simp only [squareTest, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, Pi.one_apply, shifted_matrix]
  intro h
  let I := Option (Labels j.val H.val)
  let e : Matrix I I ℚ := starEdges (labelSize j.val H.val)
  change e*e - starMass k • 1 = 0 at h
  have he := congrArg (fun x : Matrix I I ℚ => x (some c) (some b)) h
  change (e*e - starMass k • 1) (some c) (some b) = 0 at he
  unfold e at he
  simp only [Matrix.sub_apply, star_sq_apply, Matrix.smul_apply, Matrix.one_apply, Option.some.injEq,
    hcb, ite_false, smul_zero, sub_zero, Matrix.zero_apply] at he
  have he' : (starEdges (labelSize j.val H.val) * starEdges (labelSize j.val H.val))
      (some c) (some b) = labelSize j.val H.val b :=
    star_sq_apply (labelSize j.val H.val) (some c) (some b)
  exact (labelSize_pos H.val H.property.2 b).ne' (he'.symm.trans he)

lemma letter_separates {m : ℕ} {b c : Vec m} (h : b ≠ c) :
    ∃ a, letter b a ≠ letter c a := by
  simpa only [oneLetter, Option.elim_some] using oneLetter_sep (some b) (some c) (by simpa)

lemma phase_separates {m : ℕ} {b c : Vec m} (h : b ≠ c) :
    ∃ a, phase b a ≠ phase c a := by
  obtain ⟨a, ha⟩ := letter_separates h
  refine ⟨a, fun he => ha ?_⟩
  simpa [letter, phase, dot_comm a] using congrArg (fun q : ℚ => 1+q) he

set_option maxHeartbeats 900000 in
lemma model_separates (m d : ℕ) (i j : Factor m d) (hij : i ≠ j) :
    ∃ x ∈ Algebra.adjoin ℚ (Set.range (modelLetter m d)),
      (x i ≠ 0 ∧ x j = 0) ∨ (x i = 0 ∧ x j ≠ 0) := by
  classical
  let R := Algebra.adjoin ℚ (Set.range (modelLetter m d))
  have hm (a : Vec m) : modelLetter m d a ∈ R := Algebra.subset_adjoin (Set.mem_range_self a)
  have hshift : shiftedLetter m d ∈ R := R.sub_mem (hm 0) R.one_mem
  have hscalar (t : Bool) : scalarTest m d t ∈ R :=
    R.sub_mem hshift (R.smul_mem R.one_mem _)
  have hcubic (t : ℕ) : cubicTest m d t ∈ R :=
    R.sub_mem (R.mul_mem (R.mul_mem hshift hshift) hshift) (R.smul_mem hshift _)
  have hsquare (t : ℕ) : squareTest m d t ∈ R :=
    R.sub_mem (R.mul_mem hshift hshift) (R.smul_mem R.one_mem _)
  by_contra hn
  have he (x : Model m d) (hx : x ∈ R) : x i = 0 ↔ x j = 0 := by
    constructor
    · intro hi
      by_contra hj
      exact hn ⟨x, hx, Or.inr ⟨hi, hj⟩⟩
    · intro hj
      by_contra hi
      exact hn ⟨x, hx, Or.inl ⟨hi, hj⟩⟩
  have ht (t : Bool) : scalarTag i = some t ↔ scalarTag j = some t :=
    (scalarTest_zero t i).symm.trans ((he _ (hscalar t)).trans (scalarTest_zero t j))
  have htag : scalarTag i = scalarTag j := by
    cases hi : scalarTag i with
    | none =>
      cases hj : scalarTag j with
      | none => rfl
      | some t =>
        have h : (none : Option Bool) = some t := hi.symm.trans ((ht t).2 hj)
        cases h
    | some t => exact ((ht t).1 hi).symm
  rcases i with (b | b) | (t | ⟨t,H⟩) <;>
    rcases j with (c | c) | (s | ⟨s,K⟩) <;> simp [scalarTag] at htag
  · have hbc : b ≠ c := fun h => hij (by subst c; rfl)
    obtain ⟨a, ha⟩ := phase_separates hbc
    let x := modelLetter m d a - phase b a • (1 : Model m d)
    have hx : x ∈ R := R.sub_mem (hm a) (R.smul_mem R.one_mem _)
    have h0 : x (.inl (.inl b)) = 0 := by change phase b a - phase b a • (1 : ℚ) = 0; simp
    have h := (he x hx).1 h0
    change phase c a - phase b a • (1 : ℚ) = 0 at h
    exact ha (sub_eq_zero.mp (by simpa using h)).symm
  · have hbc : b ≠ c := fun h => hij (by subst c; rfl)
    obtain ⟨a, ha⟩ := letter_separates hbc
    let x := modelLetter m d a - letter b a • (1 : Model m d)
    have hx : x ∈ R := R.sub_mem (hm a) (R.smul_mem R.one_mem _)
    have h0 : x (.inl (.inr b)) = 0 := by change letter b a - letter b a • (1 : ℚ) = 0; simp
    have h := (he x hx).1 h0
    change letter c a - letter b a • (1 : ℚ) = 0 at h
    exact ha (sub_eq_zero.mp (by simpa using h)).symm
  · have h := (cubicTest_quad (m := m) t.val s).mp
      ((he _ (hcubic t.val)).1 ((cubicTest_quad t.val t).mpr rfl))
    have hs : s = t := Subtype.ext h
    exact hij (by subst s; rfl)
  · exact squareTest_matrix t.val s K ((he _ (hsquare t.val)).1 (squareTest_quad t))
  · exact squareTest_matrix s.val t H ((he _ (hsquare s.val)).2 (squareTest_quad s))
  · have h := (cubicTest_matrix t.val s K).mp
      ((he _ (hcubic t.val)).1 ((cubicTest_matrix t.val t H).mpr rfl))
    have hs : s = t := Subtype.ext h
    subst s
    have hj := (Finset.mem_Icc.mp t.property).1
    have hk : annihilatorEquiv m H.val = annihilatorEquiv m K.val := by
      ext a
      rw [← condensed_eq_zeroLetter H.val hj H.property.2,
        ← condensed_eq_zeroLetter K.val hj K.property.2]
      have hab := he (modelLetter m d a - modelLetter m d 0) (R.sub_mem (hm a) (hm 0))
      change condensed t.val H.val a - condensed t.val H.val 0 = 0 ↔
        condensed t.val K.val a - condensed t.val K.val 0 = 0 at hab
      simpa only [sub_eq_zero] using hab
    have heq : H = K := Subtype.ext ((annihilatorEquiv m).injective hk)
    exact hij (by subst K; rfl)

lemma model_adjoin (m d : ℕ) :
    Algebra.adjoin ℚ (Set.range (modelLetter m d)) = ⊤ := by
  letI := factorFintype m d
  letI : ∀ i : Factor m d, IsSimpleRing (factorAlg m d i) := factor_simple m d
  exact adjoin_of_simple_factors (modelLetter m d) (Pi.evalAlgHom ℚ _)
    (fun x y h => funext h) (eval_factor_adjoin m d) (model_separates m d)

noncomputable def condensedTrace {m : ℕ} (j : ℕ) (H : Submodule F (Vec m))
    (w : List (Vec m)) : ℚ :=
  letI := labelsFintype j H
  Matrix.trace (wordProd (condensed j H) w)

noncomputable def transferMean {m : ℕ} (j : ℕ) (w : List (Vec m)) : ℚ :=
  columnMean m j (fun b => Matrix.trace (wordProd (transfer b) w))

lemma transferMean_count {m : ℕ} (j : ℕ) (w : List (Vec m)) (hw : 0 < w.length) :
    transferMean j w = mapCount j w := by
  rw [transferMean, columnMean_apply, mapCount_fourier j w hw]
  simp [inverseAlphabet, inv_pow]

lemma transferMean_empty (m j : ℕ) : transferMean j ([] : List (Vec m)) = (2 : ℚ)^j := by
  have h (b : Fin j → Vec m) :
      Matrix.trace (wordProd (transfer b) ([] : List (Vec m))) = (2 : ℚ)^j := by
    simp [wordProd, Matrix.trace_one, card_vec]
  unfold transferMean
  simp_rw [h]
  exact columnMean_const m j _

lemma columnMean_ranges {m : ℕ} (j : ℕ) (g : Submodule F (Vec m) → ℚ) :
    letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
    columnMean m j (fun b => g (syndrome b).range) = ∑ H, imageMass j H * g H := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  let e := (transposeEquiv m j).symm
  have h := e.sum_comp (fun b => g (syndrome b).range)
  change (∑ f : Fin m → Vec j, g (rowMap f).range) = ∑ b : Fin j → Vec m, g (syndrome b).range at h
  rw [columnMean_apply, ← h, ← Finset.sum_fiberwise' (Finset.univ : Finset (Fin m → Vec j))
     (fun f => (rowMap f).range) g, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_const, nsmul_eq_mul, imageMass, ← card_row_range,
    Nat.card_eq_fintype_card, Fintype.card_subtype, mul_assoc]

lemma transferMean_decompose {m : ℕ} (j : ℕ) (w : List (Vec m)) :
    letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
    transferMean j w =
      (∑ H : Submodule F (Vec m), imageMass j H * condensedTrace j H w) +
      ∑ c : Vec m, columnMean m j (fun b => residual (syndrome b) c) * wordProd (phase c) w := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  have ht (b : Fin j → Vec m) :
      Matrix.trace (wordProd (transfer b) w) =
        condensedTrace j (syndrome b).range w +
          ∑ c : Vec m, residual (syndrome b) c * wordProd (phase c) w := transfer_residual b w
  unfold transferMean
  simp_rw [ht]
  change columnMean m j ((fun b => condensedTrace j (syndrome b).range w) +
    (fun b => ∑ c : Vec m, residual (syndrome b) c * wordProd (phase c) w)) = _
  rw [map_add, columnMean_ranges j (fun H => condensedTrace j H w)]
  congr 1
  rw [columnMean_apply, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul, columnMean_apply, mul_assoc]

lemma imageMass_vanish {m j : ℕ} {H : Submodule F (Vec m)}
    (h : j < Module.finrank F H) : imageMass j H = 0 := by
  simp [imageMass, weightPoly_root h]

lemma sum_active {m j : ℕ} (g : Submodule F (Vec m) → ℚ)
    (hg : ∀ H : Submodule F (Vec m), j < Module.finrank F H → g H = 0) :
    letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
    letI := activeFintype m j
    ∑ H, g H = g ⊥ + ∑ H : ActiveSubmodule m j, g H.val := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  letI := activeFintype m j
  let s := (Finset.univ : Finset (Submodule F (Vec m))).filter
    (fun (H : Submodule F (Vec m)) => 0 < Module.finrank F H ∧ Module.finrank F H ≤ j)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule F (Vec m)))]
  congr 1
  rw [← Finset.sum_subtype s (by simp [s]) g]
  symm
  apply Finset.sum_subset
  · intro H hH
    have hp := (Finset.mem_filter.mp hH).2.1
    exact Finset.mem_erase.mpr ⟨fun he => by rw [he, finrank_bot] at hp; omega, Finset.mem_univ _⟩
  · intro H hH hn
    have h0 : Module.finrank F H ≠ 0 := fun h => (Finset.mem_erase.mp hH).1 (Submodule.finrank_eq_zero.mp h)
    have hlt : j < Module.finrank F H := by
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by omega⟩)
    exact hg H hlt

lemma interval_sum_zero_one {R : Type*} [AddCommMonoid R] {d : ℕ} (hd : 2 ≤ d) (f : ℕ → R) :
    (∑ j ∈ Finset.range (d+1), f j) = f 0 + f 1 + ∑ j ∈ Finset.Icc 2 d, f j := by
  let s := Finset.range (d+1)
  have h0 : 0 ∈ s := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ s.erase 0 := Finset.mem_erase.mpr ⟨by decide, Finset.mem_range.mpr (by omega)⟩
  have hs : (s.erase 0).erase 1 = Finset.Icc 2 d := by
    ext t
    simp only [s, Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  change (∑ j ∈ s, f j) = _
  rw [← Finset.add_sum_erase s f h0, ← Finset.add_sum_erase (s.erase 0) f h1, hs, add_assoc]

lemma scalarTrace_expand {m d : ℕ} (hd : 2 ≤ d) (w : List (Vec m)) :
    (∑ c : Vec m, scalarWeight d c * wordProd (phase c) w) =
      (weightPoly d).coeff 0 +
        ∑ j ∈ Finset.Icc 2 d, (weightPoly d).coeff j *
          (∑ c : Vec m, columnMean m j (fun b => residual (syndrome b) c) * wordProd (phase c) w) := by
  classical
  unfold scalarWeight
  rw [Finset.sum_congr rfl (fun i _ => add_mul _ _ _), Finset.sum_add_distrib]
  have hf : phase (0 : Vec m) = fun _ => (1 : ℚ) := by
    funext a
    simp [phase, dot, sign]
  have h0 : wordProd (phase (0 : Vec m)) w = 1 := by simp [wordProd, hf]
  have h : (∑ c : Vec m, (weightPoly d).coeff 0 * bit (c = 0) * wordProd (phase c) w) =
    (weightPoly d).coeff 0 := by
    rw [Finset.sum_eq_single (0 : Vec m)]
    · simp [bit, h0]
    · intro c _ hc
      simp [bit, hc]
    · simp
  rw [h]
  congr 1
  simp_rw [coeffExtract_apply, Finset.sum_mul]
  rw [Finset.sum_comm, interval_sum_zero_one hd]
  have hz (j : ℕ) (hj : j ≤ 1) (c : Vec m) :
      columnMean m j (fun b => residual (syndrome b) c) = 0 := by
    simp_rw [residual_small hj]
    exact columnMean_const m j 0
  simp only [hz 0 (by decide), hz 1 (by decide), mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma modelTrace_blocks {m d : ℕ} (w : List (Vec m)) :
    letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
    modelTrace m d (wordProd (modelLetter m d) w) =
      (∑ c : Vec m, scalarWeight d c * wordProd (phase c) w) +
      ((weightPoly d).coeff 1 * inverseAlphabet m) * (∑ c : Vec m, wordProd (letter c) w) +
      ∑ j ∈ Finset.Icc 2 d, (weightPoly d).coeff j *
        ∑ H : Submodule F (Vec m), imageMass j H * condensedTrace j H w := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  letI : ∀ j : Degree d, Fintype (ActiveSubmodule m j.val) := fun j => activeFintype m j.val
  letI := factorFintype m d
  rw [modelTrace_apply, sum_factors]
  simp_rw [word_model_apply]
  let s₁ := (∑ c : Vec m, scalarWeight d c * wordProd (phase c) w)
  let s₂ := ((weightPoly d).coeff 1 * inverseAlphabet m) * (∑ c : Vec m, wordProd (letter c) w)
  let b₁ (j : Degree d) : ℚ := (weightPoly d).coeff j.val *
    imageMass j.val (⊥ : Submodule F (Vec m)) *
      quadTrace j.val (wordProd (fun _ : Vec m => quadLetter j.val) w)
  let b₂ (j : Degree d) : ℚ := ∑ H : ActiveSubmodule m j.val,
    (weightPoly d).coeff j.val * imageMass j.val H.val * condensedTrace j.val H.val w
  change (s₁ + (∑ c : Vec m, ((weightPoly d).coeff 1 * inverseAlphabet m) *
      wordProd (letter c) w)) + ((∑ j, b₁ j) + ∑ j, b₂ j) = _
  rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  change s₁ + s₂ + _ = s₁ + s₂ + _
  congr 1
  let g (j : ℕ) := (weightPoly d).coeff j *
    ∑ H : Submodule F (Vec m), imageMass j H * condensedTrace j H w
  change Finset.univ.sum (fun t : Degree d => b₁ t + b₂ t) = (Finset.Icc 2 d).sum g
  rw [← Finset.sum_coe_sort (Finset.Icc 2 d) g]
  apply Finset.sum_congr rfl
  intro j _
  unfold b₁ b₂ g
  rw [← condensed_bot_trace (Finset.mem_Icc.mp j.property).1 w]
  change _ * _ * condensedTrace j.val ⊥ w + _ = _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [← mul_add, ← sum_active (j := j.val)
    (fun H => imageMass j.val H * condensedTrace j.val H w)
    (fun H h => by simp [imageMass_vanish h])]

lemma modelTrace_transfer {m d : ℕ} (hd : 2 ≤ d) (w : List (Vec m)) :
    modelTrace m d (wordProd (modelLetter m d) w) =
      (weightPoly d).coeff 0 +
      ((weightPoly d).coeff 1 * inverseAlphabet m) * (∑ c : Vec m, wordProd (letter c) w) +
      ∑ j ∈ Finset.Icc 2 d, (weightPoly d).coeff j * transferMean j w := by
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  rw [modelTrace_blocks, scalarTrace_expand hd]
  simp_rw [transferMean_decompose, mul_add, Finset.sum_add_distrib]
  abel

lemma modelTrace_matches {m d : ℕ} (hd : 2 ≤ d) (w : List (Vec m)) (hw : 0 < w.length) :
    modelTrace m d (wordProd (modelLetter m d) w) =
      (weightPoly d).eval ((2 : ℚ)^d) * count d w := by
  rw [← count_extract, interval_sum_zero_one hd, modelTrace_transfer hd, mapCount_zero, mapCount_one]
  simp_rw [transferMean_count _ w hw, mul_one, inverseAlphabet, inv_pow, mul_assoc]

lemma modelTrace_empty {m d : ℕ} (hd : 2 ≤ d) :
    modelTrace m d 1 = -(weightPoly d).coeff 1 := by
  have h := modelTrace_transfer (m := m) hd []
  simp_rw [transferMean_empty, wordProd, List.map_nil, List.prod_nil, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hc : (Fintype.card (Vec m) : ℚ) = (2 : ℚ)^m := by simp [card_vec]
  rw [hc, mul_assoc, show inverseAlphabet m * (2 : ℚ)^m = 1 from inv_mul_cancel₀ (by positivity),
    mul_one] at h
  have h₀ : coeffExtract d (fun j => (2 : ℚ)^j) = 0 := by
    rw [coeffExtract_pow]
    simpa only [pow_one] using weightPoly_root (i := 1) (by omega : 1 < d)
  rw [coeffExtract_apply, interval_sum_zero_one hd, pow_zero, pow_one, mul_one] at h₀
  rw [h]
  linarith

def blockCard (r j : ℕ) : ℕ := (2^r + (if r = j then 0 else 1))^2

noncomputable def rankBlockAt (m j : ℕ) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  ∑ H : Submodule F (Vec m),
    let r := Module.finrank F H
    if r = 0 ∨ j < r then 0 else (2^r + (if r = j then 0 else 1))^2

noncomputable def rankBlocks (m d : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 2 d, rankBlockAt m j

noncomputable def postedBlocks (m d : ℕ) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  ∑ j ∈ Finset.Icc 2 d, ∑ D : Submodule F (Vec m),
    let r := m - Module.finrank F D
    if r = 0 ∨ j < r then 0 else (2^r + (if r = j then 0 else 1))^2

lemma postedBlocks_eq_rankBlocks (m d : ℕ) : postedBlocks m d = rankBlocks m d := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  unfold postedBlocks rankBlocks rankBlockAt
  apply Finset.sum_congr rfl
  intro j _
  let f (D : Submodule F (Vec m)) : ℕ :=
    let r := m - Module.finrank F D
    if r = 0 ∨ j < r then 0 else (2^r + (if r = j then 0 else 1))^2
  change (∑ D : Submodule F (Vec m), f D) = _
  rw [← (annihilatorEquiv m).sum_comp f]
  apply Finset.sum_congr rfl
  intro H _
  have hr : Module.finrank F H ≤ m := by
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le H
  have h : m - Module.finrank F (annihilatorEquiv m H) = Module.finrank F H := by
    rw [finrank_annihilator]
    exact Nat.sub_sub_self hr
  dsimp only [f]
  rw [h]

noncomputable def postedPos (m d : ℕ) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if d = 0 then 1 else if d = 1 then 2^m + 1 else
    2*2^m + 2*(d-1) + postedBlocks m d

lemma active_card_sum (m j : ℕ) :
    letI := activeFintype m j
    (∑ H : ActiveSubmodule m j, blockCard (Module.finrank F H.val) j) =
      rankBlockAt m j := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  letI := activeFintype m j
  let s := (Finset.univ : Finset (Submodule F (Vec m))).filter
    (fun (H : Submodule F (Vec m)) => 0 < Module.finrank F H ∧ Module.finrank F H ≤ j)
  let f (H : Submodule F (Vec m)) : ℕ := blockCard (Module.finrank F H) j
  change (∑ H : ActiveSubmodule m j, f H.val) = _
  rw [← Finset.sum_subtype s (by simp [s]) f]
  unfold s rankBlockAt
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro H _
  dsimp only
  have he : (¬(Module.finrank F H = 0 ∨ j < Module.finrank F H)) ↔
      (0 < Module.finrank F H ∧ Module.finrank F H ≤ j) := by omega
  by_cases h : Module.finrank F H = 0 ∨ j < Module.finrank F H
  · rw [if_neg (fun hh => he.mpr hh h), if_pos h]
  · rw [if_pos (he.mp h), if_neg h]
    unfold f blockCard
    by_cases hh : Module.finrank F H = j <;> simp only [hh, ite_true, ite_false]

lemma matrixFactor_finrank (m d : ℕ) (j : Degree d) (H : ActiveSubmodule m j.val) :
    Module.finrank ℚ (factorAlg m d (.inr (.inr ⟨j,H⟩))) =
      blockCard (Module.finrank F H.val) j.val := by
  classical
  letI := labelsFintype j.val H.val
  let I := Option (Labels j.val H.val)
  change Module.finrank ℚ (Matrix I I ℚ) = _
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, card_labels H.val H.property.2,
    blockCard, pow_two]

lemma model_finrank (m d : ℕ) (hd : 2 ≤ d) :
    Module.finrank ℚ (Model m d) = postedPos m d := by
  classical
  letI : ∀ j : Degree d, Fintype (ActiveSubmodule m j.val) := fun j => activeFintype m j.val
  letI := factorFintype m d
  letI : ∀ i : Factor m d, Module.Finite ℚ (factorAlg m d i) := factor_finite m d
  have hs (b : Vec m ⊕ Vec m) : Module.finrank ℚ (factorAlg m d (.inl b)) = 1 :=
    Module.finrank_self ℚ
  have hq (j : Degree d) : Module.finrank ℚ (factorAlg m d (.inr (.inl j))) = 2 :=
    QuadraticAlgebra.finrank_eq_two _ _
  rw [Module.finrank_pi_fintype, sum_factors]
  simp_rw [hs, hq, matrixFactor_finrank, active_card_sum]
  unfold postedPos
  rw [if_neg (by omega : d ≠ 0), if_neg (by omega : d ≠ 1), postedBlocks_eq_rankBlocks]
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, mul_one, card_vec]
  have he : Fintype.card (Degree d) = d - 1 := by simp [Degree, Nat.card_Icc]
  rw [he]
  have hb : (∑ j : Degree d, rankBlockAt m j.val) = rankBlocks m d :=
    Finset.sum_coe_sort (Finset.Icc 2 d) (rankBlockAt m)
  rw [hb]
  ring

lemma wordProd_nil {A V : Type*} [Monoid V] (M : A → V) : wordProd M [] = 1 := rfl

lemma wordProd_cons {A V : Type*} [Monoid V] (M : A → V) (a : A) (w : List A) :
    wordProd M (a :: w) = M a * wordProd M w := rfl

lemma exact_dimensions_with_empty {A V : Type*} [Ring V] [Algebra ℚ V]
    [FiniteDimensional ℚ V] (M : A → V) (L : V →ₗ[ℚ] ℚ) (g : List A → ℚ) (k : ℕ)
    (hspan : Submodule.span ℚ (Set.range (fun w : {w : List A // 0 < w.length} =>
      wordProd M w.val)) = ⊤)
    (hn : ∀ x, (∀ y, L (x*y) = 0) → x = 0)
    (hg : ∀ w, 0 < w.length → L (wordProd M w) = g w)
    (h0 : g [] ≠ L 1) :
    (Fits g k (fun w => 0 < w.length) ↔ Module.finrank ℚ V ≤ k) ∧
      (Fits g k (fun _ => True) ↔ Module.finrank ℚ V + 1 ≤ k) := by
  constructor
  · constructor
    · apply fits_lower (wordProd M) (productPair L) (P := fun w => 0 < w.length)
      · intro p q hp hq
        simp only [List.length_append]
        omega
      · exact hn
      · exact hspan
      · intro p q hp hq
        rw [← hg _ (by simp only [List.length_append]; omega), wordProd_append]
        rfl
    · exact fun hk => fits_alg M L hk hg
  · let e := g [] - L 1
    have he : e ≠ 0 := sub_ne_zero.mpr h0
    let N : A → V × ℚ := fun a => (M a, 0)
    let K : V × ℚ →ₗ[ℚ] ℚ :=
      L.comp (LinearMap.fst ℚ V ℚ) + e • LinearMap.snd ℚ V ℚ
    have hs (w : List A) (hw : 0 < w.length) : wordProd N w = (wordProd M w, 0) := by
      cases w with
      | nil => simp at hw
      | cons a w =>
        apply Prod.ext
        · have h := wordProd_hom N (MonoidHom.fst V ℚ) (a :: w)
          exact h.symm
        · simp [wordProd_cons, N]
    have hK (w : List A) : K (wordProd N w) = g w := by
      cases w with
      | nil =>
        rw [wordProd_nil]
        change L 1 + e * 1 = g []
        unfold e
        ring
      | cons a w =>
        rw [hs _ (by simp)]
        change L (wordProd M (a :: w)) + e * 0 = g (a :: w)
        rw [mul_zero, add_zero, hg _ (by simp)]
    have hSpan : Submodule.span ℚ (Set.range (fun w : {w : List A // True} => wordProd N w.val)) = ⊤ := by
      let S := Submodule.span ℚ (Set.range (fun w : {w : List A // True} => wordProd N w.val))
      have h_inl : ∀ x : V, (x, (0 : ℚ)) ∈ S := by
        have hle : Submodule.span ℚ (Set.range (fun w : {w : List A // 0 < w.length} =>
            wordProd M w.val)) ≤ S.comap (LinearMap.inl ℚ V ℚ) := by
          rw [Submodule.span_le]
          rintro _ ⟨w, rfl⟩
          change (wordProd M w.val, (0 : ℚ)) ∈ S
          rw [← hs w.val w.property]
          exact Submodule.subset_span ⟨⟨w.val, trivial⟩, rfl⟩
        intro x
        exact hle (by rw [hspan]; trivial)
      have hon : (1 : V × ℚ) ∈ S := Submodule.subset_span ⟨⟨[], trivial⟩, rfl⟩
      have h_inr : ((0 : V), (1 : ℚ)) ∈ S := by
        have h := S.sub_mem hon (h_inl 1)
        have he : (1 : V × ℚ) - (1,0) = (0,1) := by
          change (1-1, 1-0) = (0,1)
          simp
        exact he ▸ h
      apply top_unique
      rintro ⟨x,y⟩ _
      change (x,y) ∈ S
      convert S.add_mem (h_inl x) (S.smul_mem y h_inr) using 1
      ext <;> simp
    have hN (x : V × ℚ) (h : ∀ y, productPair K x y = 0) : x = 0 := by
      rcases x with ⟨x,z⟩
      have hx : x = 0 := by
        apply hn
        intro y
        have he := h (y,0)
        change L (x*y) + e*(z*0) = 0 at he
        simpa using he
      have hz := h (0,1)
      change L (x*0) + e*(z*1) = 0 at hz
      simp only [mul_zero, map_zero, zero_add, mul_one] at hz
      exact Prod.ext hx ((mul_eq_zero.mp hz).resolve_left he)
    have hc : Module.finrank ℚ (V × ℚ) = Module.finrank ℚ V + 1 := by
      rw [Module.finrank_prod, Module.finrank_self]
    rw [← hc]
    constructor
    · apply fits_lower (wordProd N) (productPair K) (P := fun _ => True)
      · simp
      · exact hN
      · exact hSpan
      · intro p q _ _
        rw [← hK, wordProd_append]
        rfl
    · exact fun hk => fits_alg N K hk (fun w _ => hK w)

lemma solve_high (m d k : ℕ) (hd : 2 ≤ d) :
    (Fits (count (m := m) d) k (fun w => 0 < w.length) ↔ postedPos m d ≤ k) ∧
    (Fits (count (m := m) d) k (fun _ => True) ↔ postedPos m d + 1 ≤ k) := by
  letI := factorFintype m d
  letI : ∀ i : Factor m d, Module.Finite ℚ (factorAlg m d i) := factor_finite m d
  let M := modelLetter m d
  let q := (weightPoly d).eval ((2 : ℚ)^d)
  have hq : 0 < q := weightPoly_top d
  let L : Model m d →ₗ[ℚ] ℚ := q⁻¹ • modelTrace m d
  have hspan := pos_word_span M 0 (modelLetter_zero_unit m d) (model_adjoin m d)
  have hn (x : Model m d) (h : ∀ y, L (x*y) = 0) : x = 0 := by
    apply modelTrace_pair hd
    intro y
    exact (mul_eq_zero.mp (h y)).resolve_left (inv_ne_zero hq.ne')
  have hw (w : List (Vec m)) (hw : 0 < w.length) : L (wordProd M w) = count d w := by
    change q⁻¹ * modelTrace m d (wordProd M w) = count d w
    rw [modelTrace_matches hd w hw, ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
  have he : count (m := m) d [] ≠ L 1 := by
    rw [count_empty (by omega)]
    symm
    change q⁻¹ * modelTrace m d 1 ≠ 0
    rw [modelTrace_empty hd]
    exact mul_ne_zero (inv_ne_zero hq.ne') (neg_ne_zero.mpr (weight_coeff_ne_zero (by omega)))
  simpa only [model_finrank m d hd] using exact_dimensions_with_empty M L _ k hspan hn hw he

def FitsWithEq {A : Type*} (g : List A → ℚ) (k : ℕ)
    (T : List A → Prop) (eq : DecidableEq (Fin k)) : Prop :=
  letI := eq
  ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
    ∀ w : List A, T w →
      (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) = g w

def ClassicalFits {A : Type*} (g : List A → ℚ) (k : ℕ) (T : List A → Prop) : Prop :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
    ∀ w : List A, T w →
      (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) = g w

lemma ClassicalFits_iff {A : Type*} (g : List A → ℚ) (k : ℕ) (T : List A → Prop) :
    ClassicalFits g k T ↔ Fits g k T := by
  change FitsWithEq g k T (fun a b => Classical.propDecidable (a=b)) ↔
    FitsWithEq g k T (inferInstance : DecidableEq (Fin k))
  have h : (fun a b : Fin k => Classical.propDecidable (a=b)) =
      (inferInstance : DecidableEq (Fin k)) := Subsingleton.elim _ _
  rw [h]

end PEqualNP.Outside.L_lib_833


set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_lib_833 : ∀ (m d : ℕ),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  let count := fun w : List A =>
    let W := Fin w.length → F
    letI : Fintype (Submodule F W) := Fintype.ofFinite _
    let next := fun i : Fin w.length =>
      (⟨(i.val+1) % w.length, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ : Fin w.length)
    let good := (Finset.univ : Finset (Submodule F W)).filter (fun (U : Submodule F W) =>
      Module.finrank F U = d ∧
      (∀ x ∈ U, ∀ a : Fin m, (∑ i, w.get i a * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i))
    (good.card : ℚ)
  let fits := fun (k : ℕ) (test : List A → Prop) =>
    ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
      ∀ w : List A, test w →
        (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = count w
  let blocks : ℕ := ∑ j ∈ Finset.Icc 2 d, ∑ D : Submodule F A,
    let r := m - Module.finrank F D
    if r = 0 ∨ j < r then 0 else (2^r + (if r = j then 0 else 1))^2
  let pos : ℕ := if d = 0 then 1 else if d = 1 then 2^m+1
    else 2*2^m + 2*(d-1) + blocks
  ∀ k : ℕ, (fits k (fun w => 0 < w.length) ↔ pos ≤ k) ∧
    (fits k (fun _ => True) ↔ pos + (if 2 ≤ d then 1 else 0) ≤ k) := by
  intro m d
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  change ∀ k : ℕ,
    (PEqualNP.Outside.L_lib_833.ClassicalFits (PEqualNP.Outside.L_lib_833.count (m := m) d) k
      (fun w => 0 < w.length) ↔ PEqualNP.Outside.L_lib_833.postedPos m d ≤ k) ∧
    (PEqualNP.Outside.L_lib_833.ClassicalFits (PEqualNP.Outside.L_lib_833.count (m := m) d) k
      (fun _ => True) ↔ PEqualNP.Outside.L_lib_833.postedPos m d + (if 2 ≤ d then 1 else 0) ≤ k)
  intro k
  rw [PEqualNP.Outside.L_lib_833.ClassicalFits_iff, PEqualNP.Outside.L_lib_833.ClassicalFits_iff]
  rcases d with _ | d
  · simpa [PEqualNP.Outside.L_lib_833.postedPos] using PEqualNP.Outside.L_lib_833.solve_zero m k
  rcases d with _ | d
  · simpa [PEqualNP.Outside.L_lib_833.postedPos] using PEqualNP.Outside.L_lib_833.solve_one m k
  · have h : 2 ≤ d+1+1 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d))
    rw [if_pos h]
    exact PEqualNP.Outside.L_lib_833.solve_high m (d+1+1) k h
