import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30643_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

abbrev F := ZMod 2

/-! ## Section 1: `ZMod 2` arithmetic, finite differences, cubics, quadratics, and `wedge3` -/

private lemma f_add_self (x : F) : x + x = 0 := by revert x; decide
private lemma f_sub_eq_add (x y : F) : x - y = x + y := by revert x y; decide
private lemma f_mul_self (x : F) : x * x = x := by revert x; decide
private lemma f_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by revert x; decide
private lemma f_ne_zero_iff (x : F) : x ≠ 0 ↔ x = 1 := by revert x; decide
private lemma f_neg (x : F) : -x = x := by revert x; decide

private def unitF {n : ℕ} (i : Fin n) : Fin n → F :=
  fun j => if i = j then 1 else 0

private lemma vec_add_self {n : ℕ} (x : Fin n → F) : x + x = 0 := by
  funext i; exact f_add_self (x i)

private lemma vec_eq_sum_unit {n : ℕ} (x : Fin n → F) :
    x = ∑ i : Fin n, x i • unitF i := by
  funext j
  simp [unitF, Finset.sum_apply]

private def diffF {n : ℕ} (g : (Fin n → F) → F) (a x : Fin n → F) : F :=
  g (x + a) - g x

private def thirdF {n : ℕ} (g : (Fin n → F) → F) (a b c : Fin n → F) : F :=
  diffF (diffF (diffF g a) b) c 0

private def isCubic {n : ℕ} (g : (Fin n → F) → F) : Prop :=
  ∀ a b c d x, diffF (diffF (diffF (diffF g a) b) c) d x = 0

private def isQuad {n : ℕ} (q : (Fin n → F) → F) : Prop :=
  ∀ a b c x, diffF (diffF (diffF q a) b) c x = 0

private def isAff {n : ℕ} (l : (Fin n → F) → F) : Prop :=
  ∀ a b x, diffF (diffF l a) b x = 0

private lemma diffF_eq_add {n : ℕ} (g : (Fin n → F) → F) (a x : Fin n → F) :
    diffF g a x = g (x + a) + g x := by
  unfold diffF; exact f_sub_eq_add _ _

private lemma diffF_zero {n : ℕ} (g : (Fin n → F) → F) (x : Fin n → F) :
    diffF g 0 x = 0 := by
  simp [diffF]

private lemma diffF_const {n : ℕ} (c : F) (a x : Fin n → F) :
    diffF (fun _ => c) a x = 0 := by
  simp [diffF]

private lemma diffF_add_fun {n : ℕ} (f g : (Fin n → F) → F) (a x : Fin n → F) :
    diffF (fun y => f y + g y) a x = diffF f a x + diffF g a x := by
  simp only [diffF_eq_add]; ring

private lemma diffF_sub_fun {n : ℕ} (f g : (Fin n → F) → F) (a x : Fin n → F) :
    diffF (fun y => f y - g y) a x = diffF f a x - diffF g a x := by
  simp only [diffF]; ring

private lemma diffF_smul_fun {n : ℕ} (c : F) (f : (Fin n → F) → F) (a x : Fin n → F) :
    diffF (fun y => c * f y) a x = c * diffF f a x := by
  simp only [diffF_eq_add]; ring

private lemma diffF_sum_fun {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n → F) → F) (a x : Fin n → F) :
    diffF (fun y => ∑ i ∈ s, f i y) a x = ∑ i ∈ s, diffF (f i) a x := by
  classical
  induction s using Finset.induction with
  | empty => simp [diffF]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [diffF_add_fun, ih]

private lemma diffF_comm {n : ℕ} (g : (Fin n → F) → F) (a b x : Fin n → F) :
    diffF (diffF g a) b x = diffF (diffF g b) a x := by
  simp only [diffF_eq_add]
  have h : x + b + a = x + a + b := by abel
  rw [h]; ring

private lemma diffF_self {n : ℕ} (g : (Fin n → F) → F) (a x : Fin n → F) :
    diffF (diffF g a) a x = 0 := by
  simp only [diffF_eq_add, add_assoc, vec_add_self, add_zero]
  ring_nf; simp [show (2 : F) = 0 by decide]

private lemma diffF_add_dir {n : ℕ} (g : (Fin n → F) → F) (a a' x : Fin n → F) :
    diffF g (a + a') x = diffF g a' (x + a) + diffF g a x := by
  simp only [diffF_eq_add, add_assoc]
  ring_nf; simp [show (2 : F) = 0 by decide]

private lemma diffF_const_of_diff_zero {n : ℕ} {f : (Fin n → F) → F}
    (h : ∀ d x, diffF f d x = 0) (x : Fin n → F) : f x = f 0 := by
  have h0 := h x 0
  rw [diffF_eq_add, zero_add] at h0
  have h2 := congrArg (· + f 0) h0
  simp only [zero_add] at h2
  rw [add_assoc, f_add_self, add_zero] at h2
  exact h2

private lemma thirdF_shift {n : ℕ} {g : (Fin n → F) → F} (hg : isCubic g) (a b c x : Fin n → F) :
    diffF (diffF (diffF g a) b) c x = thirdF g a b c :=
  diffF_const_of_diff_zero (hg a b c) x

private lemma thirdF_symm_12 {n : ℕ} (g : (Fin n → F) → F) (a b c : Fin n → F) :
    thirdF g a b c = thirdF g b a c := by
  unfold thirdF
  have h : diffF (diffF g a) b = diffF (diffF g b) a := funext (diffF_comm g a b)
  rw [h]

private lemma thirdF_symm_23 {n : ℕ} (g : (Fin n → F) → F) (a b c : Fin n → F) :
    thirdF g a b c = thirdF g a c b :=
  diffF_comm (diffF g a) b c 0

private lemma thirdF_alt_12 {n : ℕ} (g : (Fin n → F) → F) (a c : Fin n → F) :
    thirdF g a a c = 0 := by
  unfold thirdF
  have h : diffF (diffF g a) a = fun _ => 0 := funext (diffF_self g a)
  rw [h, diffF_const]

private lemma thirdF_alt_23 {n : ℕ} (g : (Fin n → F) → F) (a b : Fin n → F) :
    thirdF g a b b = 0 := by
  rw [thirdF_symm_12, thirdF_symm_23, thirdF_symm_12, thirdF_alt_12]

private lemma thirdF_alt_13 {n : ℕ} (g : (Fin n → F) → F) (a b : Fin n → F) :
    thirdF g a b a = 0 := by
  rw [thirdF_symm_23, thirdF_alt_12]

private lemma thirdF_zero_left {n : ℕ} (g : (Fin n → F) → F) (b c : Fin n → F) :
    thirdF g 0 b c = 0 := by
  unfold thirdF
  have h : diffF g 0 = fun _ => 0 := funext (diffF_zero g)
  rw [h]; simp [diffF]

private lemma thirdF_add_left {n : ℕ} {g : (Fin n → F) → F} (hg : isCubic g)
    (a a' b c : Fin n → F) :
    thirdF g (a + a') b c = thirdF g a b c + thirdF g a' b c := by
  unfold thirdF
  have h1 : diffF g (a + a') = fun x => diffF g a' (x + a) + diffF g a x :=
    funext (diffF_add_dir g a a')
  rw [h1]
  have hshift : ∀ (f : (Fin n → F) → F) (u v x : Fin n → F),
      diffF (fun y => f (y + a)) u x = diffF f u (x + a) := by
    intro f u v x
    simp only [diffF_eq_add]
    have : x + u + a = x + a + u := by abel
    rw [this]
  have h2 : diffF (fun x => diffF g a' (x + a) + diffF g a x) b =
      fun x => diffF (diffF g a') b (x + a) + diffF (diffF g a) b x := by
    funext x
    rw [diffF_add_fun, hshift (diffF g a') b 0 x]
  rw [h2, diffF_add_fun, hshift (diffF (diffF g a') b) c 0 0, zero_add]
  rw [thirdF_shift hg a' b c a, add_comm]
  rfl

private lemma thirdF_smul_left {n : ℕ} {g : (Fin n → F) → F} (_hg : isCubic g)
    (s : F) (a b c : Fin n → F) :
    thirdF g (s • a) b c = s * thirdF g a b c := by
  rcases f_eq_zero_or_one s with rfl | rfl
  · simp [thirdF_zero_left]
  · simp

private lemma thirdF_add_mid {n : ℕ} {g : (Fin n → F) → F} (hg : isCubic g)
    (a b b' c : Fin n → F) :
    thirdF g a (b + b') c = thirdF g a b c + thirdF g a b' c := by
  rw [thirdF_symm_12, thirdF_add_left hg, thirdF_symm_12, thirdF_symm_12 g a b']

private lemma thirdF_add_right {n : ℕ} {g : (Fin n → F) → F} (hg : isCubic g)
    (a b c c' : Fin n → F) :
    thirdF g a b (c + c') = thirdF g a b c + thirdF g a b c' := by
  rw [thirdF_symm_23, thirdF_add_mid hg, thirdF_symm_23, thirdF_symm_23 g a b c']

private lemma thirdF_smul_mid {n : ℕ} {g : (Fin n → F) → F} (hg : isCubic g)
    (s : F) (a b c : Fin n → F) :
    thirdF g a (s • b) c = s * thirdF g a b c := by
  rw [thirdF_symm_12, thirdF_smul_left hg, thirdF_symm_12]

private lemma thirdF_smul_right {n : ℕ} {g : (Fin n → F) → F} (hg : isCubic g)
    (s : F) (a b c : Fin n → F) :
    thirdF g a b (s • c) = s * thirdF g a b c := by
  rw [thirdF_symm_23, thirdF_smul_mid hg, thirdF_symm_23]

private def thirdLin {n : ℕ} (g : (Fin n → F) → F) (hg : isCubic g) (a : Fin n → F) :
    (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F where
  toFun b :=
    { toFun := fun c => thirdF g a b c
      map_add' := fun c c' => thirdF_add_right hg a b c c'
      map_smul' := fun s c => by simpa using thirdF_smul_right hg s a b c }
  map_add' b b' := LinearMap.ext fun c => thirdF_add_mid hg a b b' c
  map_smul' s b := LinearMap.ext fun c => by simpa using thirdF_smul_mid hg s a b c

private lemma isCubic_add {n : ℕ} {f g : (Fin n → F) → F} (hf : isCubic f) (hg : isCubic g) :
    isCubic (fun x => f x + g x) := by
  intro a b c d x
  have h1 : diffF (fun y => f y + g y) a = fun y => diffF f a y + diffF g a y :=
    funext (diffF_add_fun f g a)
  rw [h1]
  have h2 : diffF (fun y => diffF f a y + diffF g a y) b =
      fun y => diffF (diffF f a) b y + diffF (diffF g a) b y :=
    funext (diffF_add_fun _ _ b)
  rw [h2]
  have h3 : diffF (fun y => diffF (diffF f a) b y + diffF (diffF g a) b y) c =
      fun y => diffF (diffF (diffF f a) b) c y + diffF (diffF (diffF g a) b) c y :=
    funext (diffF_add_fun _ _ c)
  rw [h3, diffF_add_fun, hf a b c d x, hg a b c d x, add_zero]

private lemma thirdF_add_fun {n : ℕ} (f g : (Fin n → F) → F) (a b c : Fin n → F) :
    thirdF (fun x => f x + g x) a b c = thirdF f a b c + thirdF g a b c := by
  unfold thirdF
  have h1 : diffF (fun y => f y + g y) a = fun y => diffF f a y + diffF g a y :=
    funext (diffF_add_fun f g a)
  rw [h1]
  have h2 : diffF (fun y => diffF f a y + diffF g a y) b =
      fun y => diffF (diffF f a) b y + diffF (diffF g a) b y :=
    funext (diffF_add_fun _ _ b)
  rw [h2, diffF_add_fun]

private lemma isQuad_of_thirdF_eq {n : ℕ} {f g : (Fin n → F) → F}
    (hf : isCubic f) (hg : isCubic g) (heq : ∀ a b c, thirdF f a b c = thirdF g a b c) :
    isQuad (fun x => f x + g x) := by
  intro a b c x
  have hcub := isCubic_add hf hg
  rw [thirdF_shift hcub a b c x, thirdF_add_fun, heq a b c, f_add_self]

private lemma isQuad_isCubic {n : ℕ} {q : (Fin n → F) → F} (hq : isQuad q) : isCubic q := by
  intro a b c d x
  have h : diffF (diffF (diffF q a) b) c = fun _ => 0 := funext (hq a b c)
  rw [h, diffF_const]

private lemma isAff_isQuad {n : ℕ} {l : (Fin n → F) → F} (hl : isAff l) : isQuad l := by
  intro a b c x
  have h : diffF (diffF l a) b = fun _ => 0 := funext (hl a b)
  rw [h, diffF_const]

private lemma isAff_add {n : ℕ} {f g : (Fin n → F) → F} (hf : isAff f) (hg : isAff g) :
    isAff (fun x => f x + g x) := by
  intro a b x
  have h1 : diffF (fun y => f y + g y) a = fun y => diffF f a y + diffF g a y :=
    funext (diffF_add_fun f g a)
  rw [h1, diffF_add_fun, hf a b x, hg a b x, add_zero]

private lemma isQuad_add {n : ℕ} {f g : (Fin n → F) → F} (hf : isQuad f) (hg : isQuad g) :
    isQuad (fun x => f x + g x) := by
  intro a b c x
  have h1 : diffF (fun y => f y + g y) a = fun y => diffF f a y + diffF g a y :=
    funext (diffF_add_fun f g a)
  rw [h1]
  have h2 : diffF (fun y => diffF f a y + diffF g a y) b =
      fun y => diffF (diffF f a) b y + diffF (diffF g a) b y :=
    funext (diffF_add_fun _ _ b)
  rw [h2, diffF_add_fun, hf a b c x, hg a b c x, add_zero]

private lemma isQuad_mul_lin {n : ℕ} (α β : (Fin n → F) →ₗ[F] F) :
    isQuad (fun x => α x * β x) := by
  intro a b c x
  have h1 : diffF (fun y => α y * β y) a = fun y => α a * β y + α y * β a + α a * β a := by
    funext y; simp only [diffF_eq_add, map_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h1]
  have h2 : diffF (fun y => α a * β y + α y * β a + α a * β a) b =
      fun _ => α a * β b + α b * β a := by
    funext y; simp only [diffF_eq_add, map_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h2, diffF_const]

private lemma isQuad_dotProduct_lin {k : ℕ} (M : (Fin k → F) →ₗ[F] (Fin k → F))
    (v0 l : Fin k → F) (c : F) :
    isQuad (fun y => dotProduct (M y + v0) y + dotProduct l y + c) := by
  intro a b c' x
  have h1 : diffF (fun y => dotProduct (M y + v0) y + dotProduct l y + c) a =
      fun y => dotProduct (M a) y + dotProduct (M y) a +
        (dotProduct (M a) a + dotProduct v0 a + dotProduct l a) := by
    funext y
    simp only [diffF_eq_add, map_add, add_dotProduct, dotProduct_add]
    ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h1]
  have h2 : diffF (fun y => dotProduct (M a) y + dotProduct (M y) a +
        (dotProduct (M a) a + dotProduct v0 a + dotProduct l a)) b =
      fun _ => dotProduct (M a) b + dotProduct (M b) a := by
    funext y
    simp only [diffF_eq_add, map_add, add_dotProduct, dotProduct_add]
    ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h2, diffF_const]

private lemma isAff_eq_lin_add_const {n : ℕ} {f : (Fin n → F) → F} (hf : isAff f) :
    ∃ (l : (Fin n → F) →ₗ[F] F) (c : F), ∀ x, f x = l x + c := by
  have hshift : ∀ a x, diffF f a x = diffF f a 0 := fun a x =>
    diffF_const_of_diff_zero (hf a) x
  let l : (Fin n → F) →ₗ[F] F :=
    { toFun := fun a => diffF f a 0
      map_add' := fun a b => by
        rw [diffF_add_dir, zero_add, hshift b a, add_comm]
      map_smul' := fun s a => by
        rcases f_eq_zero_or_one s with rfl | rfl
        · simp [diffF_zero]
        · simp }
  refine ⟨l, f 0, fun x => ?_⟩
  change f x = diffF f x 0 + f 0
  rw [diffF_eq_add, zero_add, add_assoc, f_add_self, add_zero]

private lemma isQuad_repr {n : ℕ} {q : (Fin n → F) → F} (hq : isQuad q) :
    ∃ (c : F) (l : Fin n → F) (Q : Fin n → Fin n → F),
      ∀ x : Fin n → F,
        q x = c + ∑ i : Fin n, l i * x i +
          ∑ i : Fin n, ∑ j : Fin n, if i < j then Q i j * x i * x j else 0 := by
  let c : F := q 0
  let l : Fin n → F := fun i => diffF q (unitF i) 0
  let Q : Fin n → Fin n → F := fun i j => diffF (diffF q (unitF i)) (unitF j) 0
  refine ⟨c, l, Q, ?_⟩
  let q' : (Fin n → F) → F := fun x =>
    c + ∑ i : Fin n, l i * x i +
      ∑ i : Fin n, ∑ j : Fin n, if i < j then Q i j * x i * x j else 0
  have hq'_quad : isQuad q' := by
    have hconst : isQuad (n := n) (fun _ => c) := fun a b c' x => by simp [diffF]
    have hlin : isQuad (fun x => ∑ i : Fin n, l i * x i) := by
      intro a b c' x
      have h1 : diffF (fun y => ∑ i : Fin n, l i * y i) a = fun _ => ∑ i : Fin n, l i * a i := by
        funext y
        rw [diffF_sum_fun]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [diffF_eq_add, Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
      rw [h1]; simp [diffF]
    have hbil : isQuad (fun x => ∑ i : Fin n, ∑ j : Fin n, if i < j then Q i j * x i * x j else 0) := by
      intro a b c' x
      have hterm : ∀ i j : Fin n, isQuad (fun y => if i < j then Q i j * y i * y j else 0) := by
        intro i j
        by_cases hij : i < j
        · simp only [hij, ↓reduceIte]
          let α : (Fin n → F) →ₗ[F] F := Q i j • LinearMap.proj i
          let β : (Fin n → F) →ₗ[F] F := LinearMap.proj j
          have hmul := isQuad_mul_lin α β
          simpa [α, β, mul_assoc] using hmul
        · simp only [hij, ↓reduceIte]; intro u v w z; simp [diffF]
      have hsum : ∀ (s : Finset (Fin n)) (t : Finset (Fin n)),
          isQuad (fun y => ∑ i ∈ s, ∑ j ∈ t, if i < j then Q i j * y i * y j else 0) := by
        intro s t
        classical
        induction s using Finset.induction with
        | empty => intro u v w z; simp [diffF]
        | @insert i s hi ih =>
          have hinner : isQuad (fun y => ∑ j ∈ t, if i < j then Q i j * y i * y j else 0) := by
            clear ih
            induction t using Finset.induction with
            | empty => intro u v w z; simp [diffF]
            | @insert j t hj ih2 =>
              simpa [Finset.sum_insert hj] using isQuad_add (hterm i j) ih2
          simpa [Finset.sum_insert hi] using isQuad_add hinner ih
      exact hsum Finset.univ Finset.univ a b c' x
    exact isQuad_add (isQuad_add hconst hlin) hbil
  have hr_quad : isQuad (fun x => q x + q' x) := isQuad_add hq hq'_quad
  have hq'_zero : q' 0 = c := by simp [q']
  have hq'_unit : ∀ i : Fin n, q' (unitF i) = c + l i := by
    intro i
    dsimp only [q']
    have h1 : (∑ j : Fin n, l j * unitF i j) = l i := by
      rw [Finset.sum_eq_single i]
      · simp [unitF]
      · intro j _ hji; simp [unitF, Ne.symm hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2 : (∑ j : Fin n, ∑ k : Fin n, if j < k then Q j k * unitF i j * unitF i k else 0) = 0 := by
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with hjk
      · by_cases hij : i = j
        · subst hij
          have : i ≠ k := ne_of_lt hjk
          simp [unitF, this]
        · simp [unitF, hij]
      · rfl
    rw [h1, h2, add_zero]
  have hq'_pair : ∀ i j : Fin n, i < j → q' (unitF i + unitF j) = c + l i + l j + Q i j := by
    intro i j hij
    dsimp only [q']
    have h1 : (∑ t : Fin n, l t * (unitF i + unitF j) t) = l i + l j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨ne_of_gt hij, Finset.mem_univ j⟩
      rw [← Finset.sum_erase_add _ _ hjmem]
      have hrest : ∑ t ∈ (Finset.univ.erase i).erase j, l t * (unitF i + unitF j) t = 0 := by
        refine Finset.sum_eq_zero fun t ht => ?_
        have ht1 : t ≠ j := (Finset.mem_erase.mp ht).1
        have ht2 : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        simp [unitF, Ne.symm ht1, Ne.symm ht2]
      rw [hrest, zero_add]
      simp [unitF, ne_of_lt hij, ne_of_gt hij]; ring
    have h2 : (∑ a : Fin n, ∑ b : Fin n,
        if a < b then Q a b * (unitF i + unitF j) a * (unitF i + unitF j) b else 0) = Q i j := by
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp [hij, unitF, ne_of_lt hij, ne_of_gt hij]
        · intro b _ hbj
          split_ifs with hib
          · have hbi : b ≠ i := ne_of_gt hib
            simp [unitF, Ne.symm hbj, Ne.symm hbi]
          · rfl
        · intro h; exact absurd (Finset.mem_univ j) h
      · intro a _ hai
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with hab
        · by_cases haj : a = j
          · subst a
            have hbi : i ≠ b := ne_of_lt (lt_trans hij hab)
            have hbj : j ≠ b := ne_of_lt hab
            simp [unitF, hbi, hbj, Pi.add_apply]
          · simp [unitF, Ne.symm hai, Ne.symm haj, Pi.add_apply]
        · rfl
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1, h2]; ring
  let r : (Fin n → F) → F := fun x => q x + q' x
  have hr_2 : ∀ a b x, diffF (diffF r a) b x = diffF (diffF r a) b 0 := fun a b x =>
    diffF_const_of_diff_zero (hr_quad a b) x
  have hr_2_unit : ∀ i j : Fin n, diffF (diffF r (unitF i)) (unitF j) 0 = 0 := by
    have h2 : (2 : F) = 0 := by decide
    have h4 : (4 : F) = 0 := by decide
    have h10 : (10 : F) = 0 := by decide
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp only [diffF_eq_add, zero_add, r]
      have hqij : Q i j = q (unitF i + unitF j) + q (unitF i) + q (unitF j) + q 0 := by
        dsimp only [Q]; simp only [diffF_eq_add, zero_add]; rw [add_comm (unitF j) (unitF i)]; ring
      have hli : l i = q (unitF i) + q 0 := by dsimp only [l]; simp [diffF_eq_add]
      have hlj : l j = q (unitF j) + q 0 := by dsimp only [l]; simp [diffF_eq_add]
      rw [add_comm (unitF j) (unitF i), hq'_pair i j hij, hq'_unit i, hq'_unit j, hq'_zero,
        hqij, hli, hlj]
      dsimp only [c]; ring_nf; simp [h2, h4, h10]
    · exact diffF_self r (unitF i) 0
    · rw [diffF_comm]
      simp only [diffF_eq_add, zero_add, r]
      have hqji : Q j i = q (unitF j + unitF i) + q (unitF j) + q (unitF i) + q 0 := by
        dsimp only [Q]; simp only [diffF_eq_add, zero_add]; rw [add_comm (unitF i) (unitF j)]; ring
      have hli : l i = q (unitF i) + q 0 := by dsimp only [l]; simp [diffF_eq_add]
      have hlj : l j = q (unitF j) + q 0 := by dsimp only [l]; simp [diffF_eq_add]
      rw [add_comm (unitF i) (unitF j), hq'_pair j i hji, hq'_unit i, hq'_unit j, hq'_zero,
        hqji, hli, hlj]
      dsimp only [c]; ring_nf; simp [h2, h4, h10]
  have hr_aff : isAff r := by
    have hadd_left : ∀ a a' b, diffF (diffF r (a + a')) b 0 =
        diffF (diffF r a) b 0 + diffF (diffF r a') b 0 := by
      intro a a' b
      have h1 : diffF r (a + a') = fun x => diffF r a' (x + a) + diffF r a x :=
        funext (diffF_add_dir r a a')
      rw [h1, diffF_add_fun]
      have hsh : diffF (fun x => diffF r a' (x + a)) b 0 = diffF (diffF r a') b a := by
        simp only [diffF_eq_add, zero_add]; rw [add_comm b a]
      rw [hsh, hr_2 a' b a, add_comm]
    have hsmul_left : ∀ (s : F) a b, diffF (diffF r (s • a)) b 0 = s * diffF (diffF r a) b 0 := by
      intro s a b
      rcases f_eq_zero_or_one s with rfl | rfl
      · simp [show diffF r 0 = fun _ => 0 from funext (diffF_zero r), diffF_const]
      · simp
    have hlin_right : ∀ a b, diffF (diffF r a) b 0 = 0 := by
      have hleft_unit : ∀ i b, diffF (diffF r (unitF i)) b 0 = 0 := by
        intro i b
        rw [vec_eq_sum_unit b]
        have hsum : ∀ s : Finset (Fin n),
            diffF (diffF r (unitF i)) (∑ j ∈ s, b j • unitF j) 0 = 0 := by
          intro s
          classical
          induction s using Finset.induction with
          | empty => simp [diffF_zero]
          | @insert j s hj ih =>
            rw [Finset.sum_insert hj, diffF_comm, hadd_left,
              diffF_comm r (∑ x ∈ s, b x • unitF x) (unitF i), ih, add_zero,
              hsmul_left, diffF_comm, hr_2_unit, mul_zero]
        exact hsum Finset.univ
      intro a b
      rw [vec_eq_sum_unit a]
      have hsum : ∀ s : Finset (Fin n),
          diffF (diffF r (∑ i ∈ s, a i • unitF i)) b 0 = 0 := by
        intro s
        classical
        induction s using Finset.induction with
        | empty => simp [show diffF r 0 = fun _ => 0 from funext (diffF_zero r), diffF_const]
        | @insert i s hi ih =>
          rw [Finset.sum_insert hi, hadd_left, ih, add_zero, hsmul_left, hleft_unit, mul_zero]
      exact hsum Finset.univ
    intro a b x
    rw [hr_2 a b x, hlin_right a b]
  obtain ⟨lr, cr, hrc⟩ := isAff_eq_lin_add_const hr_aff
  have hcr : cr = 0 := by
    have h0 := hrc 0
    simp only [map_zero, zero_add, r, hq'_zero] at h0
    dsimp only [c] at h0
    rw [f_add_self] at h0
    exact h0.symm
  have hlr : lr = 0 := by
    have hunit : ∀ i : Fin n, lr (unitF i) = 0 := by
      intro i
      have hi := hrc (unitF i)
      simp only [hcr, add_zero, r, hq'_unit] at hi
      dsimp only [c, l] at hi
      rw [diffF_eq_add, zero_add] at hi
      have : q (unitF i) + (q 0 + (q (unitF i) + q 0)) = 0 := by
        ring_nf; simp [show (2 : F) = 0 by decide]
      rw [this] at hi
      exact hi.symm
    apply LinearMap.ext; intro x
    rw [vec_eq_sum_unit x]
    simp [map_sum, map_smul, hunit]
  intro x
  have hx := hrc x
  simp only [hlr, LinearMap.zero_apply, hcr, add_zero, r] at hx
  have h2 := congrArg (· + q' x) hx
  rw [add_assoc, f_add_self, add_zero, zero_add] at h2
  exact h2

private def wedge3 {n : ℕ} (α β γ : (Fin n → F) →ₗ[F] F) (a b c : Fin n → F) : F :=
  α a * β b * γ c + α a * β c * γ b +
  α b * β a * γ c + α b * β c * γ a +
  α c * β a * γ b + α c * β b * γ a

private lemma isCubic_mul3 {n : ℕ} (α β γ : (Fin n → F) →ₗ[F] F) :
    isCubic (fun x => α x * β x * γ x) := by
  intro a b c d x
  have h1 : diffF (fun y => α y * β y * γ y) a = fun y =>
      (α a * β y * γ y + α y * β a * γ y + α y * β y * γ a) +
      (α a * β a * γ y + α a * β y * γ a + α y * β a * γ a + α a * β a * γ a) := by
    funext y; simp only [diffF_eq_add, map_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h1]
  have h2 : diffF (fun y =>
      (α a * β y * γ y + α y * β a * γ y + α y * β y * γ a) +
      (α a * β a * γ y + α a * β y * γ a + α y * β a * γ a + α a * β a * γ a)) b = fun y =>
      (α a * β b + α b * β a) * γ y + (α a * γ b + α b * γ a) * β y +
      (β a * γ b + β b * γ a) * α y +
      (α a * β b * γ b + α b * β a * γ b + α b * β b * γ a +
       α a * β a * γ b + α a * β b * γ a + α b * β a * γ a) := by
    funext y; simp only [diffF_eq_add, map_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h2]
  have h3 : diffF (fun y =>
      (α a * β b + α b * β a) * γ y + (α a * γ b + α b * γ a) * β y +
      (β a * γ b + β b * γ a) * α y +
      (α a * β b * γ b + α b * β a * γ b + α b * β b * γ a +
       α a * β a * γ b + α a * β b * γ a + α b * β a * γ a)) c =
      fun _ => wedge3 α β γ a b c := by
    funext y; simp only [diffF_eq_add, map_add, wedge3]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h3, diffF_const]

private lemma thirdF_mul3 {n : ℕ} (α β γ : (Fin n → F) →ₗ[F] F) (a b c : Fin n → F) :
    thirdF (fun x => α x * β x * γ x) a b c = wedge3 α β γ a b c := by
  unfold thirdF
  have h1 : diffF (fun y => α y * β y * γ y) a = fun y =>
      (α a * β y * γ y + α y * β a * γ y + α y * β y * γ a) +
      (α a * β a * γ y + α a * β y * γ a + α y * β a * γ a + α a * β a * γ a) := by
    funext y; simp only [diffF_eq_add, map_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h1]
  have h2 : diffF (fun y =>
      (α a * β y * γ y + α y * β a * γ y + α y * β y * γ a) +
      (α a * β a * γ y + α a * β y * γ a + α y * β a * γ a + α a * β a * γ a)) b = fun y =>
      (α a * β b + α b * β a) * γ y + (α a * γ b + α b * γ a) * β y +
      (β a * γ b + β b * γ a) * α y +
      (α a * β b * γ b + α b * β a * γ b + α b * β b * γ a +
       α a * β a * γ b + α a * β b * γ a + α b * β a * γ a) := by
    funext y; simp only [diffF_eq_add, map_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  rw [h2]
  simp only [diffF_eq_add, map_add, map_zero, wedge3]; ring_nf
  simp [show (2 : F) = 0 by decide]

/-! ## Section 2: Alternating bilinear forms (Darboux) and alternating 3-form classification -/

private noncomputable def bilRank {n : ℕ} (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) : ℕ :=
  Module.finrank F (LinearMap.range ω)

private lemma matrix_rank_eq_bilRank {n : ℕ}
    (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) (hsym : ∀ u v, ω u v = ω v u) :
    (Matrix.of (fun i j : Fin n => ω (unitF i) (unitF j))).rank = bilRank ω := by
  let A : Matrix (Fin n) (Fin n) F := Matrix.of (fun i j => ω (unitF i) (unitF j))
  let ev : ((Fin n → F) →ₗ[F] F) ≃ₗ[F] (Fin n → F) :=
    { toFun := fun f i => f (unitF i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v =>
        { toFun := fun x => ∑ i : Fin n, v i * x i
          map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun s x => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring }
      left_inv := fun f => by
        apply LinearMap.ext; intro x
        change (∑ i : Fin n, f (unitF i) * x i) = f x
        conv_rhs => rw [vec_eq_sum_unit x]
        simp only [map_sum, map_smul, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      right_inv := fun v => by
        funext i
        change (∑ j : Fin n, v j * unitF i j) = v i
        rw [Finset.sum_eq_single i]
        · simp [unitF]
        · intro j _ hji; simp [unitF, Ne.symm hji]
        · intro h; exact absurd (Finset.mem_univ i) h }
  have hcomp : A.mulVecLin = ev.toLinearMap.comp ω := by
    apply LinearMap.ext; intro v; funext i
    change (∑ j : Fin n, ω (unitF i) (unitF j) * v j) = ω v (unitF i)
    rw [hsym v (unitF i)]
    conv_rhs => rw [vec_eq_sum_unit v]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [Matrix.rank, bilRank, hcomp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq ev (LinearMap.range ω)

private lemma alt_symm {n : ℕ} (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F)
    (halt : ∀ v, ω v v = 0) (u v : Fin n → F) : ω u v = ω v u := by
  have h := halt (u + v)
  simp only [map_add, LinearMap.add_apply, halt u, halt v, zero_add, add_zero] at h
  have h2 := congrArg (· + ω v u) h
  simp only [zero_add] at h2
  rw [← h2]; ring_nf; simp [show (2 : F) = 0 by decide]

private def wedge2 {n : ℕ} (α β : (Fin n → F) →ₗ[F] F) :
    (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F where
  toFun u := α u • β + β u • α
  map_add' u u' := LinearMap.ext fun v => by simp [map_add]; ring
  map_smul' s u := LinearMap.ext fun v => by simp [map_smul]; ring

private lemma wedge2_apply {n : ℕ} (α β : (Fin n → F) →ₗ[F] F) (u v : Fin n → F) :
    wedge2 α β u v = α u * β v + β u * α v := by
  simp [wedge2]

private lemma altBil_darboux_step {n : ℕ}
    (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) (halt : ∀ v, ω v v = 0)
    (hne : ω ≠ 0) :
    ∃ (α β : (Fin n → F) →ₗ[F] F),
      (∀ x, ω x = 0 → α x = 0 ∧ β x = 0) ∧
      (∀ v, (ω + wedge2 α β) v v = 0) ∧
      bilRank (ω + wedge2 α β) + 2 = bilRank ω := by
  have hex : ∃ e1 e2 : Fin n → F, ω e1 e2 = 1 := by
    by_contra hall
    push Not at hall
    apply hne
    apply LinearMap.ext; intro u; apply LinearMap.ext; intro v
    rcases f_eq_zero_or_one (ω u v) with h0 | h1
    · exact h0
    · exact absurd h1 (hall u v)
  rcases hex with ⟨e1, e2, he12⟩
  have hsym := alt_symm ω halt
  let α : (Fin n → F) →ₗ[F] F := ω e2
  let β : (Fin n → F) →ₗ[F] F := ω e1
  have hα1 : α e1 = 1 := by dsimp only [α]; rw [hsym, he12]
  have hα2 : α e2 = 0 := halt e2
  have hβ1 : β e1 = 0 := halt e1
  have hβ2 : β e2 = 1 := he12
  let ω' : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F := ω + wedge2 α β
  have halt' : ∀ v, ω' v v = 0 := by
    intro v
    simp only [ω', LinearMap.add_apply, halt v, wedge2_apply, zero_add]
    rw [mul_comm (β v) (α v), f_add_self]
  have hker_sub : LinearMap.ker ω ≤ LinearMap.ker ω' := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply LinearMap.ext; intro v
    have hαx : α x = 0 := by dsimp only [α]; rw [hsym, hx]; rfl
    have hβx : β x = 0 := by dsimp only [β]; rw [hsym, hx]; rfl
    simp [ω', wedge2_apply, hx, hαx, hβx]
  have hω'_e1 : ω' e1 = 0 := by
    apply LinearMap.ext; intro v
    simp only [ω', LinearMap.add_apply, wedge2_apply, hα1, hβ1, one_mul, zero_mul, add_zero,
      LinearMap.zero_apply]
    dsimp only [β]; exact f_add_self _
  have hω'_e2 : ω' e2 = 0 := by
    apply LinearMap.ext; intro v
    simp only [ω', LinearMap.add_apply, wedge2_apply, hα2, hβ2, one_mul, zero_mul, zero_add,
      LinearMap.zero_apply]
    dsimp only [α]; exact f_add_self _
  have hker_eq : LinearMap.ker ω' = LinearMap.ker ω ⊔ Submodule.span F ({e1, e2} : Set (Fin n → F)) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      let y := x + α x • e1 + β x • e2
      have hy_ker : y ∈ LinearMap.ker ω := by
        rw [LinearMap.mem_ker]
        apply LinearMap.ext; intro v
        have hxv := congrArg (fun f => f v) hx
        simp only [ω', LinearMap.add_apply, wedge2_apply, LinearMap.zero_apply] at hxv
        simp only [y, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          LinearMap.zero_apply]
        dsimp only [α, β] at hxv ⊢
        simpa [add_assoc] using hxv
      have hdecomp : x = y + (α x • e1 + β x • e2) := by
        dsimp only [y]
        funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf
        simp [show (2 : F) = 0 by decide]
      rw [hdecomp]
      apply Submodule.add_mem_sup hy_ker
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · refine sup_le hker_sub (Submodule.span_le.mpr ?_)
      rintro x (rfl | rfl)
      · exact hω'_e1
      · exact hω'_e2
  have hdisj : Disjoint (LinearMap.ker ω) (Submodule.span F ({e1, e2} : Set (Fin n → F))) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    rw [Submodule.mem_span_pair] at hx2
    rcases hx2 with ⟨c1, c2, rfl⟩
    rw [LinearMap.mem_ker] at hx1
    have h1 := congrArg (fun f => f e2) hx1
    have h2 := congrArg (fun f => f e1) hx1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      halt e2, halt e1, he12, mul_zero, mul_one, add_zero, zero_add, LinearMap.zero_apply,
      hsym e2 e1] at h1 h2
    simp [h1, h2]
  have hspan_rank : Module.finrank F (Submodule.span F ({e1, e2} : Set (Fin n → F))) = 2 := by
    have hind : LinearIndependent F ![e1, e2] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h1 := congrArg (fun x => ω x e2) hg
      have h2 := congrArg (fun x => ω x e1) hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        halt e2, halt e1, he12, hsym e2 e1, mul_zero, mul_one, add_zero, zero_add, map_zero,
        LinearMap.zero_apply] at h1 h2
      fin_cases i
      · exact h1
      · exact h2
    have hset : ({e1, e2} : Set (Fin n → F)) = Set.range ![e1, e2] := by
      ext x; simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hset, finrank_span_eq_card hind]; simp
  have hker_rank : Module.finrank F (LinearMap.ker ω') = Module.finrank F (LinearMap.ker ω) + 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker ω) (Submodule.span F ({e1, e2} : Set (Fin n → F)))
    have hinf : (LinearMap.ker ω ⊓ Submodule.span F ({e1, e2} : Set (Fin n → F))) = ⊥ :=
      disjoint_iff.mp hdisj
    rw [hinf, finrank_bot, add_zero, hspan_rank, ← hker_eq] at h
    exact h
  have hrn1 := LinearMap.finrank_range_add_finrank_ker ω
  have hrn2 := LinearMap.finrank_range_add_finrank_ker ω'
  rw [Module.finrank_fin_fun] at hrn1 hrn2
  refine ⟨α, β, ?_, halt', ?_⟩
  · intro x hx
    exact ⟨by dsimp only [α]; rw [hsym, hx]; rfl, by dsimp only [β]; rw [hsym, hx]; rfl⟩
  · dsimp only [bilRank, ω'] at hker_rank hrn2 ⊢
    omega

private lemma altBil_even_rank {n : ℕ}
    (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) (halt : ∀ v, ω v v = 0) :
    ∃ r, bilRank ω = 2 * r := by
  suffices h : ∀ k, bilRank ω = k → ∃ r, k = 2 * r from h (bilRank ω) rfl
  intro k
  induction k using Nat.strong_induction_on generalizing ω with
  | ind k ih =>
    intro hrank
    by_cases h0 : ω = 0
    · subst h0
      have : bilRank (0 : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) = 0 := by
        simp [bilRank]
      exact ⟨0, by omega⟩
    · obtain ⟨α, β, _, halt', hstep⟩ := altBil_darboux_step ω halt h0
      obtain ⟨r', hr'⟩ := ih (bilRank (ω + wedge2 α β)) (by omega) (ω + wedge2 α β) halt' rfl
      exact ⟨r' + 1, by omega⟩

private lemma altBil_rank_eq_two {n : ℕ}
    (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) (halt : ∀ v, ω v v = 0)
    (hrank : bilRank ω = 2) :
    ∃ (α β : (Fin n → F) →ₗ[F] F),
      (∀ u v, ω u v = α u * β v + β u * α v) ∧
      (∀ x, ω x = 0 → α x = 0 ∧ β x = 0) := by
  have hne : ω ≠ 0 := by
    intro h0; subst h0
    have : bilRank (0 : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) = 0 := by simp [bilRank]
    omega
  obtain ⟨α, β, hker, _, hstep⟩ := altBil_darboux_step ω halt hne
  have hzero_rank : bilRank (ω + wedge2 α β) = 0 := by omega
  have hzero : ω + wedge2 α β = 0 := by
    have hbot : LinearMap.range (ω + wedge2 α β) = ⊥ :=
      Submodule.finrank_eq_zero.mp hzero_rank
    apply LinearMap.ext; intro u; apply LinearMap.ext; intro v
    have hmem : (ω + wedge2 α β) u ∈ LinearMap.range (ω + wedge2 α β) := ⟨u, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact congrArg (fun f => f v) hmem
  refine ⟨α, β, ?_, hker⟩
  intro u v
  have h := congrArg (fun f => f u v) hzero
  simp only [LinearMap.add_apply, LinearMap.zero_apply, wedge2_apply] at h
  have h2 := congrArg (· + (α u * β v + β u * α v)) h
  rw [add_assoc, f_add_self, add_zero, zero_add] at h2
  exact h2

private lemma altBil_rank_le_four {n : ℕ}
    (ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) (halt : ∀ v, ω v v = 0)
    (hrank : bilRank ω ≤ 4) :
    ∃ (α₁ β₁ α₂ β₂ : (Fin n → F) →ₗ[F] F),
      ∀ u v, ω u v = (α₁ u * β₁ v + β₁ u * α₁ v) + (α₂ u * β₂ v + β₂ u * α₂ v) := by
  obtain ⟨r, hr⟩ := altBil_even_rank ω halt
  have hr2 : r ≤ 2 := by omega
  interval_cases r
  · have hbot : LinearMap.range ω = ⊥ := Submodule.finrank_eq_zero.mp (by dsimp only [bilRank] at hr; omega)
    refine ⟨0, 0, 0, 0, fun u v => ?_⟩
    have hmem : ω u ∈ LinearMap.range ω := ⟨u, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    simp [hmem]
  · obtain ⟨α, β, hω, _⟩ := altBil_rank_eq_two ω halt (by omega)
    exact ⟨α, β, 0, 0, fun u v => by simp [hω u v]⟩
  · have hne : ω ≠ 0 := by
      intro h0; subst h0
      have : bilRank (0 : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) = 0 := by simp [bilRank]
      omega
    obtain ⟨α₁, β₁, _, halt', hstep⟩ := altBil_darboux_step ω halt hne
    obtain ⟨α₂, β₂, hω', _⟩ := altBil_rank_eq_two (ω + wedge2 α₁ β₁) halt' (by omega)
    refine ⟨α₁, β₁, α₂, β₂, fun u v => ?_⟩
    have h := hω' u v
    simp only [LinearMap.add_apply, wedge2_apply] at h
    have h2 := congrArg (· + (α₁ u * β₁ v + β₁ u * α₁ v)) h
    rw [add_assoc, f_add_self, add_zero, add_comm] at h2
    exact h2

private lemma wedge3_on_four {n : ℕ} (T : (Fin n → F) → (Fin n → F) → (Fin n → F) → F)
    (hadd1 : ∀ a a' b c, T (a + a') b c = T a b c + T a' b c)
    (hadd2 : ∀ a b b' c, T a (b + b') c = T a b c + T a b' c)
    (hadd3 : ∀ a b c c', T a b (c + c') = T a b c + T a b c')
    (halt12 : ∀ a c, T a a c = 0) (halt23 : ∀ a b, T a b b = 0)
    (hsym12 : ∀ a b c, T a b c = T b a c) (hsym23 : ∀ a b c, T a b c = T a c b)
    (φ : Fin 4 → (Fin n → F) →ₗ[F] F) (e : Fin 4 → (Fin n → F))
    (hproj : ∀ x v w, T (x + ∑ i : Fin 4, φ i x • e i) v w = 0) :
    ∀ a b c, T a b c =
      wedge3 (φ 0) (φ 1) (T (e 0) (e 1) (e 2) • φ 2 + T (e 0) (e 1) (e 3) • φ 3) a b c +
      wedge3 (T (e 0) (e 2) (e 3) • φ 0 + T (e 1) (e 2) (e 3) • φ 1) (φ 2) (φ 3) a b c := by
  have hsmul1 : ∀ (s : F) a b c, T (s • a) b c = s * T a b c := by
    intro s a b c
    rcases f_eq_zero_or_one s with rfl | rfl
    · have h0 : T 0 b c = 0 := by
        have := hadd1 0 0 b c; rw [zero_add] at this
        have h2 := congrArg (· + T 0 b c) this
        rw [f_add_self, zero_add] at h2; exact h2.symm
      simp [h0]
    · simp
  have hsmul2 : ∀ (s : F) a b c, T a (s • b) c = s * T a b c := fun s a b c => by
    rw [hsym12, hsmul1, hsym12]
  have hsmul3 : ∀ (s : F) a b c, T a b (s • c) = s * T a b c := fun s a b c => by
    rw [hsym23, hsmul2, hsym23]
  have hdecomp : ∀ x, x = (∑ i : Fin 4, φ i x • e i) + (x + ∑ i : Fin 4, φ i x • e i) := by
    intro x; funext t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
  have hT_proj : ∀ x y z, T x y z = T (∑ i : Fin 4, φ i x • e i)
      (∑ j : Fin 4, φ j y • e j) (∑ k : Fin 4, φ k z • e k) := by
    intro x y z
    have h1 : T x y z = T (∑ i : Fin 4, φ i x • e i) y z := by
      conv_lhs => rw [hdecomp x]
      rw [hadd1, hproj x y z, add_zero]
    have h2 : T (∑ i : Fin 4, φ i x • e i) y z =
        T (∑ i : Fin 4, φ i x • e i) (∑ j : Fin 4, φ j y • e j) z := by
      rw [hsym12]
      conv_lhs => rw [hdecomp y]
      rw [hadd1, hproj y _ z, add_zero, hsym12]
    have h3 : T (∑ i : Fin 4, φ i x • e i) (∑ j : Fin 4, φ j y • e j) z =
        T (∑ i : Fin 4, φ i x • e i) (∑ j : Fin 4, φ j y • e j) (∑ k : Fin 4, φ k z • e k) := by
      rw [hsym23, hsym12]
      conv_lhs => rw [hdecomp z]
      rw [hadd1, hproj z _ _, add_zero, hsym12, hsym23]
    rw [h1, h2, h3]
  have hsum1 : ∀ (s : Finset (Fin 4)) (f : Fin 4 → (Fin n → F)) y z,
      T (∑ i ∈ s, f i) y z = ∑ i ∈ s, T (f i) y z := by
    intro s f y z; classical
    induction s using Finset.induction with
    | empty =>
      have := hadd1 0 0 y z; rw [zero_add] at this
      have h2 := congrArg (· + T 0 y z) this
      rw [f_add_self, zero_add] at h2; exact h2.symm
    | @insert i s hi ih => rw [Finset.sum_insert hi, hadd1, ih, Finset.sum_insert hi]
  have hsum2 : ∀ (s : Finset (Fin 4)) (f : Fin 4 → (Fin n → F)) x z,
      T x (∑ i ∈ s, f i) z = ∑ i ∈ s, T x (f i) z := fun s f x z => by
    rw [hsym12, hsum1]; refine Finset.sum_congr rfl fun i _ => hsym12 _ _ _
  have hsum3 : ∀ (s : Finset (Fin 4)) (f : Fin 4 → (Fin n → F)) x y,
      T x y (∑ i ∈ s, f i) = ∑ i ∈ s, T x y (f i) := fun s f x y => by
    rw [hsym23, hsum2]; refine Finset.sum_congr rfl fun i _ => hsym23 _ _ _
  intro a b c
  rw [hT_proj a b c, hsum1]
  simp_rw [hsum2, hsum3, hsmul1, hsmul2, hsmul3]
  simp only [Fin.sum_univ_four]
  have h00 : ∀ k, T (e 0) (e 0) (e k) = 0 := fun k => halt12 _ _
  have h11 : ∀ k, T (e 1) (e 1) (e k) = 0 := fun k => halt12 _ _
  have h22 : ∀ k, T (e 2) (e 2) (e k) = 0 := fun k => halt12 _ _
  have h33 : ∀ k, T (e 3) (e 3) (e k) = 0 := fun k => halt12 _ _
  have h020 : T (e 0) (e 2) (e 0) = 0 := by rw [hsym23]; exact halt12 _ _
  have h010 : T (e 0) (e 1) (e 0) = 0 := by rw [hsym23]; exact halt12 _ _
  have h030 : T (e 0) (e 3) (e 0) = 0 := by rw [hsym23]; exact halt12 _ _
  have h101 : T (e 1) (e 0) (e 1) = 0 := by rw [hsym23]; exact halt12 _ _
  have h121 : T (e 1) (e 2) (e 1) = 0 := by rw [hsym23]; exact halt12 _ _
  have h131 : T (e 1) (e 3) (e 1) = 0 := by rw [hsym23]; exact halt12 _ _
  have h202 : T (e 2) (e 0) (e 2) = 0 := by rw [hsym23]; exact halt12 _ _
  have h212 : T (e 2) (e 1) (e 2) = 0 := by rw [hsym23]; exact halt12 _ _
  have h232 : T (e 2) (e 3) (e 2) = 0 := by rw [hsym23]; exact halt12 _ _
  have h303 : T (e 3) (e 0) (e 3) = 0 := by rw [hsym23]; exact halt12 _ _
  have h313 : T (e 3) (e 1) (e 3) = 0 := by rw [hsym23]; exact halt12 _ _
  have h323 : T (e 3) (e 2) (e 3) = 0 := by rw [hsym23]; exact halt12 _ _
  have hsym_all :
      T (e 0) (e 2) (e 1) = T (e 0) (e 1) (e 2) ∧
      T (e 1) (e 0) (e 2) = T (e 0) (e 1) (e 2) ∧
      T (e 1) (e 2) (e 0) = T (e 0) (e 1) (e 2) ∧
      T (e 2) (e 0) (e 1) = T (e 0) (e 1) (e 2) ∧
      T (e 2) (e 1) (e 0) = T (e 0) (e 1) (e 2) ∧
      T (e 0) (e 3) (e 1) = T (e 0) (e 1) (e 3) ∧
      T (e 1) (e 0) (e 3) = T (e 0) (e 1) (e 3) ∧
      T (e 1) (e 3) (e 0) = T (e 0) (e 1) (e 3) ∧
      T (e 3) (e 0) (e 1) = T (e 0) (e 1) (e 3) ∧
      T (e 3) (e 1) (e 0) = T (e 0) (e 1) (e 3) ∧
      T (e 0) (e 3) (e 2) = T (e 0) (e 2) (e 3) ∧
      T (e 2) (e 0) (e 3) = T (e 0) (e 2) (e 3) ∧
      T (e 2) (e 3) (e 0) = T (e 0) (e 2) (e 3) ∧
      T (e 3) (e 0) (e 2) = T (e 0) (e 2) (e 3) ∧
      T (e 3) (e 2) (e 0) = T (e 0) (e 2) (e 3) ∧
      T (e 1) (e 3) (e 2) = T (e 1) (e 2) (e 3) ∧
      T (e 2) (e 1) (e 3) = T (e 1) (e 2) (e 3) ∧
      T (e 2) (e 3) (e 1) = T (e 1) (e 2) (e 3) ∧
      T (e 3) (e 1) (e 2) = T (e 1) (e 2) (e 3) ∧
      T (e 3) (e 2) (e 1) = T (e 1) (e 2) (e 3) := by
    refine ⟨hsym23 _ _ _, hsym12 _ _ _, by rw [hsym23, hsym12], by rw [hsym12, hsym23],
      by rw [hsym12, hsym23, hsym12],
      hsym23 _ _ _, hsym12 _ _ _, by rw [hsym23, hsym12], by rw [hsym12, hsym23],
      by rw [hsym12, hsym23, hsym12],
      hsym23 _ _ _, hsym12 _ _ _, by rw [hsym23, hsym12], by rw [hsym12, hsym23],
      by rw [hsym12, hsym23, hsym12],
      hsym23 _ _ _, hsym12 _ _ _, by rw [hsym23, hsym12], by rw [hsym12, hsym23],
      by rw [hsym12, hsym23, hsym12]⟩
  simp only [halt23, h00, h11, h22, h33, h020, h010, h030, h101, h121, h131,
    h202, h212, h232, h303, h313, h323, hsym_all,
    wedge3, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

private lemma exists_dual_coords {n m : ℕ} (φ : Fin m → (Fin n → F) →ₗ[F] F)
    (hcodim : Module.finrank F ↥(⨅ i : Fin m, LinearMap.ker (φ i)) + m = n) :
    ∃ e : Fin m → (Fin n → F), ∀ i j : Fin m, φ i (e j) = if i = j then 1 else 0 := by
  let Φ : (Fin n → F) →ₗ[F] (Fin m → F) := LinearMap.pi φ
  have hker : LinearMap.ker Φ = ⨅ i : Fin m, LinearMap.ker (φ i) := LinearMap.ker_pi φ
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [Module.finrank_fin_fun, hker] at hrn
  have hrg : Module.finrank F (LinearMap.range Φ) = m := by omega
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq (by rw [hrg, Module.finrank_fin_fun])
  choose e he using fun j : Fin m => hsurj (unitF j)
  refine ⟨e, fun i j => ?_⟩
  have h := congrArg (fun f => f i) (he j)
  simpa [Φ, unitF, eq_comm] using h

private lemma exists_two_wedge3_of_le_five {n : ℕ} (g : (Fin n → F) → F)
    (R : Submodule F (Fin n → F)) (hg : isCubic g)
    (hR : ∀ u, u ∈ R ↔ ∀ v w, thirdF g u v w = 0)
    (hd : n - Module.finrank F R ≤ 5) :
    ∃ α₁ β₁ γ₁ α₂ β₂ γ₂ : (Fin n → F) →ₗ[F] F,
      ∀ a b c, thirdF g a b c = wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c := by
  set d := n - Module.finrank F R
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl R
  have hW_rank : Module.finrank F W = d := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq R W
    rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun] at hsum
    omega
  let bW : Module.Basis (Fin d) F W := Module.finBasisOfFinrankEq F W hW_rank
  let projW : (Fin n → F) →ₗ[F] W :=
    (Submodule.projectionOnto W R hW.symm)
  have hprojW_R : ∀ r ∈ R, projW r = 0 := fun r hr =>
    Submodule.projectionOnto_apply_right hW.symm ⟨r, hr⟩
  have hprojW_W : ∀ w : W, projW w.1 = w := fun w =>
    Submodule.projectionOnto_apply_left hW.symm w
  have hsub_R : ∀ x, x + (projW x).1 ∈ R := by
    intro x
    have hmem : x ∈ W ⊔ R := by rw [hW.symm.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hmem
    rcases hmem with ⟨w, hw, r, hr, rfl⟩
    have hpw : projW (w + r) = ⟨w, hw⟩ := by
      rw [map_add, hprojW_W ⟨w, hw⟩, hprojW_R r hr, add_zero]
    rw [hpw]
    have : w + r + w = r := by
      funext i; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
    rwa [this]
  let coord : Fin d → (Fin n → F) →ₗ[F] F := fun i => (bW.coord i).comp projW
  have hcoord_dual : ∀ i j : Fin d, coord i (bW j).1 = if i = j then 1 else 0 := by
    intro i j
    simp [coord, hprojW_W, bW.coord_apply, bW.repr_self, Finsupp.single_apply, eq_comm]
  have hcoord_ker : ∀ u, (∀ i : Fin d, coord i u = 0) → u ∈ R := by
    intro u hu
    have hpw0 : projW u = 0 := by
      apply bW.repr.injective
      ext i
      simpa [coord] using hu i
    have := hsub_R u
    simpa [hpw0] using this
  by_cases hd4 : d ≤ 4
  · let φ : Fin 4 → (Fin n → F) →ₗ[F] F := fun i =>
      if h : i.val < d then coord ⟨i.val, h⟩ else 0
    let e : Fin 4 → (Fin n → F) := fun i =>
      if h : i.val < d then (bW ⟨i.val, h⟩).1 else 0
    have hdecomp_d : ∀ x, x + ∑ i : Fin d, coord i x • (bW i).1 ∈ R := by
      intro x
      apply hcoord_ker
      intro j
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hcoord_dual]
      rw [Finset.sum_eq_single j]
      · simp [f_add_self]
      · intro i _ hij; simp [Ne.symm hij]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hsum_eq : ∀ x, (∑ i : Fin 4, φ i x • e i) = ∑ i : Fin d, coord i x • (bW i).1 := by
      intro x
      have h1 : (∑ i : Fin 4, φ i x • e i) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin 4 => i.val < d), φ i x • e i := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
        rw [Finset.mem_filter] at hi
        push Not at hi
        have hnot : ¬ (i.val < d) := not_lt.mpr (hi (Finset.mem_univ i))
        simp [φ, hnot]
      rw [h1]
      refine Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin d)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i1 _ i2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
      · intro j _
        exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
      · intro i hi
        have hlt : i.val < d := (Finset.mem_filter.mp hi).2
        simp [φ, e, hlt]
    have hproj4 : ∀ x v w, thirdF g (x + ∑ i : Fin 4, φ i x • e i) v w = 0 := fun x v w => by
      rw [hsum_eq x]
      exact (hR _).mp (hdecomp_d x) v w
    exact ⟨φ 0, φ 1, thirdF g (e 0) (e 1) (e 2) • φ 2 + thirdF g (e 0) (e 1) (e 3) • φ 3,
      thirdF g (e 0) (e 2) (e 3) • φ 0 + thirdF g (e 1) (e 2) (e 3) • φ 1, φ 2, φ 3,
      wedge3_on_four (thirdF g) (thirdF_add_left hg) (thirdF_add_mid hg) (thirdF_add_right hg)
        (thirdF_alt_12 g) (thirdF_alt_23 g) (thirdF_symm_12 g) (thirdF_symm_23 g) φ e hproj4⟩
  · -- Case d = 5: dualize 3-form on F^5 to a 5x5 alternating matrix A of rank ≤ 4 < 5
    have hW5 : Module.finrank F W = 5 := by omega
    let bW5 : Module.Basis (Fin 5) F W := Module.finBasisOfFinrankEq F W hW5
    let e5 : Fin 5 → (Fin n → F) := fun i => (bW5 i).1
    let c5 : Fin 5 → (Fin n → F) →ₗ[F] F := fun i => (bW5.coord i).comp projW
    have hdual5 : ∀ i j : Fin 5, c5 i (e5 j) = if i = j then 1 else 0 := by
      intro i j
      simp [c5, e5, hprojW_W, bW5.coord_apply, bW5.repr_self, Finsupp.single_apply, eq_comm]
    have hcoord_ker5 : ∀ u, (∀ i : Fin 5, c5 i u = 0) → u ∈ R := by
      intro u hu
      have hpw0 : projW u = 0 := by
        apply bW5.repr.injective
        ext i
        simpa [c5] using hu i
      have := hsub_R u
      simpa [hpw0] using this
    -- Define the 5x5 alternating matrix A(i,j) = thirdF g e_a e_b e_c where {a,b,c} = univ \ {i,j}
    let Afun : Fin 5 → Fin 5 → F := fun i j =>
      if i = j then 0
      else
        let rem := (Finset.univ.erase i).erase j
        let l := rem.sort (· ≤ ·)
        thirdF g (e5 (l.getD 0 0)) (e5 (l.getD 1 0)) (e5 (l.getD 2 0))
    have hA_diag : ∀ i, Afun i i = 0 := fun i => by simp [Afun]
    have hA_symm : ∀ i j, Afun i j = Afun j i := by
      intro i j
      by_cases hij : i = j
      · subst hij; rfl
      · dsimp only [Afun]
        simp only [hij, Ne.symm hij, ↓reduceIte]
        have heq : (Finset.univ.erase i).erase j = (Finset.univ.erase j).erase i := by
          ext x; simp [and_comm]
        rw [heq]
    let ωA : (Fin 5 → F) →ₗ[F] (Fin 5 → F) →ₗ[F] F :=
      { toFun := fun u =>
          { toFun := fun v => ∑ i : Fin 5, ∑ j : Fin 5, Afun i j * u i * v j
            map_add' := fun v1 v2 => by
              simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
            map_smul' := fun s v => by
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
        map_add' := fun u1 u2 => LinearMap.ext fun v => by
          change (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * (u1 + u2) i * v j) =
            (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * u1 i * v j) +
            (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * u2 i * v j)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
        map_smul' := fun s u => LinearMap.ext fun v => by
          change (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * (s • u) i * v j) =
            s * (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * u i * v j)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring }
    have hωA_alt : ∀ u, ωA u u = 0 := by
      intro u
      change (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * u i * u j) = 0
      have hpair : ∀ i j : Fin 5, Afun i j * u i * u j = Afun j i * u j * u i := fun i j => by
        rw [hA_symm i j]; ring
      -- Split into i < j, i = j, i > j
      have hsplit : (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * u i * u j) =
          (∑ i : Fin 5, ∑ j : Fin 5, if i < j then Afun i j * u i * u j else 0) +
          (∑ i : Fin 5, ∑ j : Fin 5, if j < i then Afun i j * u i * u j else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases lt_trichotomy i j with hij | rfl | hji
        · simp [hij, not_lt.mpr (le_of_lt hij)]
        · simp [hA_diag]
        · simp [hji, not_lt.mpr (le_of_lt hji)]
      rw [hsplit]
      have hswap : (∑ i : Fin 5, ∑ j : Fin 5, if j < i then Afun i j * u i * u j else 0) =
          (∑ i : Fin 5, ∑ j : Fin 5, if i < j then Afun i j * u i * u j else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · exact hpair j i
        · rfl
      rw [hswap, f_add_self]
    obtain ⟨rA, hrA⟩ := altBil_even_rank ωA hωA_alt
    have hrA_le5 : bilRank ωA ≤ 5 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker ωA
      rw [Module.finrank_fin_fun] at hrn
      dsimp only [bilRank]; omega
    have hkerA_pos : 0 < Module.finrank F (LinearMap.ker ωA) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker ωA
      rw [Module.finrank_fin_fun] at hrn
      dsimp only [bilRank] at hrA hrA_le5; omega
    have hkerA_ne : LinearMap.ker ωA ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hkerA_pos; omega
    obtain ⟨cv, hcv_mem, hcv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerA_ne
    have hcv_eq : ∀ k : Fin 5, ∑ j : Fin 5, Afun k j * cv j = 0 := by
      intro k
      rw [LinearMap.mem_ker] at hcv_mem
      have h := congrArg (fun f => f (unitF k)) hcv_mem
      simp only [ωA, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at h
      have h2 : (∑ i : Fin 5, ∑ j : Fin 5, Afun i j * cv i * unitF k j) =
          ∑ i : Fin 5, Afun k i * cv i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single k]
        · simp [unitF, hA_symm i k]
        · intro j _ hjk; simp [unitF, Ne.symm hjk]
        · intro hm; exact absurd (Finset.mem_univ k) hm
      rw [h2] at h
      exact h
    have hex_i0 : ∃ i0 : Fin 5, cv i0 = 1 := by
      by_contra h
      push Not at h
      apply hcv_ne
      funext i
      rcases f_eq_zero_or_one (cv i) with h0 | h1
      · exact h0
      · exact absurd h1 (h i)
    rcases hex_i0 with ⟨i0, hci0⟩
    let α : (Fin n → F) →ₗ[F] F := ∑ i : Fin 5, cv i • c5 i
    have hα_e : ∀ j : Fin 5, α (e5 j) = cv j := by
      intro j
      simp only [α, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hdual5]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [hij]
      · intro hm; exact absurd (Finset.mem_univ j) hm
    have hα_i0 : α (e5 i0) = 1 := by rw [hα_e, hci0]
    -- Show Afun k j = thirdF g (e5 a) (e5 b) (e5 c) whenever {k, j, a, b, c} = univ (pairwise distinct)
    have hA_triple : ∀ (k j a b c : Fin 5),
        k ≠ j → k ≠ a → k ≠ b → k ≠ c → j ≠ a → j ≠ b → j ≠ c →
        a ≠ b → a ≠ c → b ≠ c →
        Afun k j = thirdF g (e5 a) (e5 b) (e5 c) := by
      intro k j a b c hkj hka hkb hkc hja hjb hjc hab hac hbc
      dsimp only [Afun]
      simp only [hkj, ↓reduceIte]
      set rem := (Finset.univ.erase k).erase j
      have hrem_eq : rem = {a, b, c} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hnot
          push Not at hnot
          have hmem_rem : x ∈ rem := hx
          have hxk : x ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hmem_rem).2).1
          have hxj : x ≠ j := (Finset.mem_erase.mp hmem_rem).1
          have hcard6 : ({k, j, a, b, c, x} : Finset (Fin 5)).card = 6 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [Ne.symm hnot.2.2]
            · simp [hbc, Ne.symm hnot.2.1]
            · simp [hab, hac, Ne.symm hnot.1]
            · simp [hja, hjb, hjc, Ne.symm hxj]
            · simp [hkj, hka, hkb, hkc, Ne.symm hxk]
          have hle5 : ({k, j, a, b, c, x} : Finset (Fin 5)).card ≤ 5 := by
            have := Finset.card_le_univ ({k, j, a, b, c, x} : Finset (Fin 5))
            simpa using this
          omega
        · have hcard3 : ({a, b, c} : Finset (Fin 5)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [hbc]
            · simp [hab, hac]
          have hrem_card : rem.card = 3 := by
            dsimp only [rem]
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hkj, Finset.mem_univ j⟩),
              Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
          omega
      set l := rem.sort (· ≤ ·)
      have hlen : l.length = 3 := by
        rw [Finset.length_sort, hrem_eq, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hbc]
        · simp [hab, hac]
      have hnd : l.Nodup := Finset.sort_nodup _ _
      rcases List.length_eq_three.mp hlen with ⟨x0, x1, x2, hl⟩
      have hmem_l : ∀ z, z ∈ l ↔ z = a ∨ z = b ∨ z = c := fun z => by
        rw [Finset.mem_sort, hrem_eq]; simp
      have hx0 : x0 = a ∨ x0 = b ∨ x0 = c := (hmem_l x0).mp (by rw [hl]; simp)
      have hx1 : x1 = a ∨ x1 = b ∨ x1 = c := (hmem_l x1).mp (by rw [hl]; simp)
      have hx2 : x2 = a ∨ x2 = b ∨ x2 = c := (hmem_l x2).mp (by rw [hl]; simp)
      rw [hl] at hnd ⊢
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
      rcases hnd with ⟨⟨h01, h02⟩, h12, _⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rcases hx0 with rfl | rfl | rfl
      · rcases hx1 with rfl | rfl | rfl
        · exact absurd rfl h01
        · rcases hx2 with rfl | rfl | rfl
          · exact absurd rfl h02
          · exact absurd rfl h12
          · rfl
        · rcases hx2 with rfl | rfl | rfl
          · exact absurd rfl h02
          · exact thirdF_symm_23 g _ _ _
          · exact absurd rfl h12
      · rcases hx1 with rfl | rfl | rfl
        · rcases hx2 with rfl | rfl | rfl
          · exact absurd rfl h12
          · exact absurd rfl h02
          · exact thirdF_symm_12 g _ _ _
        · exact absurd rfl h01
        · rcases hx2 with rfl | rfl | rfl
          · rw [thirdF_symm_23, thirdF_symm_12]
          · exact absurd rfl h02
          · exact absurd rfl h12
      · rcases hx1 with rfl | rfl | rfl
        · rcases hx2 with rfl | rfl | rfl
          · exact absurd rfl h12
          · rw [thirdF_symm_12, thirdF_symm_23]
          · exact absurd rfl h02
        · rcases hx2 with rfl | rfl | rfl
          · rw [thirdF_symm_12, thirdF_symm_23, thirdF_symm_12]
          · exact absurd rfl h12
          · exact absurd rfl h02
        · exact absurd rfl h01
    -- Define the 4-element basis of ker α ∩ W: v j = e5 j + cv j • e5 i0 for j ≠ i0
    let v : Fin 5 → (Fin n → F) := fun j => e5 j + cv j • e5 i0
    have hT_v : ∀ a b c : Fin 5, thirdF g (v a) (v b) (v c) = 0 := by
      intro a b c
      by_cases ha0 : a = i0
      · subst ha0; simp [v, hci0, vec_add_self, thirdF_zero_left]
      by_cases hb0 : b = i0
      · subst hb0; rw [thirdF_symm_12]; simp [v, hci0, vec_add_self, thirdF_zero_left]
      by_cases hc0 : c = i0
      · subst hc0; rw [thirdF_symm_23, thirdF_symm_12]; simp [v, hci0, vec_add_self, thirdF_zero_left]
      by_cases hab : a = b
      · subst hab; exact thirdF_alt_12 g _ _
      by_cases hac : a = c
      · subst hac; exact thirdF_alt_13 g _ _
      by_cases hbc : b = c
      · subst hbc; exact thirdF_alt_23 g _ _
      -- Find unique k ∈ Fin 5 \ {i0, a, b, c}
      have hex_k : ∃ k : Fin 5, k ≠ i0 ∧ k ≠ a ∧ k ≠ b ∧ k ≠ c := by
        have hcard : ({i0, a, b, c} : Finset (Fin 5)).card ≤ 4 := by
          exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
            (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
              (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))))
        have hne : (Finset.univ \ ({i0, a, b, c} : Finset (Fin 5))).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hsub
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_univ, Fintype.card_fin] at h1
          omega
        rcases hne with ⟨k, hk⟩
        rw [Finset.mem_sdiff] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        exact ⟨k, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩
      rcases hex_k with ⟨k, hki0, hka, hkb, hkc⟩
      dsimp only [v]
      simp only [thirdF_add_left hg, thirdF_add_mid hg, thirdF_add_right hg,
        thirdF_smul_left hg, thirdF_smul_mid hg, thirdF_smul_right hg,
        thirdF_alt_12, thirdF_alt_13, thirdF_alt_23, mul_zero, add_zero, zero_add]
      have h1 := hA_triple k i0 a b c hki0 hka hkb hkc (Ne.symm ha0) (Ne.symm hb0) (Ne.symm hc0) hab hac hbc
      have h2 := hA_triple k a i0 b c hka hki0 hkb hkc ha0 hab hac (Ne.symm hb0) (Ne.symm hc0) hbc
      have h3 := hA_triple k b a i0 c hkb hka hki0 hkc (Ne.symm hab) hb0 hbc ha0 hac (Ne.symm hc0)
      have h4 := hA_triple k c a b i0 hkc hka hkb hki0 (Ne.symm hac) (Ne.symm hbc) hc0 hab ha0 hb0
      rw [← h1, ← h2, ← h3, ← h4]
      have hsum := hcv_eq k
      have huniv : Finset.univ = ({k, i0, a, b, c} : Finset (Fin 5)) := by
        symm
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        rw [Finset.card_univ, Fintype.card_fin]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hbc]
        · simp [hab, hac]
        · simp [Ne.symm ha0, Ne.symm hb0, Ne.symm hc0]
        · simp [hki0, hka, hkb, hkc]
      rw [huniv] at hsum
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
        Finset.sum_singleton] at hsum
      · rw [hA_diag k, zero_mul, zero_add, hci0, mul_one] at hsum
        rw [← hsum]; ring
      · simp [hbc]
      · simp [hab, hac]
      · simp [Ne.symm ha0, Ne.symm hb0, Ne.symm hc0]
      · simp [hki0, hka, hkb, hkc]
    -- Show T vanishes on ker α
    have hT_ker : ∀ x y z, α x = 0 → α y = 0 → α z = 0 → thirdF g x y z = 0 := by
      have hproj_v : ∀ x, α x = 0 → x + ∑ j : Fin 5, c5 j x • v j ∈ R := by
        intro x hαx
        apply hcoord_ker5
        intro t
        simp only [map_add, map_sum, map_smul, smul_eq_mul, v, hdual5]
        by_cases ht : t = i0
        · rw [ht]
          have h1 : (∑ j : Fin 5, c5 j x * ((if i0 = j then 1 else 0) + cv j * 1)) =
              c5 i0 x + α x := by
            simp only [mul_add, Finset.sum_add_distrib, mul_one]
            congr 1
            · rw [Finset.sum_eq_single i0]
              · simp
              · intro j _ hji; simp [Ne.symm hji]
              · intro hm; exact absurd (Finset.mem_univ i0) hm
            · simp only [α, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
              refine Finset.sum_congr rfl fun j _ => mul_comm _ _
          simp only [↓reduceIte, mul_one] at h1 ⊢
          rw [h1, hαx, add_zero, f_add_self]
        · have h1 : (∑ j : Fin 5, c5 j x * ((if t = j then 1 else 0) + cv j * (if t = i0 then 1 else 0))) =
              c5 t x := by
            simp only [ht, ↓reduceIte, mul_zero, add_zero]
            rw [Finset.sum_eq_single t]
            · simp
            · intro j _ hjt; simp [Ne.symm hjt]
            · intro hm; exact absurd (Finset.mem_univ t) hm
          rw [h1, f_add_self]
      have hT_sum1 : ∀ (s : Finset (Fin 5)) (f : Fin 5 → (Fin n → F)) y z,
          thirdF g (∑ i ∈ s, f i) y z = ∑ i ∈ s, thirdF g (f i) y z := by
        intro s f y z; classical
        induction s using Finset.induction with
        | empty => exact thirdF_zero_left g y z
        | @insert i s hi ih => rw [Finset.sum_insert hi, thirdF_add_left hg, ih, Finset.sum_insert hi]
      have hT_sum2 : ∀ (s : Finset (Fin 5)) (f : Fin 5 → (Fin n → F)) x z,
          thirdF g x (∑ i ∈ s, f i) z = ∑ i ∈ s, thirdF g x (f i) z := fun s f x z => by
        rw [thirdF_symm_12, hT_sum1]; refine Finset.sum_congr rfl fun i _ => thirdF_symm_12 g _ _ _
      have hT_sum3 : ∀ (s : Finset (Fin 5)) (f : Fin 5 → (Fin n → F)) x y,
          thirdF g x y (∑ i ∈ s, f i) = ∑ i ∈ s, thirdF g x y (f i) := fun s f x y => by
        rw [thirdF_symm_23, hT_sum2]; refine Finset.sum_congr rfl fun i _ => thirdF_symm_23 g _ _ _
      intro x y z hx hy hz
      have hx' : x = (∑ j : Fin 5, c5 j x • v j) + (x + ∑ j : Fin 5, c5 j x • v j) := by
        funext t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
      have hy' : y = (∑ j : Fin 5, c5 j y • v j) + (y + ∑ j : Fin 5, c5 j y • v j) := by
        funext t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
      have hz' : z = (∑ j : Fin 5, c5 j z • v j) + (z + ∑ j : Fin 5, c5 j z • v j) := by
        funext t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
      rw [hx', thirdF_add_left hg, (hR _).mp (hproj_v x hx), add_zero]
      have hzero_y : thirdF g (∑ j : Fin 5, c5 j x • v j) (y + ∑ j : Fin 5, c5 j y • v j) z = 0 := by
        rw [thirdF_symm_12]; exact (hR _).mp (hproj_v y hy) _ _
      rw [hy', thirdF_add_mid hg, hzero_y, add_zero]
      have hzero_z : thirdF g (∑ j : Fin 5, c5 j x • v j) (∑ j : Fin 5, c5 j y • v j) (z + ∑ j : Fin 5, c5 j z • v j) = 0 := by
        rw [thirdF_symm_23, thirdF_symm_12]; exact (hR _).mp (hproj_v z hz) _ _
      rw [hz', thirdF_add_right hg, hzero_z, add_zero]
      rw [hT_sum1]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hT_sum2]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [hT_sum3]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [thirdF_smul_left hg, thirdF_smul_mid hg, thirdF_smul_right hg, hT_v a b c]
      simp
    -- Now let ω := thirdLin g hg (e5 i0) restricted via projection π(x) = x + α x • e5 i0
    let π : (Fin n → F) →ₗ[F] (Fin n → F) := LinearMap.id + α.smulRight (e5 i0)
    have hα_π : ∀ x, α (π x) = 0 := by
      intro x; simp [π, map_add, map_smul, hα_i0, f_add_self]
    let ω : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F := thirdLin g hg (e5 i0)
    have hω_alt : ∀ u, ω u u = 0 := fun u => thirdF_alt_23 g (e5 i0) u
    have hω_rank : bilRank ω ≤ 4 := by
      have hker_le : R ⊔ (F ∙ e5 i0) ≤ LinearMap.ker ω := by
        refine sup_le ?_ ?_
        · intro r hr; rw [LinearMap.mem_ker]; apply LinearMap.ext; intro w
          exact (hR r).mp hr (e5 i0) w |> fun h => by rw [thirdF_symm_12] at h; exact h
        · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]; apply LinearMap.ext; intro w
          exact thirdF_alt_12 g (e5 i0) w
      have hnotmem : e5 i0 ∉ R := by
        intro hmem
        have := hdual5 i0 i0
        simp only [↓reduceIte, c5, LinearMap.comp_apply, hprojW_R _ hmem, map_zero] at this
        exact one_ne_zero this.symm
      have hdisj : Disjoint R (F ∙ e5 i0) := by
        rw [Submodule.disjoint_span_singleton]
        intro h
        exact absurd h hnotmem
      have hker_ge : Module.finrank F R + 1 ≤ Module.finrank F (LinearMap.ker ω) := by
        have h1 := Submodule.finrank_mono hker_le
        have h2 := Submodule.finrank_sup_add_finrank_inf_eq R (F ∙ e5 i0)
        rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, finrank_span_singleton] at h2
        · omega
        · intro h0; apply hnotmem; rw [h0]; exact R.zero_mem
      have hrn := LinearMap.finrank_range_add_finrank_ker ω
      rw [Module.finrank_fin_fun] at hrn
      dsimp only [bilRank]; omega
    obtain ⟨β₁', γ₁', β₂', γ₂', hω⟩ := altBil_rank_le_four ω hω_alt hω_rank
    let β₁ := β₁'.comp π
    let γ₁ := γ₁'.comp π
    let β₂ := β₂'.comp π
    let γ₂ := γ₂'.comp π
    refine ⟨α, β₁, γ₁, α, β₂, γ₂, fun a b c => ?_⟩
    have ha : a = α a • e5 i0 + π a := by
      funext i; simp only [π, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; simp [show (2 : F) = 0 by decide]
    have hb : b = α b • e5 i0 + π b := by
      funext i; simp only [π, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; simp [show (2 : F) = 0 by decide]
    have hc : c = α c • e5 i0 + π c := by
      funext i; simp only [π, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; simp [show (2 : F) = 0 by decide]
    conv_lhs => rw [ha, hb, hc]
    simp only [thirdF_add_left hg, thirdF_add_mid hg, thirdF_add_right hg,
      thirdF_smul_left hg, thirdF_smul_mid hg, thirdF_smul_right hg,
      thirdF_alt_12, thirdF_alt_13, thirdF_alt_23,
      hT_ker (π a) (π b) (π c) (hα_π a) (hα_π b) (hα_π c),
      mul_zero, add_zero, zero_add]
    have h1 : thirdF g (e5 i0) (π b) (π c) = ω (π b) (π c) := rfl
    have h2 : thirdF g (π a) (e5 i0) (π c) = ω (π a) (π c) := thirdF_symm_12 g _ _ _
    have h3 : thirdF g (π a) (π b) (e5 i0) = ω (π a) (π b) := by
      rw [thirdF_symm_23, thirdF_symm_12]; rfl
    rw [h1, h2, h3, hω (π b) (π c), hω (π a) (π c), hω (π a) (π b)]
    simp only [wedge3, β₁, γ₁, β₂, γ₂, LinearMap.comp_apply]
    ring

private lemma exists_two_wedge3_of_eq_six {n : ℕ} (g : (Fin n → F) → F)
    (R : Submodule F (Fin n → F)) (hg : isCubic g)
    (hR : ∀ u, u ∈ R ↔ ∀ v w, thirdF g u v w = 0)
    (hd : n - Module.finrank F R = 6)
    (u v : Fin n → F)
    (hu : bilRank (thirdLin g hg u) = 2)
    (hv : bilRank (thirdLin g hg v) = 2)
    (huv : bilRank (thirdLin g hg (u + v)) = 4) :
    ∃ α₁ β₁ γ₁ α₂ β₂ γ₂ : (Fin n → F) →ₗ[F] F,
      ∀ a b c, thirdF g a b c = wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c := by
  let Mu := thirdLin g hg u
  let Mv := thirdLin g hg v
  let Muv := thirdLin g hg (u + v)
  have hMuv_eq : Muv = Mu + Mv := by
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
    exact thirdF_add_left hg u v a b
  obtain ⟨β₁, γ₁, hMu, hker_u⟩ := altBil_rank_eq_two Mu (fun w => thirdF_alt_23 g u w) hu
  obtain ⟨β₂, γ₂, hMv, hker_v⟩ := altBil_rank_eq_two Mv (fun w => thirdF_alt_23 g v w) hv
  have hR_vanish : ∀ r ∈ R, β₁ r = 0 ∧ γ₁ r = 0 ∧ β₂ r = 0 ∧ γ₂ r = 0 := by
    intro r hr
    have hr1 : Mu r = 0 := by
      apply LinearMap.ext; intro w; exact (hR r).mp hr u w |> fun h => by rw [thirdF_symm_12] at h; exact h
    have hr2 : Mv r = 0 := by
      apply LinearMap.ext; intro w; exact (hR r).mp hr v w |> fun h => by rw [thirdF_symm_12] at h; exact h
    exact ⟨(hker_u r hr1).1, (hker_u r hr1).2, (hker_v r hr2).1, (hker_v r hr2).2⟩
  let φ4 : Fin 4 → (Fin n → F) →ₗ[F] F := ![β₁, γ₁, β₂, γ₂]
  let K4 : Submodule F (Fin n → F) := ⨅ i : Fin 4, LinearMap.ker (φ4 i)
  have hK4_sub_ker : K4 ≤ LinearMap.ker Muv := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have hb1 : β₁ x = 0 := hx 0
    have hg1 : γ₁ x = 0 := hx 1
    have hb2 : β₂ x = 0 := hx 2
    have hg2 : γ₂ x = 0 := hx 3
    rw [LinearMap.mem_ker]
    apply LinearMap.ext; intro w
    rw [hMuv_eq, LinearMap.add_apply, LinearMap.add_apply, hMu x w, hMv x w]
    simp [hb1, hg1, hb2, hg2]
  have hcodim_K4 : Module.finrank F K4 + 4 = n := by
    let Φ4 : (Fin n → F) →ₗ[F] (Fin 4 → F) := LinearMap.pi φ4
    have hker4 : LinearMap.ker Φ4 = K4 := LinearMap.ker_pi φ4
    have hrn4 := LinearMap.finrank_range_add_finrank_ker Φ4
    rw [Module.finrank_fin_fun, hker4] at hrn4
    have hrg4_le : Module.finrank F (LinearMap.range Φ4) ≤ 4 := by
      have := Submodule.finrank_le (LinearMap.range Φ4)
      rwa [Module.finrank_fin_fun] at this
    have hrn_uv := LinearMap.finrank_range_add_finrank_ker Muv
    rw [Module.finrank_fin_fun] at hrn_uv
    have hmono := Submodule.finrank_mono hK4_sub_ker
    have huv' : Module.finrank F (LinearMap.range Muv) = 4 := huv
    omega
  obtain ⟨e4, he4⟩ := exists_dual_coords φ4 hcodim_K4
  have hdual4 :
      β₁ (e4 0) = 1 ∧ γ₁ (e4 0) = 0 ∧ β₂ (e4 0) = 0 ∧ γ₂ (e4 0) = 0 ∧
      β₁ (e4 1) = 0 ∧ γ₁ (e4 1) = 1 ∧ β₂ (e4 1) = 0 ∧ γ₂ (e4 1) = 0 ∧
      β₁ (e4 2) = 0 ∧ γ₁ (e4 2) = 0 ∧ β₂ (e4 2) = 1 ∧ γ₂ (e4 2) = 0 ∧
      β₁ (e4 3) = 0 ∧ γ₁ (e4 3) = 0 ∧ β₂ (e4 3) = 0 ∧ γ₂ (e4 3) = 1 := by
    refine ⟨by simpa [φ4] using he4 0 0, by simpa [φ4] using he4 1 0,
      by simpa [φ4] using he4 2 0, by simpa [φ4] using he4 3 0,
      by simpa [φ4] using he4 0 1, by simpa [φ4] using he4 1 1,
      by simpa [φ4] using he4 2 1, by simpa [φ4] using he4 3 1,
      by simpa [φ4] using he4 0 2, by simpa [φ4] using he4 1 2,
      by simpa [φ4] using he4 2 2, by simpa [φ4] using he4 3 2,
      by simpa [φ4] using he4 0 3, by simpa [φ4] using he4 1 3,
      by simpa [φ4] using he4 2 3, by simpa [φ4] using he4 3 3⟩
  -- Show u and v are in K4!
  have hu_K4 : u ∈ K4 := by
    have hMu_u : Mu u = 0 := LinearMap.ext fun w => thirdF_alt_12 g u w
    have h1 := hker_u u hMu_u
    have h2 : ∀ w, β₁ v * γ₁ w + γ₁ v * β₁ w = β₂ u * γ₂ w + γ₂ u * β₂ w := by
      intro w
      have hsym : thirdF g u v w = thirdF g v u w := thirdF_symm_12 g u v w
      change Mu v w = Mv u w at hsym
      rw [hMu v w, hMv u w] at hsym
      exact hsym
    have hβ2u : β₂ u = 0 := by
      have h := h2 (e4 3)
      simp only [hdual4, mul_zero, mul_one, add_zero, zero_add] at h
      exact h.symm
    have hγ2u : γ₂ u = 0 := by
      have h := h2 (e4 2)
      simp only [hdual4, mul_zero, mul_one, add_zero, zero_add] at h
      exact h.symm
    rw [Submodule.mem_iInf]
    intro i; fin_cases i
    · exact h1.1
    · exact h1.2
    · exact hβ2u
    · exact hγ2u
  have hv_K4 : v ∈ K4 := by
    have hMv_v : Mv v = 0 := LinearMap.ext fun w => thirdF_alt_12 g v w
    have h1 := hker_v v hMv_v
    have h2 : ∀ w, β₁ v * γ₁ w + γ₁ v * β₁ w = β₂ u * γ₂ w + γ₂ u * β₂ w := by
      intro w
      have hsym : thirdF g u v w = thirdF g v u w := thirdF_symm_12 g u v w
      change Mu v w = Mv u w at hsym
      rw [hMu v w, hMv u w] at hsym
      exact hsym
    have hβ1v : β₁ v = 0 := by
      have h := h2 (e4 1)
      simp only [hdual4, mul_zero, mul_one, add_zero, zero_add] at h
      exact h
    have hγ1v : γ₁ v = 0 := by
      have h := h2 (e4 0)
      simp only [hdual4, mul_zero, mul_one, add_zero, zero_add] at h
      exact h
    rw [Submodule.mem_iInf]
    intro i; fin_cases i
    · exact hβ1v
    · exact hγ1v
    · exact h1.1
    · exact h1.2
  -- Show R ≤ K4 and R ∩ span{u, v} = ⊥ and K4 = R ⊔ span{u, v}
  have hR_le_K4 : R ≤ K4 := by
    intro r hr
    rw [Submodule.mem_iInf]
    have hv := hR_vanish r hr
    intro i; fin_cases i
    · exact hv.1
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2
  have huv_indep_mod_R : ∀ c1 c2 : F, c1 • u + c2 • v ∈ R → c1 = 0 ∧ c2 = 0 := by
    intro c1 c2 hmem
    have hM0 : thirdLin g hg (c1 • u + c2 • v) = 0 :=
      LinearMap.ext fun a => LinearMap.ext fun b => (hR _).mp hmem a b
    have hr0 : bilRank (thirdLin g hg (c1 • u + c2 • v)) = 0 := by
      rw [hM0]; simp [bilRank]
    rcases f_eq_zero_or_one c1 with rfl | rfl <;> rcases f_eq_zero_or_one c2 with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp only [zero_smul, one_smul, zero_add] at hr0; omega
    · simp only [zero_smul, one_smul, add_zero] at hr0; omega
    · simp only [one_smul] at hr0; omega
  have hind_uv : LinearIndependent F ![u, v] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hc
    have h0 : c 0 • u + c 1 • v ∈ R := by rw [hc]; exact R.zero_mem
    have ⟨h00, h01⟩ := huv_indep_mod_R (c 0) (c 1) h0
    fin_cases i
    · exact h00
    · exact h01
  have hspan_uv_rank : Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) = 2 := by
    have hset : ({u, v} : Set (Fin n → F)) = Set.range ![u, v] := by
      ext x; simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hset, finrank_span_eq_card hind_uv]; simp
  have hdisj_R_uv : Disjoint R (Submodule.span F ({u, v} : Set (Fin n → F))) := by
    rw [Submodule.disjoint_def]
    intro x hxR hxuv
    rw [Submodule.mem_span_pair] at hxuv
    rcases hxuv with ⟨c1, c2, rfl⟩
    have ⟨h1, h2⟩ := huv_indep_mod_R c1 c2 hxR
    simp [h1, h2]
  have hK4_eq : R ⊔ Submodule.span F ({u, v} : Set (Fin n → F)) = K4 := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine sup_le hR_le_K4 (Submodule.span_le.mpr ?_)
      rintro x (rfl | rfl)
      · exact hu_K4
      · exact hv_K4
    · have hsum := Submodule.finrank_sup_add_finrank_inf_eq R (Submodule.span F ({u, v} : Set (Fin n → F)))
      rw [disjoint_iff.mp hdisj_R_uv, finrank_bot, add_zero, hspan_uv_rank] at hsum
      have hR_le_n : Module.finrank F R ≤ n := by
        have := Submodule.finrank_le R; rwa [Module.finrank_fin_fun] at this
      omega
  -- Construct linear maps α₁, α₂ extracting u, v coordinates of πK4(x) := x + ∑ i, φ4 i x • e4 i ∈ K4
  let πK4 : (Fin n → F) →ₗ[F] K4 :=
    { toFun := fun x =>
        ⟨x + ∑ i : Fin 4, φ4 i x • e4 i, by
          rw [Submodule.mem_iInf]
          intro j
          simp only [LinearMap.mem_ker, map_add, map_sum, map_smul, smul_eq_mul, he4]
          rw [Finset.sum_eq_single j]
          · simp [f_add_self]
          · intro i _ hij; simp [Ne.symm hij]
          · intro hm; exact absurd (Finset.mem_univ j) hm⟩
      map_add' := fun x y => by
        apply Subtype.ext; simp only [Submodule.coe_add, map_add, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := fun s x => by
        apply Subtype.ext; simp only [SetLike.val_smul, map_smul, smul_eq_mul, Finset.smul_sum,
          smul_add, mul_smul, RingHom.id_apply] }
  let S_uv : Submodule F (Fin n → F) := Submodule.span F ({u, v} : Set (Fin n → F))
  have hcompl_in_K4 : IsCompl (R.comap K4.subtype) (S_uv.comap K4.subtype) := by
    rw [isCompl_iff]
    constructor
    · rw [Submodule.disjoint_def]
      rintro ⟨x, _⟩ hx1 hx2
      exact Subtype.ext (Submodule.disjoint_def.mp hdisj_R_uv x hx1 hx2)
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hxK⟩ _
      rw [← hK4_eq, Submodule.mem_sup] at hxK
      rcases hxK with ⟨r, hr, s, hs, rfl⟩
      have hrK : r ∈ K4 := hR_le_K4 hr
      have hsK : s ∈ K4 := by
        have hle : S_uv ≤ K4 := Submodule.span_le.mpr (by rintro z (rfl | rfl) <;> assumption)
        exact hle hs
      have heq : (⟨r + s, hxK⟩ : K4) = ⟨r, hrK⟩ + ⟨s, hsK⟩ := rfl
      rw [heq]
      exact Submodule.add_mem_sup hr hs
  let proj_uv : K4 →ₗ[F] S_uv.comap K4.subtype :=
    Submodule.projectionOnto (S_uv.comap K4.subtype) (R.comap K4.subtype) hcompl_in_K4.symm
  let uK : S_uv.comap K4.subtype := ⟨⟨u, hu_K4⟩, Submodule.subset_span (by simp)⟩
  let vK : S_uv.comap K4.subtype := ⟨⟨v, hv_K4⟩, Submodule.subset_span (by simp)⟩
  have hind_uvK : LinearIndependent F ![uK, vK] := by
    let emb : S_uv.comap K4.subtype →ₗ[F] (Fin n → F) :=
      K4.subtype.comp (S_uv.comap K4.subtype).subtype
    have hcomp : emb ∘ ![uK, vK] = ![u, v] := by funext i; fin_cases i <;> rfl
    exact LinearIndependent.of_comp emb (by rw [hcomp]; exact hind_uv)
  have hspan_uvK : ⊤ ≤ Submodule.span F (Set.range ![uK, vK]) := by
    rintro ⟨⟨x, hxK⟩, hxS⟩ _
    change x ∈ S_uv at hxS
    rw [Submodule.mem_span_pair] at hxS
    rcases hxS with ⟨c1, c2, hxc⟩
    have heq : (⟨⟨x, hxK⟩, hxS⟩ : S_uv.comap K4.subtype) = c1 • uK + c2 • vK := by
      apply Subtype.ext; apply Subtype.ext; exact hxc.symm
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let b_uv : Module.Basis (Fin 2) F (S_uv.comap K4.subtype) :=
    Module.Basis.mk hind_uvK hspan_uvK
  let α₁ : (Fin n → F) →ₗ[F] F := ((b_uv.coord 0).comp proj_uv).comp πK4
  let α₂ : (Fin n → F) →ₗ[F] F := ((b_uv.coord 1).comp proj_uv).comp πK4
  have hπK4_K4 : ∀ x (hx : x ∈ K4), πK4 x = ⟨x, hx⟩ := by
    intro x hx
    apply Subtype.ext
    rw [Submodule.mem_iInf] at hx
    have hsum : (∑ i : Fin 4, φ4 i x • e4 i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hx i, zero_smul]
    simp [πK4, hsum]
  have hα_R : ∀ r ∈ R, α₁ r = 0 ∧ α₂ r = 0 := by
    intro r hr
    have hπ := hπK4_K4 r (hR_le_K4 hr)
    have hp0 : proj_uv ⟨r, hR_le_K4 hr⟩ = 0 :=
      Submodule.projectionOnto_apply_right hcompl_in_K4.symm ⟨⟨r, hR_le_K4 hr⟩, hr⟩
    simp [α₁, α₂, hπ, hp0]
  have hα_u : α₁ u = 1 ∧ α₂ u = 0 := by
    have hπ := hπK4_K4 u hu_K4
    have hp : proj_uv ⟨u, hu_K4⟩ = uK :=
      Submodule.projectionOnto_apply_left hcompl_in_K4.symm uK
    have hu0 : b_uv 0 = uK := by simp [b_uv]
    constructor
    · simp [α₁, hπ, hp, ← hu0]
    · simp [α₂, hπ, hp, ← hu0]
  have hα_v : α₁ v = 0 ∧ α₂ v = 1 := by
    have hπ := hπK4_K4 v hv_K4
    have hp : proj_uv ⟨v, hv_K4⟩ = vK :=
      Submodule.projectionOnto_apply_left hcompl_in_K4.symm vK
    have hv1 : b_uv 1 = vK := by simp [b_uv]
    constructor
    · simp [α₁, hπ, hp, ← hv1]
    · simp [α₂, hπ, hp, ← hv1]
  -- Define T'(a, b, c) := thirdF g a b c + wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c
  let T' : (Fin n → F) → (Fin n → F) → (Fin n → F) → F := fun a b c =>
    thirdF g a b c + wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c
  have hT'_add1 : ∀ a a' b c, T' (a + a') b c = T' a b c + T' a' b c := by
    intro a a' b c; simp only [T', thirdF_add_left hg, wedge3, map_add]; ring
  have hT'_add2 : ∀ a b b' c, T' a (b + b') c = T' a b c + T' a b' c := by
    intro a b b' c; simp only [T', thirdF_add_mid hg, wedge3, map_add]; ring
  have hT'_add3 : ∀ a b c c', T' a b (c + c') = T' a b c + T' a b c' := by
    intro a b c c'; simp only [T', thirdF_add_right hg, wedge3, map_add]; ring
  have hT'_sym12 : ∀ a b c, T' a b c = T' b a c := by
    intro a b c; simp only [T', thirdF_symm_12 g, wedge3]; ring
  have hT'_sym23 : ∀ a b c, T' a b c = T' a c b := by
    intro a b c; simp only [T', thirdF_symm_23 g, wedge3]; ring
  have hT'_alt12 : ∀ a c, T' a a c = 0 := by
    intro a c; simp only [T', thirdF_alt_12 g, wedge3, zero_add]; ring_nf
    simp [show (2 : F) = 0 by decide]
  have hT'_alt23 : ∀ a b, T' a b b = 0 := by
    intro a b; rw [hT'_sym12, hT'_sym23, hT'_sym12]; exact hT'_alt12 b a
  have hT'_K4 : ∀ x ∈ K4, ∀ y z, T' x y z = 0 := by
    intro x hx y z
    rw [← hK4_eq, Submodule.mem_sup] at hx
    rcases hx with ⟨r, hr, s, hs, rfl⟩
    rw [Submodule.mem_span_pair] at hs
    rcases hs with ⟨c1, c2, rfl⟩
    rw [hT'_add1, hT'_add1]
    have hr0 : T' r y z = 0 := by
      have h1 := (hR r).mp hr y z
      have h2 := hR_vanish r hr
      have h3 := hα_R r hr
      simp [T', wedge3, h1, h2, h3]
    have hu0 : T' u y z = 0 := by
      have h1 : thirdF g u y z = β₁ y * γ₁ z + γ₁ y * β₁ z := hMu y z
      rw [Submodule.mem_iInf] at hu_K4
      have hb1 : β₁ u = 0 := hu_K4 0
      have hg1 : γ₁ u = 0 := hu_K4 1
      have hb2 : β₂ u = 0 := hu_K4 2
      have hg2 : γ₂ u = 0 := hu_K4 3
      simp only [T', h1, wedge3, hα_u, hb1, hg1, hb2, hg2, one_mul, zero_mul, add_zero, zero_add]
      ring_nf; simp [show (2 : F) = 0 by decide]
    have hv0 : T' v y z = 0 := by
      have h1 : thirdF g v y z = β₂ y * γ₂ z + γ₂ y * β₂ z := hMv y z
      rw [Submodule.mem_iInf] at hv_K4
      have hb1 : β₁ v = 0 := hv_K4 0
      have hg1 : γ₁ v = 0 := hv_K4 1
      have hb2 : β₂ v = 0 := hv_K4 2
      have hg2 : γ₂ v = 0 := hv_K4 3
      simp only [T', h1, wedge3, hα_v, hb1, hg1, hb2, hg2, one_mul, zero_mul, add_zero, zero_add]
      ring_nf; simp [show (2 : F) = 0 by decide]
    have hsmul : ∀ (s : F) a, T' (s • a) y z = s * T' a y z := by
      intro s a
      rcases f_eq_zero_or_one s with rfl | rfl
      · simp [T', thirdF_zero_left, wedge3]
      · simp
    rw [hr0, hsmul, hsmul, hu0, hv0]; simp
  have hproj4 : ∀ x y z, T' (x + ∑ i : Fin 4, φ4 i x • e4 i) y z = 0 := fun x y z =>
    hT'_K4 _ (πK4 x).2 y z
  have hT'_eq := wedge3_on_four T' hT'_add1 hT'_add2 hT'_add3 hT'_alt12 hT'_alt23
    hT'_sym12 hT'_sym23 φ4 e4 hproj4
  -- Absorb the 2 wedges of T' directly into α₁ and α₂!
  let α₁' := α₁ + T' (e4 0) (e4 1) (e4 2) • β₂ + T' (e4 0) (e4 1) (e4 3) • γ₂
  let α₂' := α₂ + T' (e4 0) (e4 2) (e4 3) • β₁ + T' (e4 1) (e4 2) (e4 3) • γ₁
  refine ⟨α₁', β₁, γ₁, α₂', β₂, γ₂, fun a b c => ?_⟩
  have h := hT'_eq a b c
  have hφ3 : φ4 3 = γ₂ := rfl
  simp only [φ4, hφ3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  change thirdF g a b c + wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c = _ at h
  have hT_eq : thirdF g a b c = wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c +
      (wedge3 β₁ γ₁ (T' (e4 0) (e4 1) (e4 2) • β₂ + T' (e4 0) (e4 1) (e4 3) • γ₂) a b c +
       wedge3 (T' (e4 0) (e4 2) (e4 3) • β₁ + T' (e4 1) (e4 2) (e4 3) • γ₁) β₂ γ₂ a b c) := by
    have h2 := congrArg (· + (wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c)) h
    have hlhs : thirdF g a b c + wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c +
        (wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c) = thirdF g a b c := by
      ring_nf; simp [show (2 : F) = 0 by decide]
    rw [hlhs] at h2
    rw [h2]; ring
  rw [hT_eq]
  simp only [α₁', α₂', wedge3, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## Section 3: Circuit construction (`⇐` direction, cost `≤ k + m + 2`) -/

private def legalCirc (n : ℕ) (C : Circuit) : Prop :=
  ReadsBack n C ∧
    (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))

private noncomputable def costCirc (C : Circuit) : ℕ :=
  C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))

private def bitsVec (n : ℕ) (u : Fin n → F) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

private lemma bitsVec_length (n : ℕ) (u : Fin n → F) : (bitsVec n u).length = n := by
  simp [bitsVec]

private lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  suffices h : ∀ (gs : List Gate) (acc : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + gs.length from h C.gates x
  intro gs
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

private lemma wires_append_gate (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

private lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (hi : i < l₁.length) (d : α) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_singleton_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma decide_eq_one_iff (a : F) : decide (a = 1) = true ↔ a = 1 := by
  simp

private lemma bool_of_f_add (a b : F) :
    decide (a + b = 1) = !(decide (([decide (a = 1), decide (b = 1)].count true) % 2 = 0)) := by
  revert a b; decide

private lemma bool_of_f_mul (a b : F) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  revert a b; decide

private lemma bool_of_f_not (a : F) :
    decide (a + 1 = 1) = !(decide (a = 1)) := by
  revert a; decide

private structure Builder (k : ℕ) where
  gates : List Gate
  val : ℕ → (Fin k → F) → (Fin k → F) → F
  hreads : ReadsBack (2 * k) ⟨gates, 0⟩
  hlegal : ∀ h ∈ gates, h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))
  hval : ∀ (x y : Fin k → F) (w : ℕ), w < 2 * k + gates.length →
    ((Circuit.mk gates 0).wires (bitsVec k x ++ bitsVec k y)).getD w false = decide (val w x y = 1)

private def Builder.init (k : ℕ) : Builder k where
  gates := []
  val := fun w x y =>
    if h1 : w < k then x ⟨w, h1⟩
    else if h2 : w - k < k then y ⟨w - k, h2⟩
    else 0
  hreads := fun j hj => by simp at hj
  hlegal := fun h hh => by simp at hh
  hval := fun x y w hw => by
    simp only [Circuit.wires, List.foldl_nil, List.length_nil, add_zero] at hw ⊢
    by_cases h1 : w < k
    · have hl : w < (bitsVec k x).length := by rw [bitsVec_length]; exact h1
      rw [getD_append_left _ _ _ hl]
      simp [bitsVec, List.getD_eq_getElem?_getD, h1]
    · have h2 : w - k < k := by omega
      simp only [h1, h2, ↓reduceDIte]
      have hlen : (bitsVec k x).length = k := bitsVec_length k x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : (bitsVec k x).length ≤ w), hlen]
      simp [bitsVec, h2]

private def Builder.push {k : ℕ} (B : Builder k) (g : Gate)
    (hread : ∀ i ∈ g.inputs, i < 2 * k + B.gates.length)
    (hleg : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (f : (Fin k → F) → (Fin k → F) → F)
    (hf : ∀ x y, g.op.eval (g.inputs.map fun i => decide (B.val i x y = 1)) = decide (f x y = 1)) :
    Builder k where
  gates := B.gates ++ [g]
  val := fun w x y => if w = 2 * k + B.gates.length then f x y else B.val w x y
  hreads := fun j hj i hi => by
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < B.gates.length
    · have hgat : gateAt ⟨B.gates ++ [g], 0⟩ j = gateAt ⟨B.gates, 0⟩ j := by
        unfold gateAt; exact getD_append_left B.gates [g] j hlt _
      rw [hgat] at hi
      exact B.hreads j hlt i hi
    · have hj_eq : j = B.gates.length := by omega
      subst hj_eq
      have hgat : gateAt ⟨B.gates ++ [g], 0⟩ B.gates.length = g := by
        unfold gateAt; exact getD_append_singleton_last B.gates g _
      rw [hgat] at hi
      exact hread i hi
  hlegal := fun h hh => by
    rw [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact B.hlegal h hh
    · exact hleg
  hval := fun x y w hw => by
    rw [wires_append_gate]
    have hlen : ((Circuit.mk B.gates 0).wires (bitsVec k x ++ bitsVec k y)).length =
        2 * k + B.gates.length := by
      have h1 := wires_length ⟨B.gates, 0⟩ (bitsVec k x ++ bitsVec k y)
      rw [List.length_append, bitsVec_length, bitsVec_length] at h1
      dsimp only at h1; omega
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < 2 * k + B.gates.length
    · rw [getD_append_left _ _ _ (by omega)]
      have hne : w ≠ 2 * k + B.gates.length := by omega
      simp only [hne, ↓reduceIte]
      exact B.hval x y w hlt
    · have heq : w = 2 * k + B.gates.length := by omega
      subst heq
      rw [← hlen, getD_append_singleton_last, hlen]
      simp only [↓reduceIte]
      have hmap : (g.inputs.map fun i =>
          ((Circuit.mk B.gates 0).wires (bitsVec k x ++ bitsVec k y)).getD i false) =
          (g.inputs.map fun i => decide (B.val i x y = 1)) := by
        refine List.map_congr_left fun i hi => B.hval x y i (hread i hi)
      rw [hmap]
      exact hf x y

private lemma costCirc_push_free {k : ℕ} (B : Builder k) (g : Gate)
    (hread : ∀ i ∈ g.inputs, i < 2 * k + B.gates.length)
    (hleg : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (f : (Fin k → F) → (Fin k → F) → F)
    (hf : ∀ x y, g.op.eval (g.inputs.map fun i => decide (B.val i x y = 1)) = decide (f x y = 1))
    (hfree : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    costCirc ⟨(B.push g hread hleg f hf).gates, 0⟩ = costCirc ⟨B.gates, 0⟩ := by
  simp [costCirc, Builder.push, List.countP_append, hfree]

private lemma costCirc_push_and {k : ℕ} (B : Builder k) (a b : ℕ)
    (ha : a < 2 * k + B.gates.length) (hb : b < 2 * k + B.gates.length) :
    let g : Gate := ⟨.and, [a, b]⟩
    let hread : ∀ i ∈ g.inputs, i < 2 * k + B.gates.length := by
      intro i hi; simp [g] at hi; rcases hi with rfl | rfl <;> assumption
    let hleg : g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
      simp [g]
    let hf : ∀ x y, g.op.eval (g.inputs.map fun i => decide (B.val i x y = 1)) =
        decide (B.val a x y * B.val b x y = 1) := fun x y => by
      simp [g, GateOp.eval, bool_of_f_mul]
    costCirc ⟨(B.push g hread hleg (fun x y => B.val a x y * B.val b x y) hf).gates, 0⟩ =
      costCirc ⟨B.gates, 0⟩ + 1 := by
  simp [costCirc, Builder.push, List.countP_append]

private def Builder.addZero {k : ℕ} (B : Builder k) :
    { p : Builder k × ℕ //
      B.gates.length ≤ p.1.gates.length ∧
      p.2 < 2 * k + p.1.gates.length ∧
      (∀ w < 2 * k + B.gates.length, p.1.val w = B.val w) ∧
      (∀ x y, p.1.val p.2 x y = 0) ∧
      costCirc ⟨p.1.gates, 0⟩ = costCirc ⟨B.gates, 0⟩ } :=
  let g : Gate := ⟨.or, []⟩
  let hread : ∀ i ∈ g.inputs, i < 2 * k + B.gates.length := fun _ h => by simp [g] at h
  let hleg : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
    simp [g]
  let hf : ∀ x y, g.op.eval (g.inputs.map fun i => decide (B.val i x y = 1)) = decide ((0 : F) = 1) :=
    fun _ _ => by simp [g, GateOp.eval]
  let B' := B.push g hread hleg (fun _ _ => 0) hf
  ⟨(B', 2 * k + B.gates.length),
    ⟨by simp [B', Builder.push],
     by simp [B', Builder.push],
     fun w hw => by funext x y; simp [B', Builder.push, ne_of_lt hw],
     fun x y => by simp [B', Builder.push],
     costCirc_push_free B g hread hleg (fun _ _ => 0) hf (by simp [g])⟩⟩

private def Builder.addNot {k : ℕ} (B : Builder k) (a : ℕ) (ha : a < 2 * k + B.gates.length) :
    { p : Builder k × ℕ //
      B.gates.length ≤ p.1.gates.length ∧
      p.2 < 2 * k + p.1.gates.length ∧
      (∀ w < 2 * k + B.gates.length, p.1.val w = B.val w) ∧
      (∀ x y, p.1.val p.2 x y = B.val a x y + 1) ∧
      costCirc ⟨p.1.gates, 0⟩ = costCirc ⟨B.gates, 0⟩ } :=
  let g : Gate := ⟨.not, [a]⟩
  let hread : ∀ i ∈ g.inputs, i < 2 * k + B.gates.length := fun i hi => by
    simp [g] at hi; subst hi; exact ha
  let hleg : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
    simp [g]
  let hf : ∀ x y, g.op.eval (g.inputs.map fun i => decide (B.val i x y = 1)) =
      decide (B.val a x y + 1 = 1) := fun x y => by
    simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, bool_of_f_not]
  let B' := B.push g hread hleg (fun x y => B.val a x y + 1) hf
  ⟨(B', 2 * k + B.gates.length),
    ⟨by simp [B', Builder.push],
     by simp [B', Builder.push],
     fun w hw => by funext x y; simp [B', Builder.push, ne_of_lt hw],
     fun x y => by simp [B', Builder.push],
     costCirc_push_free B g hread hleg _ hf (by simp [g])⟩⟩

private def Builder.addXor {k : ℕ} (B : Builder k) (a b : ℕ)
    (ha : a < 2 * k + B.gates.length) (hb : b < 2 * k + B.gates.length) :
    { p : Builder k × ℕ //
      B.gates.length ≤ p.1.gates.length ∧
      p.2 < 2 * k + p.1.gates.length ∧
      (∀ w < 2 * k + B.gates.length, p.1.val w = B.val w) ∧
      (∀ x y, p.1.val p.2 x y = B.val a x y + B.val b x y) ∧
      costCirc ⟨p.1.gates, 0⟩ = costCirc ⟨B.gates, 0⟩ } :=
  let g1 : Gate := ⟨.mod 2, [a, b]⟩
  let B1 := B.push g1 (fun i hi => by simp [g1] at hi; rcases hi with rfl | rfl <;> assumption)
    (by simp [g1]) (fun x y => B.val a x y + B.val b x y + 1)
    (fun x y => by
      simp only [g1, List.map_cons, List.map_nil, GateOp.eval]
      have h := bool_of_f_add (B.val a x y) (B.val b x y)
      rw [bool_of_f_not, h, Bool.not_not])
  let w1 := 2 * k + B.gates.length
  let res2 := B1.addNot w1 (by simp [B1, Builder.push, w1])
  ⟨res2.val,
    ⟨by have h1 : B.gates.length ≤ B1.gates.length := by simp [B1, Builder.push]
        exact le_trans h1 res2.property.1,
     res2.property.2.1,
     fun w hw => by
       have hw1 : w < 2 * k + B1.gates.length := by simp [B1, Builder.push]; omega
       rw [res2.property.2.2.1 w hw1]
       funext x y; simp [B1, Builder.push, ne_of_lt hw],
     fun x y => by
       rw [res2.property.2.2.2.1 x y]
       simp only [B1, Builder.push, w1, ↓reduceIte]
       rw [add_assoc, f_add_self, add_zero],
     by rw [res2.property.2.2.2.2, costCirc_push_free B g1 _ _ _ _ (by simp [g1])]⟩⟩

private def Builder.addAnd {k : ℕ} (B : Builder k) (a b : ℕ)
    (ha : a < 2 * k + B.gates.length) (hb : b < 2 * k + B.gates.length) :
    { p : Builder k × ℕ //
      B.gates.length ≤ p.1.gates.length ∧
      p.2 < 2 * k + p.1.gates.length ∧
      (∀ w < 2 * k + B.gates.length, p.1.val w = B.val w) ∧
      (∀ x y, p.1.val p.2 x y = B.val a x y * B.val b x y) ∧
      costCirc ⟨p.1.gates, 0⟩ = costCirc ⟨B.gates, 0⟩ + 1 } :=
  let g : Gate := ⟨.and, [a, b]⟩
  let B' := B.push g (fun i hi => by simp [g] at hi; rcases hi with rfl | rfl <;> assumption)
    (by simp [g]) (fun x y => B.val a x y * B.val b x y)
    (fun x y => by simp [g, GateOp.eval, bool_of_f_mul])
  ⟨(B', 2 * k + B.gates.length),
    ⟨by simp [B', Builder.push],
     by simp [B', Builder.push],
     fun w hw => by funext x y; simp [B', Builder.push, ne_of_lt hw],
     fun x y => by simp [B', Builder.push],
     costCirc_push_and B a b ha hb⟩⟩

private def Builder.addSumList {k : ℕ} (B : Builder k) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < 2 * k + B.gates.length) :
    { p : Builder k × ℕ //
      B.gates.length ≤ p.1.gates.length ∧
      p.2 < 2 * k + p.1.gates.length ∧
      (∀ w < 2 * k + B.gates.length, p.1.val w = B.val w) ∧
      (∀ x y, p.1.val p.2 x y = (ws.map (fun w => B.val w x y)).sum) ∧
      costCirc ⟨p.1.gates, 0⟩ = costCirc ⟨B.gates, 0⟩ } := by
  induction ws generalizing B with
  | nil =>
    let r := B.addZero
    exact ⟨r.val, r.property.1, r.property.2.1, r.property.2.2.1,
      fun x y => by simp [r.property.2.2.2.1], r.property.2.2.2.2⟩
  | cons a ws ih =>
    have ha : a < 2 * k + B.gates.length := hws a (by simp)
    have hrest : ∀ w ∈ ws, w < 2 * k + B.gates.length := fun w hw => hws w (by simp [hw])
    let r1 := ih B hrest
    have ha1 : a < 2 * k + r1.val.1.gates.length := by have := r1.property.1; omega
    let r2 := r1.val.1.addXor a r1.val.2 ha1 r1.property.2.1
    refine ⟨r2.val, le_trans r1.property.1 r2.property.1, r2.property.2.1, ?_, ?_, ?_⟩
    · intro w hw
      have hw1 : w < 2 * k + r1.val.1.gates.length := by have := r1.property.1; omega
      rw [r2.property.2.2.1 w hw1, r1.property.2.2.1 w hw]
    · intro x y
      rw [r2.property.2.2.2.1 x y, r1.property.2.2.1 a ha, r1.property.2.2.2.1 x y]
      simp
    · rw [r2.property.2.2.2.2, r1.property.2.2.2.2]

private lemma sum_fin_eq_list_sum {m : ℕ} (f : Fin m → F) :
    (∑ i : Fin m, f i) = ((List.finRange m).map f).sum := by
  have hnodup : ∀ l : List (Fin m), l.Nodup → (∑ i ∈ l.toFinset, f i) = (l.map f).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      have hnot : a ∉ l.toFinset := by simpa using hnd.1
      simp only [List.toFinset_cons, Finset.sum_insert hnot, List.map_cons, List.sum_cons, ih hnd.2]
  have huniv : (Finset.univ : Finset (Fin m)) = (List.finRange m).toFinset := by
    ext i; simp
  rw [huniv, hnodup (List.finRange m) (List.nodup_finRange m)]

private lemma sum_filter_eq_sum_ite {m : ℕ} (p : Fin m → F) (f : Fin m → F) :
    (((List.finRange m).filter (fun i => decide (p i = 1))).map f).sum =
      ∑ i : Fin m, p i * f i := by
  rw [sum_fin_eq_list_sum]
  suffices h : ∀ l : List (Fin m),
      ((l.filter (fun i => decide (p i = 1))).map f).sum = (l.map (fun i => p i * f i)).sum from
    h (List.finRange m)
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases f_eq_zero_or_one (p a) with hp | hp
    · simp [hp, ih]
    · simp [hp, ih]

private def Builder.addLinComb {k r : ℕ} (B : Builder k)
    (wires : Fin r → ℕ) (hw : ∀ i, wires i < 2 * k + B.gates.length)
    (coeff : Fin r → F) :
    { p : Builder k × ℕ //
      B.gates.length ≤ p.1.gates.length ∧
      p.2 < 2 * k + p.1.gates.length ∧
      (∀ w < 2 * k + B.gates.length, p.1.val w = B.val w) ∧
      (∀ x y, p.1.val p.2 x y = ∑ i : Fin r, coeff i * B.val (wires i) x y) ∧
      costCirc ⟨p.1.gates, 0⟩ = costCirc ⟨B.gates, 0⟩ } := by
  let idxs := (List.finRange r).filter (fun i => decide (coeff i = 1))
  let ws := idxs.map wires
  have hws : ∀ w ∈ ws, w < 2 * k + B.gates.length := by
    intro w hw'
    rw [List.mem_map] at hw'
    rcases hw' with ⟨i, _, rfl⟩
    exact hw i
  let res := B.addSumList ws hws
  refine ⟨res.val, res.property.1, res.property.2.1, res.property.2.2.1, ?_, res.property.2.2.2.2⟩
  intro x y
  rw [res.property.2.2.2.1 x y]
  dsimp only [ws, idxs]
  rw [List.map_map]
  exact sum_filter_eq_sum_ite coeff (fun i => B.val (wires i) x y)

private lemma build_circuit_of_cubics {k r : ℕ}
    (c0 : F) (l : Fin k → F) (Q : Fin k → Fin k → F)
    (α β γ : Fin r → (Fin k → F) →ₗ[F] F) :
    ∃ C : Circuit, legalCirc (2 * k) C ∧ costCirc C ≤ k + r ∧
      ∀ x y : Fin k → F,
        C.eval (bitsVec k x ++ bitsVec k y) =
          decide (dotProduct x y +
            (c0 + ∑ i : Fin k, l i * y i +
             (∑ i : Fin k, ∑ j : Fin k, if i < j then Q i j * y i * y j else 0) +
             ∑ a : Fin r, α a y * β a y * γ a y) = 1) := by
  -- Step 1: Start with init builder (inputs 0..k-1 are x, k..2k-1 are y)
  have hB0_x : ∀ (i : Fin k) (x y : Fin k → F), (Builder.init k).val i.val x y = x i := by
    intro i x y; simp [Builder.init, i.isLt]
  have hB0_y : ∀ (i : Fin k) (x y : Fin k → F), (Builder.init k).val (k + i.val) x y = y i := by
    intro i x y
    have hi := i.isLt
    have h1 : ¬ (k + i.val < k) := by omega
    have h2 : k + i.val - k < k := by omega
    simp only [Builder.init, h1, h2, ↓reduceDIte]
    congr 1; exact Fin.ext (by dsimp only; omega)
  -- Step 2: Build the r product wires t_a = α a y * β a y (cost r)
  have hstep_r : ∀ (s : ℕ) (hs : s ≤ r),
      ∃ (B : Builder k) (tw : Fin s → ℕ),
        (∀ a : Fin s, tw a < 2 * k + B.gates.length) ∧
        (∀ i : Fin k, ∀ x y, B.val i.val x y = x i) ∧
        (∀ i : Fin k, ∀ x y, B.val (k + i.val) x y = y i) ∧
        (∀ a : Fin s, ∀ x y, B.val (tw a) x y = α ⟨a.val, by have := a.isLt; omega⟩ y * β ⟨a.val, by have := a.isLt; omega⟩ y) ∧
        costCirc ⟨B.gates, 0⟩ = s := by
    intro s
    induction s with
    | zero =>
      intro _
      exact ⟨Builder.init k, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
        hB0_x, hB0_y, fun a => Fin.elim0 a, by simp [costCirc, Builder.init]⟩
    | succ s ih =>
      intro hs
      obtain ⟨B, tw, htw_lt, hxB, hyB, htw_val, hcostB⟩ := ih (by omega)
      let yWires : Fin k → ℕ := fun i => k + i.val
      have hy_lt : ∀ i : Fin k, yWires i < 2 * k + B.gates.length := fun i => by
        dsimp only [yWires]; have := i.isLt; omega
      let aIdx : Fin r := ⟨s, by omega⟩
      let rA := B.addLinComb yWires hy_lt (fun i => α aIdx (unitF i))
      let B1 := rA.val.1
      let wA := rA.val.2
      have hlen01 : B.gates.length ≤ B1.gates.length := rA.property.1
      have hwA1 : wA < 2 * k + B1.gates.length := rA.property.2.1
      have hy_lt1 : ∀ i : Fin k, yWires i < 2 * k + B1.gates.length := fun i => by
        have := hy_lt i; omega
      let rB := B1.addLinComb yWires hy_lt1 (fun i => β aIdx (unitF i))
      let B2 := rB.val.1
      let wB := rB.val.2
      have hlen12 : B1.gates.length ≤ B2.gates.length := rB.property.1
      have hwA2 : wA < 2 * k + B2.gates.length := by omega
      let rP := B2.addAnd wA wB hwA2 rB.property.2.1
      let B3 := rP.val.1
      let wP := rP.val.2
      have hlen23 : B2.gates.length ≤ B3.gates.length := rP.property.1
      have hpres : ∀ w < 2 * k + B.gates.length, B3.val w = B.val w := fun w hw => by
        rw [rP.property.2.2.1 w (by omega), rB.property.2.2.1 w (by omega), rA.property.2.2.1 w hw]
      have hlin_eval : ∀ (φ : (Fin k → F) →ₗ[F] F) (y : Fin k → F),
          (∑ i : Fin k, φ (unitF i) * y i) = φ y := by
        intro φ y
        conv_rhs => rw [vec_eq_sum_unit y]
        simp only [map_sum, map_smul, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      let tw' : Fin (s + 1) → ℕ := fun a =>
        if h : a.val < s then tw ⟨a.val, h⟩ else wP
      refine ⟨B3, tw', ?_, ?_, ?_, ?_, ?_⟩
      · intro a; dsimp only [tw']; split_ifs with h
        · have := htw_lt ⟨a.val, h⟩; omega
        · exact rP.property.2.1
      · intro i x y; rw [hpres i.val (by have := i.isLt; omega)]; exact hxB i x y
      · intro i x y; rw [hpres (k + i.val) (by have := i.isLt; omega)]; exact hyB i x y
      · intro a x y; dsimp only [tw']; split_ifs with h
        · rw [hpres _ (htw_lt ⟨a.val, h⟩)]; exact htw_val ⟨a.val, h⟩ x y
        · have ha_eq : (⟨a.val, by have := a.isLt; omega⟩ : Fin r) = aIdx :=
            Fin.ext (by dsimp only [aIdx]; have := a.isLt; omega)
          rw [ha_eq, rP.property.2.2.2.1 x y, rB.property.2.2.1 wA rA.property.2.1,
            rA.property.2.2.2.1 x y, rB.property.2.2.2.1 x y]
          have h1 : (∑ i : Fin k, α aIdx (unitF i) * B.val (yWires i) x y) = α aIdx y := by
            simpa [yWires, hyB] using hlin_eval (α aIdx) y
          have h2 : (∑ i : Fin k, β aIdx (unitF i) * B1.val (yWires i) x y) = β aIdx y := by
            have hB1y : ∀ i : Fin k, B1.val (yWires i) x y = y i := fun i => by
              rw [rA.property.2.2.1 (yWires i) (hy_lt i)]; exact hyB i x y
            simpa [hB1y] using hlin_eval (β aIdx) y
          rw [h1, h2]
      · rw [rP.property.2.2.2.2, rB.property.2.2.2.2, rA.property.2.2.2.2, hcostB]
  obtain ⟨Br, tw, htw_lt, hxBr, hyBr, htw_val, hcostBr⟩ := hstep_r r le_rfl
  -- Step 3: Build k AND gates u_i = X'_i * y_i (cost k)
  have hstep_k : ∀ (s : ℕ) (hs : s ≤ k),
      ∃ (B : Builder k) (uw : Fin s → ℕ),
        Br.gates.length ≤ B.gates.length ∧
        (∀ i : Fin s, uw i < 2 * k + B.gates.length) ∧
        (∀ w < 2 * k + Br.gates.length, B.val w = Br.val w) ∧
        (∀ i : Fin s, ∀ x y, B.val (uw i) x y =
          (x ⟨i.val, by have := i.isLt; omega⟩ +
            (∑ j : Fin k, if (⟨i.val, by have := i.isLt; omega⟩ : Fin k) < j then Q ⟨i.val, by have := i.isLt; omega⟩ j * y j else 0) +
            ∑ a : Fin r, γ a (unitF ⟨i.val, by have := i.isLt; omega⟩) * (α a y * β a y)) * y ⟨i.val, by have := i.isLt; omega⟩) ∧
        costCirc ⟨B.gates, 0⟩ = r + s := by
    intro s
    induction s with
    | zero =>
      intro _
      exact ⟨Br, fun i => Fin.elim0 i, le_rfl, fun i => Fin.elim0 i, fun _ _ => rfl,
        fun i => Fin.elim0 i, by simpa using hcostBr⟩
    | succ s ih =>
      intro hs
      obtain ⟨B, uw, hlenB, huw_lt, hpresB, huw_val, hcostB⟩ := ih (by omega)
      let iIdx : Fin k := ⟨s, by omega⟩
      let rQ := B.addLinComb (fun j : Fin k => k + j.val) (fun j => by have := j.isLt; omega)
        (fun j => if iIdx < j then Q iIdx j else 0)
      let B1 := rQ.val.1
      let wQ := rQ.val.2
      have h1 : B.gates.length ≤ B1.gates.length := rQ.property.1
      have hwQ1 : wQ < 2 * k + B1.gates.length := rQ.property.2.1
      let rG := B1.addLinComb tw (fun a => by have := htw_lt a; omega)
        (fun a => γ a (unitF iIdx))
      let B2 := rG.val.1
      let wG := rG.val.2
      have h2 : B1.gates.length ≤ B2.gates.length := rG.property.1
      have hwG2 : wG < 2 * k + B2.gates.length := rG.property.2.1
      have hx_lt2 : iIdx.val < 2 * k + B2.gates.length := by
        have := iIdx.isLt; omega
      have hwQ2 : wQ < 2 * k + B2.gates.length := by omega
      let rX1 := B2.addXor iIdx.val wQ hx_lt2 hwQ2
      let B3 := rX1.val.1
      let wX1 := rX1.val.2
      have h3 : B2.gates.length ≤ B3.gates.length := rX1.property.1
      have hwG3 : wG < 2 * k + B3.gates.length := by omega
      let rX2 := B3.addXor wX1 wG rX1.property.2.1 hwG3
      let B4 := rX2.val.1
      let wX2 := rX2.val.2
      have h4 : B3.gates.length ≤ B4.gates.length := rX2.property.1
      have hy_lt4 : k + iIdx.val < 2 * k + B4.gates.length := by
        have := iIdx.isLt; omega
      let rU := B4.addAnd wX2 (k + iIdx.val) rX2.property.2.1 hy_lt4
      let B5 := rU.val.1
      let wU := rU.val.2
      have h5 : B4.gates.length ≤ B5.gates.length := rU.property.1
      have hlen05 : B.gates.length ≤ B5.gates.length := by omega
      have hpres5 : ∀ w < 2 * k + B.gates.length, B5.val w = B.val w := fun w hw => by
        rw [rU.property.2.2.1 w (by omega), rX2.property.2.2.1 w (by omega),
          rX1.property.2.2.1 w (by omega), rG.property.2.2.1 w (by omega),
          rQ.property.2.2.1 w hw]
      let uw' : Fin (s + 1) → ℕ := fun i =>
        if h : i.val < s then uw ⟨i.val, h⟩ else wU
      refine ⟨B5, uw', le_trans hlenB hlen05, ?_, ?_, ?_, ?_⟩
      · intro i; dsimp only [uw']; split_ifs with h
        · have := huw_lt ⟨i.val, h⟩; omega
        · exact rU.property.2.1
      · intro w hw; rw [hpres5 w (by omega), hpresB w hw]
      · intro i x y; dsimp only [uw']; split_ifs with h
        · rw [hpres5 _ (huw_lt ⟨i.val, h⟩)]; exact huw_val ⟨i.val, h⟩ x y
        · have hi_eq : (⟨i.val, by have := i.isLt; omega⟩ : Fin k) = iIdx :=
            Fin.ext (by dsimp only [iIdx]; have := i.isLt; omega)
          rw [hi_eq, rU.property.2.2.2.1 x y]
          have hiLt := iIdx.isLt
          have hval_y : B4.val (k + iIdx.val) x y = y iIdx := by
            rw [rX2.property.2.2.1 _ (by omega), rX1.property.2.2.1 _ (by omega),
              rG.property.2.2.1 _ (by omega), rQ.property.2.2.1 _ (by omega),
              hpresB _ (by omega)]
            exact hyBr iIdx x y
          have hval_x : B2.val iIdx.val x y = x iIdx := by
            rw [rG.property.2.2.1 _ (by omega), rQ.property.2.2.1 _ (by omega),
              hpresB _ (by omega)]
            exact hxBr iIdx x y
          have hval_Q : B2.val wQ x y =
              ∑ j : Fin k, if iIdx < j then Q iIdx j * y j else 0 := by
            rw [rG.property.2.2.1 wQ rQ.property.2.1, rQ.property.2.2.2.1 x y]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hpresB (k + j.val) (by have := j.isLt; omega), hyBr j x y]
            split_ifs <;> simp
          have hval_G : B3.val wG x y =
              ∑ a : Fin r, γ a (unitF iIdx) * (α a y * β a y) := by
            rw [rX1.property.2.2.1 wG rG.property.2.1, rG.property.2.2.2.1 x y]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [rQ.property.2.2.1 (tw a) (by have := htw_lt a; omega),
              hpresB (tw a) (htw_lt a), htw_val a x y]
          rw [hval_y, rX2.property.2.2.2.1 x y, rX1.property.2.2.2.1 x y,
            hval_x, hval_Q, hval_G]
      · rw [rU.property.2.2.2.2, rX2.property.2.2.2.2, rX1.property.2.2.2.2,
          rG.property.2.2.2.2, rQ.property.2.2.2.2, hcostB]; omega
  obtain ⟨Bk, uw, hlenBk, huw_lt, hpresBk, huw_val, hcostBk⟩ := hstep_k k le_rfl
  -- Step 4: Sum l_i * y_i and u_i, plus optional c0 (cost 0)
  let rL := Bk.addLinComb (fun i : Fin k => k + i.val) (fun i => by have := i.isLt; omega) l
  let B1 := rL.val.1
  let wL := rL.val.2
  have hlenL : Bk.gates.length ≤ B1.gates.length := rL.property.1
  have hwL1 : wL < 2 * k + B1.gates.length := rL.property.2.1
  let rUsum := B1.addLinComb uw (fun i => by have := huw_lt i; omega)
    (fun _ => 1)
  let B2 := rUsum.val.1
  let wUsum := rUsum.val.2
  have hlenU : B1.gates.length ≤ B2.gates.length := rUsum.property.1
  have hwL2 : wL < 2 * k + B2.gates.length := by omega
  let rTot := B2.addXor wL wUsum hwL2 rUsum.property.2.1
  let B3 := rTot.val.1
  let wTot := rTot.val.2
  -- Add c0 (if c0 = 1, addNot; if c0 = 0, keep wTot)
  have hsum_combine_U : ∀ x y, (∑ i : Fin k, 1 * B1.val (uw i) x y) =
      dotProduct x y +
      (∑ i : Fin k, ∑ j : Fin k, if i < j then Q i j * y i * y j else 0) +
      ∑ a : Fin r, α a y * β a y * γ a y := by
    intro x y
    have hstep1 : (∑ i : Fin k, 1 * B1.val (uw i) x y) =
        ∑ i : Fin k, (x i * y i +
          (∑ j : Fin k, if i < j then Q i j * y i * y j else 0) +
          ∑ a : Fin r, γ a (unitF i) * (α a y * β a y) * y i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_mul, rL.property.2.2.1 (uw i) (huw_lt i), huw_val i x y]
      simp only [add_mul, Finset.sum_mul]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hstep1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hγ : (∑ i : Fin k, γ a (unitF i) * (α a y * β a y) * y i) =
        α a y * β a y * (∑ i : Fin k, y i * γ a (unitF i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hγ]
    congr 1
    conv_rhs => rw [vec_eq_sum_unit y]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hsum_combine_L : ∀ x y, (∑ i : Fin k, l i * Bk.val (k + i.val) x y) = ∑ i : Fin k, l i * y i :=
    fun x y => Finset.sum_congr rfl fun i _ => by
      rw [hpresBk _ (by have := i.isLt; omega), hyBr i x y]
  have hcostB3 : costCirc ⟨B3.gates, 0⟩ = r + k := by
    rw [rTot.property.2.2.2.2, rUsum.property.2.2.2.2, rL.property.2.2.2.2, hcostBk]
  rcases f_eq_zero_or_one c0 with rfl | rfl
  · refine ⟨⟨B3.gates, wTot⟩, ⟨B3.hreads, B3.hlegal⟩, by change costCirc ⟨B3.gates, 0⟩ ≤ k + r; omega,
      fun x y => ?_⟩
    change ((Circuit.mk B3.gates 0).wires (bitsVec k x ++ bitsVec k y)).getD wTot false = _
    rw [B3.hval x y wTot rTot.property.2.1, rTot.property.2.2.2.1 x y,
      rUsum.property.2.2.1 wL rL.property.2.1, rL.property.2.2.2.1 x y,
      rUsum.property.2.2.2.1 x y]
    apply congrArg (fun v : F => decide (v = 1))
    rw [hsum_combine_L x y, hsum_combine_U x y, zero_add]; ring
  · let rFin := B3.addNot wTot rTot.property.2.1
    let B4 := rFin.val.1
    let wFin := rFin.val.2
    have hcostB4 : costCirc ⟨B4.gates, 0⟩ = r + k := by
      rw [rFin.property.2.2.2.2, hcostB3]
    refine ⟨⟨B4.gates, wFin⟩, ⟨B4.hreads, B4.hlegal⟩, by change costCirc ⟨B4.gates, 0⟩ ≤ k + r; omega,
      fun x y => ?_⟩
    change ((Circuit.mk B4.gates 0).wires (bitsVec k x ++ bitsVec k y)).getD wFin false = _
    rw [B4.hval x y wFin rFin.property.2.1, rFin.property.2.2.2.1 x y,
      rTot.property.2.2.2.1 x y, rUsum.property.2.2.1 wL rL.property.2.1,
      rL.property.2.2.2.1 x y, rUsum.property.2.2.2.1 x y]
    apply congrArg (fun v : F => decide (v = 1))
    rw [hsum_combine_L x y, hsum_combine_U x y]; ring

/-! ## Section 4: Circuit → SLP (`circuit_to_slp`) and `x`-elimination (`slp_elim_x`) -/

private def ofBool (b : Bool) : F := if b then 1 else 0

private lemma ofBool_decide_eq_one (a : F) : ofBool (decide (a = 1)) = a := by
  revert a; decide

private lemma ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide

private lemma ofBool_or (a b : Bool) :
    ofBool (a || b) = (ofBool a + 1) * (ofBool b + 1) + 1 := by
  cases a <;> cases b <;> decide

private lemma ofBool_not (a : Bool) : ofBool (!a) = ofBool a + 1 := by
  cases a <;> decide

private lemma ofBool_mod2_two (a b : Bool) :
    ofBool (decide ([a, b].count true % 2 = 0)) = ofBool a + ofBool b + 1 := by
  cases a <;> cases b <;> decide

private lemma ofBool_mod2_one (a : Bool) :
    ofBool (decide ([a].count true % 2 = 0)) = ofBool a + 1 := by
  cases a <;> decide

private structure SLP (k s : ℕ) where
  ax : Fin s → (Fin k → F)
  ay : Fin s → (Fin k → F)
  ac : Fin s → F
  ap : Fin s → Fin s → F
  bx : Fin s → (Fin k → F)
  by_ : Fin s → (Fin k → F)
  bc : Fin s → F
  bp : Fin s → Fin s → F
  p : Fin s → (Fin k → F) → (Fin k → F) → F
  hp : ∀ t x y, p t x y =
    (dotProduct (ax t) x + dotProduct (ay t) y + ac t +
      ∑ j : Fin s, if j.val < t.val then ap t j * p j x y else 0) *
    (dotProduct (bx t) x + dotProduct (by_ t) y + bc t +
      ∑ j : Fin s, if j.val < t.val then bp t j * p j x y else 0)

private def isAffRep {k s : ℕ} (S : SLP k s) (f : (Fin k → F) → (Fin k → F) → F) : Prop :=
  ∃ (cx cy : Fin k → F) (cc : F) (cp : Fin s → F),
    ∀ x y, f x y = dotProduct cx x + dotProduct cy y + cc + ∑ j : Fin s, cp j * S.p j x y

private lemma isAffRep_const {k s : ℕ} (S : SLP k s) (c : F) :
    isAffRep S (fun _ _ => c) :=
  ⟨0, 0, c, 0, fun _ _ => by simp⟩

private lemma isAffRep_add {k s : ℕ} (S : SLP k s) {f g : (Fin k → F) → (Fin k → F) → F}
    (hf : isAffRep S f) (hg : isAffRep S g) : isAffRep S (fun x y => f x y + g x y) := by
  rcases hf with ⟨cx1, cy1, cc1, cp1, hf⟩
  rcases hg with ⟨cx2, cy2, cc2, cp2, hg⟩
  refine ⟨cx1 + cx2, cy1 + cy2, cc1 + cc2, fun j => cp1 j + cp2 j, fun x y => ?_⟩
  dsimp only
  rw [hf x y, hg x y, add_dotProduct, add_dotProduct]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

private lemma isAffRep_add_one {k s : ℕ} (S : SLP k s) {f : (Fin k → F) → (Fin k → F) → F}
    (hf : isAffRep S f) : isAffRep S (fun x y => f x y + 1) :=
  isAffRep_add S hf (isAffRep_const S 1)

private lemma circuit_to_slp {k : ℕ} (gs : List Gate)
    (hleg : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))) :
    ∃ (S : SLP k (costCirc ⟨gs, 0⟩)),
      ∀ w : ℕ, isAffRep S (fun x y =>
        ofBool (((Circuit.mk gs 0).wires (bitsVec k x ++ bitsVec k y)).getD w false)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    change ∃ (S : SLP k 0), _
    let S0 : SLP k 0 :=
      { ax := Fin.elim0, ay := Fin.elim0, ac := Fin.elim0, ap := fun t => Fin.elim0 t,
        bx := Fin.elim0, by_ := Fin.elim0, bc := Fin.elim0, bp := fun t => Fin.elim0 t,
        p := Fin.elim0, hp := fun t => Fin.elim0 t }
    refine ⟨S0, fun w => ?_⟩
    by_cases h1 : w < k
    · refine ⟨unitF ⟨w, h1⟩, 0, 0, Fin.elim0, fun x y => ?_⟩
      have hdot : dotProduct (unitF ⟨w, h1⟩) x = x ⟨w, h1⟩ := by
        unfold dotProduct
        rw [Finset.sum_eq_single ⟨w, h1⟩]
        · simp [unitF]
        · intro j _ hne; simp [unitF, Ne.symm hne]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      simp only [Circuit.wires, List.foldl_nil, zero_dotProduct, add_zero, hdot]
      change ofBool ((bitsVec k x ++ bitsVec k y).getD w false) = x ⟨w, h1⟩ + ∑ j : Fin 0, Fin.elim0 j * S0.p j x y
      rw [Fin.sum_univ_zero, add_zero, getD_append_left _ _ _ (by rw [bitsVec_length]; exact h1)]
      simp [bitsVec, List.getD_eq_getElem?_getD, h1, ofBool_decide_eq_one]
    · by_cases h2 : w - k < k
      · refine ⟨0, unitF ⟨w - k, h2⟩, 0, Fin.elim0, fun x y => ?_⟩
        have hdot : dotProduct (unitF ⟨w - k, h2⟩) y = y ⟨w - k, h2⟩ := by
          unfold dotProduct
          rw [Finset.sum_eq_single ⟨w - k, h2⟩]
          · simp [unitF]
          · intro j _ hne; simp [unitF, Ne.symm hne]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        simp only [Circuit.wires, List.foldl_nil, zero_dotProduct, zero_add, add_zero, hdot]
        change ofBool ((bitsVec k x ++ bitsVec k y).getD w false) = y ⟨w - k, h2⟩ + ∑ j : Fin 0, Fin.elim0 j * S0.p j x y
        rw [Fin.sum_univ_zero, add_zero]
        have hlen : (bitsVec k x).length = k := bitsVec_length k x
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : (bitsVec k x).length ≤ w), hlen]
        simp [bitsVec, h2, ofBool_decide_eq_one]
      · refine ⟨0, 0, 0, Fin.elim0, fun x y => ?_⟩
        simp only [Circuit.wires, List.foldl_nil, zero_dotProduct, add_zero, Fin.sum_univ_zero]
        have hge : (bitsVec k x ++ bitsVec k y).length ≤ w := by
          rw [List.length_append, bitsVec_length, bitsVec_length]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
        rfl
  | append_singleton gs g ih =>
    have hleg_gs : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)) :=
      fun h hh => hleg h (List.mem_append_left [g] hh)
    have hleg_g := hleg g (List.mem_append_right gs (List.mem_singleton_self g))
    obtain ⟨S, hS⟩ := ih hleg_gs
    let wireVal : ℕ → (Fin k → F) → (Fin k → F) → F := fun w x y =>
      ofBool (((Circuit.mk gs 0).wires (bitsVec k x ++ bitsVec k y)).getD w false)
    let newVal : (Fin k → F) → (Fin k → F) → F := fun x y =>
      ofBool (g.op.eval (g.inputs.map fun i =>
        ((Circuit.mk gs 0).wires (bitsVec k x ++ bitsVec k y)).getD i false))
    have hlen_w : ∀ x y, ((Circuit.mk gs 0).wires (bitsVec k x ++ bitsVec k y)).length =
        2 * k + gs.length := fun x y => by
      have h1 := wires_length ⟨gs, 0⟩ (bitsVec k x ++ bitsVec k y)
      rw [List.length_append, bitsVec_length, bitsVec_length] at h1
      dsimp only at h1; omega
    have hwire_step : ∀ (w : ℕ) (x y : Fin k → F),
        ofBool (((Circuit.mk (gs ++ [g]) 0).wires (bitsVec k x ++ bitsVec k y)).getD w false) =
        if w < 2 * k + gs.length then wireVal w x y
        else if w = 2 * k + gs.length then newVal x y
        else 0 := by
      intro w x y
      rw [wires_append_gate]
      by_cases hlt : w < 2 * k + gs.length
      · simp only [hlt, ↓reduceIte, wireVal]
        rw [getD_append_left _ _ _ (by rw [hlen_w]; exact hlt)]
      · by_cases heq : w = 2 * k + gs.length
        · subst heq
          simp only [lt_irrefl, ↓reduceIte, newVal]
          rw [← hlen_w x y, getD_append_singleton_last]
        · simp only [hlt, heq, ↓reduceIte]
          have hge : (((Circuit.mk gs 0).wires (bitsVec k x ++ bitsVec k y)) ++
              [g.op.eval (g.inputs.map fun i =>
                ((Circuit.mk gs 0).wires (bitsVec k x ++ bitsVec k y)).getD i false)]).length ≤ w := by
            rw [List.length_append, List.length_singleton, hlen_w]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
          rfl
    by_cases hcost : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2
    · -- Cost gate: cost increases by 1
      have hcost_eq : costCirc ⟨gs ++ [g], 0⟩ = costCirc ⟨gs, 0⟩ + 1 := by
        simp [costCirc, List.countP_append, hcost]
      let s := costCirc ⟨gs, 0⟩
      rcases List.length_eq_two.mp hcost.2 with ⟨i, j, hij⟩
      have hAi : isAffRep S (wireVal i) := hS i
      have hBj : isAffRep S (wireVal j) := hS j
      -- Choose (A, B, outShift) depending on .and vs .or
      have hAB : ∃ (A B : (Fin k → F) → (Fin k → F) → F) (sh : F),
          isAffRep S A ∧ isAffRep S B ∧ ∀ x y, newVal x y = A x y * B x y + sh := by
        rcases hcost.1 with hop | hop
        · refine ⟨wireVal i, wireVal j, 0, hAi, hBj, fun x y => ?_⟩
          simp [newVal, hop, hij, GateOp.eval, ofBool_and, wireVal]
        · refine ⟨fun x y => wireVal i x y + 1, fun x y => wireVal j x y + 1, 1,
            isAffRep_add_one S hAi, isAffRep_add_one S hBj, fun x y => ?_⟩
          simp [newVal, hop, hij, GateOp.eval, ofBool_or, wireVal]
      rcases hAB with ⟨A, B, sh, ⟨ax0, ay0, ac0, ap0, hA⟩, ⟨bx0, by0, bc0, bp0, hB⟩, hnew⟩
      -- Extend S from s to s + 1
      let S' : SLP k (s + 1) :=
        { ax := fun t => if h : t.val < s then S.ax ⟨t.val, h⟩ else ax0
          ay := fun t => if h : t.val < s then S.ay ⟨t.val, h⟩ else ay0
          ac := fun t => if h : t.val < s then S.ac ⟨t.val, h⟩ else ac0
          ap := fun t r =>
            if ht : t.val < s then
              if hr : r.val < s then S.ap ⟨t.val, ht⟩ ⟨r.val, hr⟩ else 0
            else if hr : r.val < s then ap0 ⟨r.val, hr⟩ else 0
          bx := fun t => if h : t.val < s then S.bx ⟨t.val, h⟩ else bx0
          by_ := fun t => if h : t.val < s then S.by_ ⟨t.val, h⟩ else by0
          bc := fun t => if h : t.val < s then S.bc ⟨t.val, h⟩ else bc0
          bp := fun t r =>
            if ht : t.val < s then
              if hr : r.val < s then S.bp ⟨t.val, ht⟩ ⟨r.val, hr⟩ else 0
            else if hr : r.val < s then bp0 ⟨r.val, hr⟩ else 0
          p := fun t x y => if h : t.val < s then S.p ⟨t.val, h⟩ x y else A x y * B x y
          hp := fun t x y => by
            by_cases ht : t.val < s
            · simp only [ht, ↓reduceDIte]
              rw [S.hp ⟨t.val, ht⟩ x y]
              congr 1
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last s).val < t.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun r _ => ?_
                have hr : (Fin.castSucc r).val < s := r.isLt
                simp only [hr, ↓reduceDIte]
                rfl
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last s).val < t.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun r _ => ?_
                have hr : (Fin.castSucc r).val < s := r.isLt
                simp only [hr, ↓reduceDIte]
                rfl
            · have ht_eq : t.val = s := by omega
              simp only [ht, ↓reduceDIte]
              rw [hA x y, hB x y]
              congr 1
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last s).val < t.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun r _ => ?_
                have hr : (Fin.castSucc r).val < s := r.isLt
                have hrt : (Fin.castSucc r).val < t.val := by rw [ht_eq]; exact r.isLt
                simp only [hr, hrt, ↓reduceDIte, ↓reduceIte]
                rfl
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last s).val < t.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun r _ => ?_
                have hr : (Fin.castSucc r).val < s := r.isLt
                have hrt : (Fin.castSucc r).val < t.val := by rw [ht_eq]; exact r.isLt
                simp only [hr, hrt, ↓reduceDIte, ↓reduceIte]
                rfl }
      have hlift : ∀ {f : (Fin k → F) → (Fin k → F) → F}, isAffRep S f → isAffRep S' f := by
        intro f ⟨cx, cy, cc, cp, hf⟩
        refine ⟨cx, cy, cc, fun t => if h : t.val < s then cp ⟨t.val, h⟩ else 0, fun x y => ?_⟩
        rw [hf x y]
        congr 1
        rw [Fin.sum_univ_castSucc]
        have hlast : ¬ ((Fin.last s).val < s) := by simp
        simp only [hlast, ↓reduceDIte, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun r _ => ?_
        have hr : (Fin.castSucc r).val < s := r.isLt
        simp only [S', hr, ↓reduceDIte]
        rfl
      rw [hcost_eq]
      refine ⟨S', fun w => ?_⟩
      have hfn : (fun x y => ofBool (((Circuit.mk (gs ++ [g]) 0).wires
            (bitsVec k x ++ bitsVec k y)).getD w false)) =
          if w < 2 * k + gs.length then wireVal w
          else if w = 2 * k + gs.length then newVal else fun _ _ => 0 := by
        funext x y
        rw [hwire_step w x y]
        by_cases h1 : w < 2 * k + gs.length
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : w = 2 * k + gs.length
          · subst h2; simp only [lt_irrefl, ↓reduceIte]
          · simp only [h1, h2, ↓reduceIte]
      rw [hfn]
      split_ifs with h1 h2
      · exact hlift (hS w)
      · refine ⟨0, 0, sh, fun t => if t = Fin.last s then 1 else 0, fun x y => ?_⟩
        rw [hnew x y]
        simp only [zero_dotProduct, zero_add]
        rw [Finset.sum_eq_single (Fin.last s)]
        · simp [S', add_comm]
        · intro t _ hne; simp [hne]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · exact isAffRep_const S' 0
    · -- Non-cost gate: cost unchanged!
      have hcost_eq : costCirc ⟨gs ++ [g], 0⟩ = costCirc ⟨gs, 0⟩ := by
        simp [costCirc, List.countP_append, hcost]
      rw [hcost_eq]
      have hnew_aff : isAffRep S newVal := by
        rcases hleg_g with ⟨hlen_g, hop⟩
        rcases hop with hop | hop | hop | ⟨hop, hlen1⟩
        · -- .and with length ≤ 1
          have hlt2 : g.inputs.length < 2 := by
            by_contra hge; exact hcost ⟨Or.inl hop, by omega⟩
          cases hgin : g.inputs with
          | nil =>
            have : newVal = fun _ _ => 1 := by
              funext x y; simp [newVal, hop, hgin, GateOp.eval, ofBool]
            rw [this]; exact isAffRep_const S 1
          | cons i tl =>
            cases tl with
            | nil =>
              have : newVal = wireVal i := by
                funext x y; simp [newVal, wireVal, hop, hgin, GateOp.eval]
              rw [this]; exact hS i
            | cons _ _ => simp [hgin] at hlt2
        · -- .or with length ≤ 1
          have hlt2 : g.inputs.length < 2 := by
            by_contra hge; exact hcost ⟨Or.inr hop, by omega⟩
          cases hgin : g.inputs with
          | nil =>
            have : newVal = fun _ _ => 0 := by
              funext x y; simp [newVal, hop, hgin, GateOp.eval, ofBool]
            rw [this]; exact isAffRep_const S 0
          | cons i tl =>
            cases tl with
            | nil =>
              have : newVal = wireVal i := by
                funext x y; simp [newVal, wireVal, hop, hgin, GateOp.eval]
              rw [this]; exact hS i
            | cons _ _ => simp [hgin] at hlt2
        · -- .mod 2 with length ≤ 2
          cases hgin : g.inputs with
          | nil =>
            have : newVal = fun _ _ => 1 := by
              funext x y; simp [newVal, hop, hgin, GateOp.eval, ofBool]
            rw [this]; exact isAffRep_const S 1
          | cons i tl =>
            cases tl with
            | nil =>
              have : newVal = fun x y => wireVal i x y + 1 := by
                funext x y; simp [newVal, wireVal, hop, hgin, GateOp.eval, ofBool_mod2_one]
              rw [this]; exact isAffRep_add_one S (hS i)
            | cons j tl2 =>
              cases tl2 with
              | nil =>
                have : newVal = fun x y => wireVal i x y + wireVal j x y + 1 := by
                  funext x y; simp [newVal, wireVal, hop, hgin, GateOp.eval, ofBool_mod2_two]
                rw [this]; exact isAffRep_add_one S (isAffRep_add S (hS i) (hS j))
              | cons _ _ => simp [hgin] at hlen_g
        · -- .not with length = 1
          rcases List.length_eq_one_iff.mp hlen1 with ⟨i, hgin⟩
          have : newVal = fun x y => wireVal i x y + 1 := by
            funext x y; simp [newVal, wireVal, hop, hgin, GateOp.eval, ofBool_not]
          rw [this]; exact isAffRep_add_one S (hS i)
      refine ⟨S, fun w => ?_⟩
      have hfn : (fun x y => ofBool (((Circuit.mk (gs ++ [g]) 0).wires
            (bitsVec k x ++ bitsVec k y)).getD w false)) =
          if w < 2 * k + gs.length then wireVal w
          else if w = 2 * k + gs.length then newVal else fun _ _ => 0 := by
        funext x y
        rw [hwire_step w x y]
        by_cases h1 : w < 2 * k + gs.length
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : w = 2 * k + gs.length
          · subst h2; simp only [lt_irrefl, ↓reduceIte]
          · simp only [h1, h2, ↓reduceIte]
      rw [hfn]
      split_ifs with h1 h2
      · exact hS w
      · exact hnew_aff
      · exact isAffRep_const S 0

private structure YSLP (k r : ℕ) where
  ℓ : Fin r → (Fin k → F) →ₗ[F] F
  lc : Fin r → F
  α : Fin r → (Fin k → F) →ₗ[F] F
  ac : Fin r → F
  ap : Fin r → Fin r → F
  β : Fin r → (Fin k → F) →ₗ[F] F
  bc : Fin r → F
  bp : Fin r → Fin r → F
  q : Fin r → (Fin k → F) → F
  hq : ∀ a y, q a y =
    (α a y + ac a + ∑ b : Fin r, if b.val < a.val then ap a b * q b y else 0) *
    (β a y + bc a + ∑ b : Fin r, if b.val < a.val then bp a b * q b y else 0)

private def dotLin {k : ℕ} (v : Fin k → F) : (Fin k → F) →ₗ[F] F where
  toFun y := dotProduct v y
  map_add' y1 y2 := dotProduct_add v y1 y2
  map_smul' s y := by simp [dotProduct_smul]

private lemma slp_elim_x {k s : ℕ} (S : SLP k s)
    (target : (Fin k → F) → F)
    (htarget : isAffRep S (fun x y => dotProduct x y + target y)) :
    ∃ (r : ℕ) (_ : k + r ≤ s) (Y : YSLP k r) (Q : (Fin k → F) → F),
      isQuad Q ∧ ∀ y : Fin k → F, target y = Q y + ∑ a : Fin r, (Y.ℓ a y + Y.lc a) * Y.q a y := by
  -- Inductively eliminate x-dependent gates over t = 0 .. s
  have hstep : ∀ (t : ℕ) (_ht : t ≤ s),
      ∃ (U : Submodule F (Fin k → F)) (r : ℕ) (idx : Fin r ↪ Fin t)
        (M : (Fin k → F) →ₗ[F] (Fin k → F)) (v0 : Fin k → F) (w : Fin r → (Fin k → F))
        (α β : Fin r → (Fin k → F) →ₗ[F] F) (ac bc : Fin r → F) (ap bp : Fin r → Fin r → F)
        (q : Fin r → (Fin k → F) → F),
        (∀ a b : Fin r, a < b → idx a < idx b) ∧
        Module.finrank F U + t = k + r ∧
        (∀ a y, q a y =
          (α a y + ac a + ∑ b : Fin r, if b.val < a.val then ap a b * q b y else 0) *
          (β a y + bc a + ∑ b : Fin r, if b.val < a.val then bp a b * q b y else 0)) ∧
        (∀ (j : Fin t) (y z : Fin k → F), z ∈ U →
          let x0 := M y + v0 + ∑ a : Fin r, q a y • w a
          S.p ⟨j.val, by have := j.isLt; omega⟩ (x0 + z) y =
            if h : ∃ a : Fin r, idx a = j then q h.choose y else 0) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨⊤, 0, ⟨Fin.elim0, fun a => Fin.elim0 a⟩, 0, 0, Fin.elim0,
        Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
        Fin.elim0, fun a => Fin.elim0 a, ?_, fun a => Fin.elim0 a, fun j => Fin.elim0 j⟩
      rw [finrank_top, Module.finrank_fin_fun]
    | succ t ih =>
      intro ht
      obtain ⟨U, r, idx, M, v0, w, α, β, ac, bc, ap, bp, q, hmono, hdim, hq, hinv⟩ := ih (by omega)
      let tFin : Fin s := ⟨t, by omega⟩
      let x0 : (Fin k → F) → (Fin k → F) := fun y => M y + v0 + ∑ a : Fin r, q a y • w a
      -- Compute linear/affine decompositions of A(tFin) and B(tFin) on (x0 y + z, y)
      let α_z : (Fin k → F) →ₗ[F] F := dotLin (S.ax tFin)
      let β_z : (Fin k → F) →ₗ[F] F := dotLin (S.bx tFin)
      let a_y_lin : (Fin k → F) →ₗ[F] F := (dotLin (S.ax tFin)).comp M + dotLin (S.ay tFin)
      let a_c : F := dotProduct (S.ax tFin) v0 + S.ac tFin
      let a_p : Fin r → F := fun a =>
        dotProduct (S.ax tFin) (w a) + S.ap tFin ⟨(idx a).val, by have := (idx a).isLt; omega⟩
      let b_y_lin : (Fin k → F) →ₗ[F] F := (dotLin (S.bx tFin)).comp M + dotLin (S.by_ tFin)
      let b_c : F := dotProduct (S.bx tFin) v0 + S.bc tFin
      let b_p : Fin r → F := fun a =>
        dotProduct (S.bx tFin) (w a) + S.bp tFin ⟨(idx a).val, by have := (idx a).isLt; omega⟩
      have hA_eval : ∀ y z, z ∈ U →
          (dotProduct (S.ax tFin) (x0 y + z) + dotProduct (S.ay tFin) y + S.ac tFin +
            ∑ j : Fin s, if j.val < tFin.val then S.ap tFin j * S.p j (x0 y + z) y else 0) =
          α_z z + (a_y_lin y + a_c + ∑ a : Fin r, a_p a * q a y) := by
        intro y z hz
        have hsum_s : (∑ j : Fin s, if j.val < tFin.val then S.ap tFin j * S.p j (x0 y + z) y else 0) =
            ∑ a : Fin r, S.ap tFin ⟨(idx a).val, by omega⟩ * q a y := by
          have hfilt : (∑ j : Fin s, if j.val < tFin.val then S.ap tFin j * S.p j (x0 y + z) y else 0) =
              ∑ j : Fin t, S.ap tFin ⟨j.val, by omega⟩ * S.p ⟨j.val, by omega⟩ (x0 y + z) y := by
            have h1 : (∑ j : Fin s, if j.val < tFin.val then S.ap tFin j * S.p j (x0 y + z) y else 0) =
                ∑ j ∈ Finset.univ.filter (fun j : Fin s => j.val < t),
                  S.ap tFin j * S.p j (x0 y + z) y := by
              rw [Finset.sum_filter]
            rw [h1]
            refine Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin t)) ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
            · intro j _; exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
            · intro _ _; rfl
          rw [hfilt]
          have h2 : (∑ j : Fin t, S.ap tFin ⟨j.val, by omega⟩ * S.p ⟨j.val, by omega⟩ (x0 y + z) y) =
              ∑ j ∈ Finset.univ.image idx, S.ap tFin ⟨j.val, by omega⟩ * S.p ⟨j.val, by omega⟩ (x0 y + z) y := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) fun j _ hnot => ?_
            have hnex : ¬ ∃ a : Fin r, idx a = j := by
              intro ⟨a, ha⟩; exact hnot (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
            rw [hinv j y z hz]
            simp [hnex]
          rw [h2, Finset.sum_image (fun a _ b _ h => idx.injective h)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hinv (idx a) y z hz]
          have hex : ∃ a' : Fin r, idx a' = idx a := ⟨a, rfl⟩
          simp only [hex, ↓reduceDIte]
          have hch : hex.choose = a := idx.injective hex.choose_spec
          rw [hch]
        rw [hsum_s]
        dsimp only [x0, α_z, a_y_lin, a_c, a_p, dotLin]
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul, add_mul,
          Finset.sum_add_distrib]
        have hcomm : (∑ a : Fin r, q a y * dotProduct (S.ax tFin) (w a)) =
            ∑ a : Fin r, dotProduct (S.ax tFin) (w a) * q a y :=
          Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [hcomm]; ring
      have hB_eval : ∀ y z, z ∈ U →
          (dotProduct (S.bx tFin) (x0 y + z) + dotProduct (S.by_ tFin) y + S.bc tFin +
            ∑ j : Fin s, if j.val < tFin.val then S.bp tFin j * S.p j (x0 y + z) y else 0) =
          β_z z + (b_y_lin y + b_c + ∑ a : Fin r, b_p a * q a y) := by
        intro y z hz
        have hsum_s : (∑ j : Fin s, if j.val < tFin.val then S.bp tFin j * S.p j (x0 y + z) y else 0) =
            ∑ a : Fin r, S.bp tFin ⟨(idx a).val, by omega⟩ * q a y := by
          have hfilt : (∑ j : Fin s, if j.val < tFin.val then S.bp tFin j * S.p j (x0 y + z) y else 0) =
              ∑ j : Fin t, S.bp tFin ⟨j.val, by omega⟩ * S.p ⟨j.val, by omega⟩ (x0 y + z) y := by
            have h1 : (∑ j : Fin s, if j.val < tFin.val then S.bp tFin j * S.p j (x0 y + z) y else 0) =
                ∑ j ∈ Finset.univ.filter (fun j : Fin s => j.val < t),
                  S.bp tFin j * S.p j (x0 y + z) y := by
              rw [Finset.sum_filter]
            rw [h1]
            refine Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin t)) ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
            · intro j _; exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
            · intro _ _; rfl
          rw [hfilt]
          have h2 : (∑ j : Fin t, S.bp tFin ⟨j.val, by omega⟩ * S.p ⟨j.val, by omega⟩ (x0 y + z) y) =
              ∑ j ∈ Finset.univ.image idx, S.bp tFin ⟨j.val, by omega⟩ * S.p ⟨j.val, by omega⟩ (x0 y + z) y := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) fun j _ hnot => ?_
            have hnex : ¬ ∃ a : Fin r, idx a = j := by
              intro ⟨a, ha⟩; exact hnot (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
            rw [hinv j y z hz]
            simp [hnex]
          rw [h2, Finset.sum_image (fun a _ b _ h => idx.injective h)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hinv (idx a) y z hz]
          have hex : ∃ a' : Fin r, idx a' = idx a := ⟨a, rfl⟩
          simp only [hex, ↓reduceDIte]
          have hch : hex.choose = a := idx.injective hex.choose_spec
          rw [hch]
        rw [hsum_s]
        dsimp only [x0, β_z, b_y_lin, b_c, b_p, dotLin]
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul, add_mul,
          Finset.sum_add_distrib]
        have hcomm : (∑ a : Fin r, q a y * dotProduct (S.bx tFin) (w a)) =
            ∑ a : Fin r, dotProduct (S.bx tFin) (w a) * q a y :=
          Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [hcomm]; ring
      -- Helper to kill gate tFin given linear functional φ_z with u ∈ U, φ_z u = 1, and y-part (y_lin, c_y, p_y)
      have hkill : ∀ (φ_z : (Fin k → F) →ₗ[F] F) (y_lin : (Fin k → F) →ₗ[F] F)
          (c_y : F) (p_y : Fin r → F) (u : Fin k → F),
          u ∈ U → φ_z u = 1 →
          (∀ y z, z ∈ U → φ_z z + (y_lin y + c_y + ∑ a : Fin r, p_y a * q a y) = 0 →
            S.p tFin (x0 y + z) y = 0) →
          ∃ (U' : Submodule F (Fin k → F)) (r' : ℕ) (idx' : Fin r' ↪ Fin (t + 1))
            (M' : (Fin k → F) →ₗ[F] (Fin k → F)) (v0' : Fin k → F) (w' : Fin r' → (Fin k → F))
            (α' β' : Fin r' → (Fin k → F) →ₗ[F] F) (ac' bc' : Fin r' → F)
            (ap' bp' : Fin r' → Fin r' → F) (q' : Fin r' → (Fin k → F) → F),
            (∀ a b : Fin r', a < b → idx' a < idx' b) ∧
            Module.finrank F U' + (t + 1) = k + r' ∧
            (∀ a y, q' a y =
              (α' a y + ac' a + ∑ b : Fin r', if b.val < a.val then ap' a b * q' b y else 0) *
              (β' a y + bc' a + ∑ b : Fin r', if b.val < a.val then bp' a b * q' b y else 0)) ∧
            (∀ (j : Fin (t + 1)) (y z : Fin k → F), z ∈ U' →
              let x0' := M' y + v0' + ∑ a : Fin r', q' a y • w' a
              S.p ⟨j.val, by omega⟩ (x0' + z) y =
                if h : ∃ a : Fin r', idx' a = j then q' h.choose y else 0) := by
        intro φ_z y_lin c_y p_y u huU hφu hkill_eq
        let U' : Submodule F (Fin k → F) := U ⊓ LinearMap.ker φ_z
        have hdim' : Module.finrank F U' + 1 = Module.finrank F U := by
          let φU : U →ₗ[F] F := φ_z.domRestrict U
          have hsurj : Function.Surjective φU := by
            intro c
            refine ⟨c • ⟨u, huU⟩, ?_⟩
            simp [φU, map_smul, hφu]
          have hrg : Module.finrank F (LinearMap.range φU) = 1 := by
            rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
          have hrn := LinearMap.finrank_range_add_finrank_ker φU
          have hker_eq : Module.finrank F (LinearMap.ker φU) = Module.finrank F U' := by
            let e : LinearMap.ker φU ≃ₗ[F] U' :=
              { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
                map_add' := fun _ _ => rfl
                map_smul' := fun _ _ => rfl
                invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }
            exact e.finrank_eq
          omega
        let idx' : Fin r ↪ Fin (t + 1) := idx.trans ⟨Fin.castSucc, Fin.castSucc_injective t⟩
        let M' : (Fin k → F) →ₗ[F] (Fin k → F) := M + y_lin.smulRight u
        let v0' : Fin k → F := v0 + c_y • u
        let w' : Fin r → (Fin k → F) := fun a => w a + p_y a • u
        refine ⟨U', r, idx', M', v0', w', α, β, ac, bc, ap, bp, q,
          fun a b hab => Fin.castSucc_lt_castSucc_iff.mpr (hmono a b hab), by omega, hq, ?_⟩
        intro j y z hz'
        have hzU : z ∈ U := hz'.1
        have hzφ : φ_z z = 0 := hz'.2
        let δ : Fin k → F := (y_lin y + c_y + ∑ a : Fin r, p_y a * q a y) • u
        have hδU : δ ∈ U := U.smul_mem _ huU
        have hshift : (M' y + v0' + ∑ a : Fin r, q a y • w' a) + z = x0 y + (δ + z) := by
          dsimp only [M', v0', w', x0, δ]
          simp only [LinearMap.add_apply, LinearMap.smulRight_apply, smul_add,
            Finset.sum_add_distrib, add_smul, Finset.sum_smul]
          have hsum_smul : (∑ a : Fin r, q a y • (p_y a • u)) =
              ∑ a : Fin r, (p_y a * q a y) • u :=
            Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]
          rw [hsum_smul]; abel
        dsimp only
        rw [hshift]
        by_cases hjlt : j.val < t
        · have hj' := hinv ⟨j.val, hjlt⟩ y (δ + z) (U.add_mem hδU hzU)
          rw [hj']
          have hiff : (∃ a : Fin r, idx' a = j) ↔ (∃ a : Fin r, idx a = ⟨j.val, hjlt⟩) := by
            constructor
            · rintro ⟨a, ha⟩; exact ⟨a, Fin.ext (by simpa [idx'] using congrArg Fin.val ha)⟩
            · rintro ⟨a, ha⟩; exact ⟨a, Fin.ext (by simpa [idx'] using congrArg Fin.val ha)⟩
          by_cases hex : ∃ a : Fin r, idx a = ⟨j.val, hjlt⟩
          · have hex' : ∃ a : Fin r, idx' a = j := hiff.mpr hex
            simp only [hex, hex', ↓reduceDIte]
            have hch : hex'.choose = hex.choose :=
              idx.injective (by
                have h1 := congrArg Fin.val hex'.choose_spec
                have h2 := congrArg Fin.val hex.choose_spec
                exact Fin.ext (by simpa [idx'] using h1.trans h2.symm))
            rw [hch]
          · have hnex' : ¬ ∃ a : Fin r, idx' a = j := fun h => hex (hiff.mp h)
            simp [hex, hnex']
        · have hj_eq : j.val = t := by omega
          have hnex' : ¬ ∃ a : Fin r, idx' a = j := by
            rintro ⟨a, ha⟩
            have := congrArg Fin.val ha
            simp only [idx', Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
              Fin.val_castSucc] at this
            have := (idx a).isLt; omega
          simp only [hnex', ↓reduceDIte]
          have hfin_eq : (⟨j.val, by omega⟩ : Fin s) = tFin := Fin.ext hj_eq
          rw [hfin_eq]
          apply hkill_eq y (δ + z) (U.add_mem hδU hzU)
          simp only [δ, map_add, map_smul, hφu, hzφ, smul_eq_mul, mul_one, add_zero]
          exact f_add_self _
      -- Now split: either α_z vanishes on U ∧ β_z vanishes on U (surviving gate), or kill it!
      by_cases hα : ∃ u ∈ U, α_z u ≠ 0
      · rcases hα with ⟨u, huU, hne⟩
        have h1 : α_z u = 1 := (f_ne_zero_iff _).mp hne
        exact hkill α_z a_y_lin a_c a_p u huU h1 (fun y z hz h0 => by
          rw [S.hp tFin (x0 y + z) y, hA_eval y z hz, h0, zero_mul])
      · by_cases hβ : ∃ u ∈ U, β_z u ≠ 0
        · rcases hβ with ⟨u, huU, hne⟩
          have h1 : β_z u = 1 := (f_ne_zero_iff _).mp hne
          exact hkill β_z b_y_lin b_c b_p u huU h1 (fun y z hz h0 => by
            rw [S.hp tFin (x0 y + z) y, hB_eval y z hz, h0, mul_zero])
        · -- Surviving gate: r → r + 1!
          push Not at hα hβ
          let idx' : Fin (r + 1) ↪ Fin (t + 1) :=
            ⟨fun a => if h : a.val < r then Fin.castSucc (idx ⟨a.val, h⟩) else Fin.last t, by
              intro a1 a2 heq
              by_cases h1 : a1.val < r <;> by_cases h2 : a2.val < r
              · simp only [h1, h2, ↓reduceDIte] at heq
                have := idx.injective (Fin.castSucc_injective t heq)
                exact Fin.ext (by simpa using congrArg Fin.val this)
              · simp only [h1, h2, ↓reduceDIte] at heq
                have := congrArg Fin.val heq
                simp only [Fin.val_castSucc, Fin.val_last] at this
                have := (idx ⟨a1.val, h1⟩).isLt; omega
              · simp only [h1, h2, ↓reduceDIte] at heq
                have := congrArg Fin.val heq
                simp only [Fin.val_castSucc, Fin.val_last] at this
                have := (idx ⟨a2.val, h2⟩).isLt; omega
              · exact Fin.ext (by omega)⟩
          let w' : Fin (r + 1) → (Fin k → F) := fun a => if h : a.val < r then w ⟨a.val, h⟩ else 0
          let α' : Fin (r + 1) → (Fin k → F) →ₗ[F] F := fun a =>
            if h : a.val < r then α ⟨a.val, h⟩ else a_y_lin
          let β' : Fin (r + 1) → (Fin k → F) →ₗ[F] F := fun a =>
            if h : a.val < r then β ⟨a.val, h⟩ else b_y_lin
          let ac' : Fin (r + 1) → F := fun a => if h : a.val < r then ac ⟨a.val, h⟩ else a_c
          let bc' : Fin (r + 1) → F := fun a => if h : a.val < r then bc ⟨a.val, h⟩ else b_c
          let ap' : Fin (r + 1) → Fin (r + 1) → F := fun a b =>
            if ha : a.val < r then
              if hb : b.val < r then ap ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
            else if hb : b.val < r then a_p ⟨b.val, hb⟩ else 0
          let bp' : Fin (r + 1) → Fin (r + 1) → F := fun a b =>
            if ha : a.val < r then
              if hb : b.val < r then bp ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
            else if hb : b.val < r then b_p ⟨b.val, hb⟩ else 0
          let qNew : (Fin k → F) → F := fun y =>
            (a_y_lin y + a_c + ∑ a : Fin r, a_p a * q a y) *
            (b_y_lin y + b_c + ∑ a : Fin r, b_p a * q a y)
          let q' : Fin (r + 1) → (Fin k → F) → F := fun a y =>
            if h : a.val < r then q ⟨a.val, h⟩ y else qNew y
          have hx0_eq : ∀ y, M y + v0 + ∑ a : Fin (r + 1), q' a y • w' a = x0 y := by
            intro y; dsimp only [x0]; congr 1
            rw [Fin.sum_univ_castSucc]
            have hlast : ¬ ((Fin.last r).val < r) := by simp
            simp only [w', q', hlast, ↓reduceDIte, smul_zero, add_zero]
            refine Finset.sum_congr rfl fun a _ => ?_
            have ha : (Fin.castSucc a).val < r := a.isLt
            simp only [ha, ↓reduceDIte]; rfl
          refine ⟨U, r + 1, idx', M, v0, w', α', β', ac', bc', ap', bp', q', ?_, by omega, ?_, ?_⟩
          · intro a b hab
            by_cases hb : b.val < r
            · have ha : a.val < r := lt_trans hab hb
              change (if h : a.val < r then Fin.castSucc (idx ⟨a.val, h⟩) else Fin.last t) <
                (if h : b.val < r then Fin.castSucc (idx ⟨b.val, h⟩) else Fin.last t)
              simp only [ha, hb, ↓reduceDIte]
              exact Fin.castSucc_lt_castSucc_iff.mpr (hmono ⟨a.val, ha⟩ ⟨b.val, hb⟩ hab)
            · have ha : a.val < r := by omega
              change (if h : a.val < r then Fin.castSucc (idx ⟨a.val, h⟩) else Fin.last t) <
                (if h : b.val < r then Fin.castSucc (idx ⟨b.val, h⟩) else Fin.last t)
              simp only [ha, hb, ↓reduceDIte]
              exact Fin.castSucc_lt_last _
          · intro a y
            by_cases ha : a.val < r
            · simp only [q', α', β', ac', bc', ha, ↓reduceDIte]
              rw [hq ⟨a.val, ha⟩ y]
              congr 1
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last r).val < a.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun b _ => ?_
                have hb : (Fin.castSucc b).val < r := b.isLt
                simp only [ap', ha, hb, ↓reduceDIte]; rfl
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last r).val < a.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun b _ => ?_
                have hb : (Fin.castSucc b).val < r := b.isLt
                simp only [bp', ha, hb, ↓reduceDIte]; rfl
            · have ha_eq : a.val = r := by omega
              simp only [q', α', β', ac', bc', ha, ↓reduceDIte, qNew]
              congr 1
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last r).val < a.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun b _ => ?_
                have hb : (Fin.castSucc b).val < r := b.isLt
                have hba : (Fin.castSucc b).val < a.val := by simp [ha_eq, b.isLt]
                simp only [ap', ha, hb, hba, ↓reduceDIte, ↓reduceIte]; rfl
              · congr 1
                rw [Fin.sum_univ_castSucc]
                have hlast : ¬ ((Fin.last r).val < a.val) := by simp; omega
                simp only [hlast, ↓reduceIte, add_zero]
                refine Finset.sum_congr rfl fun b _ => ?_
                have hb : (Fin.castSucc b).val < r := b.isLt
                have hba : (Fin.castSucc b).val < a.val := by simp [ha_eq, b.isLt]
                simp only [bp', ha, hb, hba, ↓reduceDIte, ↓reduceIte]; rfl
          · intro j y z hz
            dsimp only
            rw [hx0_eq y]
            by_cases hjlt : j.val < t
            · rw [hinv ⟨j.val, hjlt⟩ y z hz]
              by_cases hex : ∃ a : Fin r, idx a = ⟨j.val, hjlt⟩
              · have hex' : ∃ a : Fin (r + 1), idx' a = j := by
                  rcases hex with ⟨a, ha⟩
                  refine ⟨Fin.castSucc a, Fin.ext ?_⟩
                  change (if h : (Fin.castSucc a).val < r then Fin.castSucc (idx ⟨(Fin.castSucc a).val, h⟩) else Fin.last t).val = j.val
                  simp only [Fin.val_castSucc, a.isLt, ↓reduceDIte]
                  exact congrArg Fin.val ha
                simp only [hex, hex', ↓reduceDIte]
                have hlt_ch : hex'.choose.val < r := by
                  by_contra hge
                  have h1 := congrArg Fin.val hex'.choose_spec
                  change (if h : hex'.choose.val < r then Fin.castSucc (idx ⟨hex'.choose.val, h⟩) else Fin.last t).val = j.val at h1
                  simp only [hge, ↓reduceDIte, Fin.val_last] at h1
                  omega
                have hch_eq : (⟨hex'.choose.val, hlt_ch⟩ : Fin r) = hex.choose :=
                  idx.injective (Fin.ext (by
                    have h1 := congrArg Fin.val hex'.choose_spec
                    have h2 := congrArg Fin.val hex.choose_spec
                    change (if h : hex'.choose.val < r then Fin.castSucc (idx ⟨hex'.choose.val, h⟩) else Fin.last t).val = j.val at h1
                    simp only [hlt_ch, ↓reduceDIte, Fin.val_castSucc] at h1
                    exact h1.trans h2.symm))
                simp only [q', hlt_ch, ↓reduceDIte, hch_eq]
              · have hnex' : ¬ ∃ a : Fin (r + 1), idx' a = j := by
                  rintro ⟨a, ha⟩
                  have h1 := congrArg Fin.val ha
                  change (if h : a.val < r then Fin.castSucc (idx ⟨a.val, h⟩) else Fin.last t).val = j.val at h1
                  by_cases hlt_a : a.val < r
                  · apply hex; refine ⟨⟨a.val, hlt_a⟩, Fin.ext ?_⟩
                    simp only [hlt_a, ↓reduceDIte, Fin.val_castSucc] at h1
                    exact h1
                  · simp only [hlt_a, ↓reduceDIte, Fin.val_last] at h1
                    omega
                simp [hex, hnex']
            · have hj_eq : j.val = t := by omega
              have hex' : ∃ a : Fin (r + 1), idx' a = j := by
                refine ⟨Fin.last r, Fin.ext ?_⟩
                change (if h : (Fin.last r).val < r then Fin.castSucc (idx ⟨(Fin.last r).val, h⟩) else Fin.last t).val = j.val
                have hnot : ¬ ((Fin.last r).val < r) := by simp
                simp [hnot, hj_eq]
              simp only [hex', ↓reduceDIte]
              have hch : hex'.choose = Fin.last r := by
                apply idx'.injective
                rw [hex'.choose_spec]
                apply Fin.ext
                change j.val = (if h : (Fin.last r).val < r then Fin.castSucc (idx ⟨(Fin.last r).val, h⟩) else Fin.last t).val
                have hnot : ¬ ((Fin.last r).val < r) := by simp
                simp [hnot, hj_eq]
              rw [hch]
              have hnotlt : ¬ ((Fin.last r).val < r) := by simp
              simp only [q', hnotlt, ↓reduceDIte, qNew]
              have hfin : (⟨j.val, by omega⟩ : Fin s) = tFin := Fin.ext hj_eq
              rw [hfin, S.hp tFin (x0 y + z) y, hA_eval y z hz, hB_eval y z hz,
                hα z hz, hβ z hz, zero_add, zero_add]
  -- Apply hstep at t = s!
  obtain ⟨U, r, idx, M, v0, w, α, β, ac, bc, ap, bp, q, _, hdim, hq, hinv⟩ := hstep s le_rfl
  rcases htarget with ⟨ox, oy, oc, op, htarget⟩
  let x0 : (Fin k → F) → (Fin k → F) := fun y => M y + v0 + ∑ a : Fin r, q a y • w a
  have hsum_out : ∀ y z, z ∈ U →
      (∑ j : Fin s, op j * S.p j (x0 y + z) y) = ∑ a : Fin r, op (idx a) * q a y := by
    intro y z hz
    have h1 : (∑ j : Fin s, op j * S.p j (x0 y + z) y) =
        ∑ j ∈ Finset.univ.image idx, op j * S.p j (x0 y + z) y := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hnot => ?_
      have hnex : ¬ ∃ a : Fin r, idx a = j := by
        intro ⟨a, ha⟩; exact hnot (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      rw [hinv j y z hz]
      simp [hnex]
    rw [h1, Finset.sum_image (fun a _ b _ h => idx.injective h)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hinv (idx a) y z hz]
    have hex : ∃ a' : Fin r, idx a' = idx a := ⟨a, rfl⟩
    simp only [hex, ↓reduceDIte]
    rw [idx.injective hex.choose_spec]
  -- Deduce U = ⊥!
  have hU_bot : U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hdiff : ∀ y : Fin k → F, dotProduct z y = dotProduct ox z := by
      intro y
      have h1 := htarget (x0 y + z) y
      have h0 := htarget (x0 y + 0) y
      rw [hsum_out y z hz] at h1
      rw [hsum_out y 0 U.zero_mem] at h0
      simp only [add_dotProduct, dotProduct_add, zero_dotProduct, add_zero] at h1 h0
      have hadd := congrArg₂ (· + ·) h1 h0
      have hlhs : (dotProduct (x0 y) y + dotProduct z y + target y) +
          (dotProduct (x0 y) y + target y) = dotProduct z y := by
        ring_nf; simp [show (2 : F) = 0 by decide]
      have hrhs : (dotProduct ox (x0 y) + dotProduct ox z + dotProduct oy y + oc +
            ∑ a : Fin r, op (idx a) * q a y) +
          (dotProduct ox (x0 y) + dotProduct oy y + oc +
            ∑ a : Fin r, op (idx a) * q a y) = dotProduct ox z := by
        ring_nf; simp [show (2 : F) = 0 by decide]
      rw [hlhs, hrhs] at hadd
      exact hadd
    have hox0 : dotProduct ox z = 0 := by
      have := hdiff 0; simpa using this.symm
    funext i
    have hi := hdiff (unitF i)
    rw [hox0] at hi
    have hdot : dotProduct z (unitF i) = z i := by
      unfold dotProduct
      rw [Finset.sum_eq_single i]
      · simp [unitF]
      · intro j _ hji; simp [unitF, Ne.symm hji]
      · intro hm; exact absurd (Finset.mem_univ i) hm
    rw [hdot] at hi
    exact hi
  have hkr : k + r ≤ s := by
    rw [hU_bot, finrank_bot, zero_add] at hdim; omega
  -- Evaluate at z = 0 to solve for target y = Q y + ∑ a, (ℓ a y + lc a) * q a y!
  let ℓ : Fin r → (Fin k → F) →ₗ[F] F := fun a => dotLin (w a)
  let lc : Fin r → F := fun a => dotProduct ox (w a) + op (idx a)
  let Y : YSLP k r :=
    { ℓ := ℓ, lc := lc, α := α, ac := ac, ap := ap, β := β, bc := bc, bp := bp, q := q, hq := hq }
  let Q : (Fin k → F) → F := fun y =>
    dotProduct (M y + v0) y + dotProduct (fun i => oy i + dotProduct ox (M (unitF i))) y +
      (dotProduct ox v0 + oc)
  have hQ_quad : isQuad Q := isQuad_dotProduct_lin M v0 _ _
  refine ⟨r, hkr, Y, Q, hQ_quad, fun y => ?_⟩
  have h0 := htarget (x0 y + 0) y
  rw [hsum_out y 0 U.zero_mem, add_zero] at h0
  have hoxM : dotProduct ox (M y) = dotProduct (fun i => dotProduct ox (M (unitF i))) y := by
    conv_lhs => rw [vec_eq_sum_unit y]
    simp only [map_sum, map_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h0' : dotProduct (M y + v0) y + (∑ a : Fin r, q a y * dotProduct (w a) y) + target y =
      dotProduct (fun i => dotProduct ox (M (unitF i))) y + dotProduct ox v0 +
      (∑ a : Fin r, q a y * dotProduct ox (w a)) + dotProduct oy y + oc +
      ∑ a : Fin r, op (idx a) * q a y := by
    have h1 := h0
    dsimp only [x0] at h1
    simp only [add_dotProduct, dotProduct_add, sum_dotProduct, dotProduct_sum,
      smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1
    rw [hoxM] at h1
    simpa [add_assoc, add_left_comm, add_comm] using h1
  have hsum_combine : (∑ a : Fin r, (Y.ℓ a y + Y.lc a) * Y.q a y) =
      (∑ a : Fin r, q a y * dotProduct (w a) y) +
      (∑ a : Fin r, q a y * dotProduct ox (w a)) +
      (∑ a : Fin r, op (idx a) * q a y) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [Y, ℓ, lc, dotLin]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]; ring
  have hQ_eq : Q y = dotProduct (M y + v0) y + dotProduct oy y +
      dotProduct (fun i => dotProduct ox (M (unitF i))) y + dotProduct ox v0 + oc := by
    dsimp only [Q]
    have : dotProduct (fun i => oy i + dotProduct ox (M (unitF i))) y =
        dotProduct oy y + dotProduct (fun i => dotProduct ox (M (unitF i))) y := by
      unfold dotProduct; simp [add_mul, Finset.sum_add_distrib]
    rw [this]; ring
  rw [hQ_eq, hsum_combine]
  have h2 := congrArg (· + (dotProduct (M y + v0) y + ∑ a : Fin r, q a y * dotProduct (w a) y)) h0'
  have hlhs : dotProduct (M y + v0) y + (∑ a : Fin r, q a y * dotProduct (w a) y) + target y +
      (dotProduct (M y + v0) y + ∑ a : Fin r, q a y * dotProduct (w a) y) = target y := by
    ring_nf; simp [show (2 : F) = 0 by decide]
  rw [hlhs] at h2
  rw [h2]; ring

/-! ## Section 5: Dimension bound (`d ≤ 6`) and saturation dichotomy (`d = 6`) -/

private def std3 (a b c : Fin 3 → F) : F :=
  a 0 * b 1 * c 2 + a 0 * b 2 * c 1 +
  a 1 * b 0 * c 2 + a 1 * b 2 * c 0 +
  a 2 * b 0 * c 1 + a 2 * b 1 * c 0

private def std3Lin (v : Fin 3 → F) : (Fin 3 → F) →ₗ[F] (Fin 3 → F) →ₗ[F] F where
  toFun a :=
    { toFun := fun b => std3 v a b
      map_add' := fun b1 b2 => by simp only [std3, Pi.add_apply]; ring
      map_smul' := fun s b => by simp only [std3, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' a1 a2 := LinearMap.ext fun b => by simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, std3, Pi.add_apply]; ring
  map_smul' s a := LinearMap.ext fun b => by simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, std3, Pi.smul_apply]; ring

private lemma bilRank_std3 (v : Fin 3 → F) :
    bilRank (std3Lin v) = if v = 0 then 0 else 2 := by
  by_cases hv : v = 0
  · subst hv
    have h0 : std3Lin 0 = 0 := LinearMap.ext fun a => LinearMap.ext fun b => by simp [std3Lin, std3]
    simp [bilRank, h0]
  · simp only [hv, ↓reduceIte]
    have hker : LinearMap.ker (std3Lin v) = F ∙ v := by
      apply le_antisymm
      · intro a ha
        rw [LinearMap.mem_ker] at ha
        have h0 := congrArg (fun f => f (unitF 0)) ha
        have h1 := congrArg (fun f => f (unitF 1)) ha
        have h2 := congrArg (fun f => f (unitF 2)) ha
        simp only [std3Lin, LinearMap.coe_mk, AddHom.coe_mk, std3, unitF, LinearMap.zero_apply,
          Fin.reduceEq, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at h0 h1 h2
        rw [Submodule.mem_span_singleton]
        have hex : ∃ i : Fin 3, v i = 1 := by
          by_contra hall; push Not at hall; apply hv; funext i
          rcases f_eq_zero_or_one (v i) with h | h
          · exact h
          · exact absurd h (hall i)
        rcases hex with ⟨i, hi⟩
        refine ⟨a i, ?_⟩
        funext j
        have hrel : ∀ (v0 v1 v2 a0 a1 a2 : F),
            v1 * a2 + v2 * a1 = 0 → v0 * a2 + v2 * a0 = 0 → v0 * a1 + v1 * a0 = 0 →
            (v0 = 1 → a0 * v0 = a0 ∧ a0 * v1 = a1 ∧ a0 * v2 = a2) ∧
            (v1 = 1 → a1 * v0 = a0 ∧ a1 * v1 = a1 ∧ a1 * v2 = a2) ∧
            (v2 = 1 → a2 * v0 = a0 ∧ a2 * v1 = a1 ∧ a2 * v2 = a2) := by
          decide
        have hr := hrel (v 0) (v 1) (v 2) (a 0) (a 1) (a 2) h0 h1 h2
        fin_cases i <;> fin_cases j <;> simp only [Pi.smul_apply, smul_eq_mul]
        · exact (hr.1 hi).1
        · exact (hr.1 hi).2.1
        · exact (hr.1 hi).2.2
        · exact (hr.2.1 hi).1
        · exact (hr.2.1 hi).2.1
        · exact (hr.2.1 hi).2.2
        · exact (hr.2.2 hi).1
        · exact (hr.2.2 hi).2.1
        · exact (hr.2.2 hi).2.2
      · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
        apply LinearMap.ext; intro a
        simp only [std3Lin, LinearMap.coe_mk, AddHom.coe_mk, std3, LinearMap.zero_apply]
        ring_nf; simp [show (2 : F) = 0 by decide]
    have hrn := LinearMap.finrank_range_add_finrank_ker (std3Lin v)
    rw [Module.finrank_fin_fun, hker, finrank_span_singleton hv] at hrn
    dsimp only [bilRank]; omega

private lemma finrank_range_block_sum {ι : Type*} [Fintype ι] {U V : ι → Type*}
    [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)] [∀ i, Module.Finite F (U i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)] [∀ i, Module.Finite F (V i)]
    (f : ∀ i, U i →ₗ[F] V i) :
    Module.finrank F (LinearMap.range (LinearMap.pi fun i => (f i).comp (LinearMap.proj i))) =
      ∑ i : ι, Module.finrank F (LinearMap.range (f i)) := by
  let L : (∀ i, U i) →ₗ[F] (∀ i, V i) := LinearMap.pi fun i => (f i).comp (LinearMap.proj i)
  let e : LinearMap.range L ≃ₗ[F] (∀ i, LinearMap.range (f i)) :=
    { toFun := fun ⟨y, hy⟩ i => ⟨y i, hy.choose i, by simpa [L] using congrFun hy.choose_spec i⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun g =>
        ⟨fun i => (g i).1, fun i => (g i).2.choose, by
          funext i; exact (g i).2.choose_spec⟩
      left_inv := fun ⟨y, _⟩ => rfl
      right_inv := fun g => by funext i; exact Subtype.ext rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

private lemma bilRank_of_surj_std3 {k r : ℕ}
    (Φ : (Fin k → F) →ₗ[F] (Fin r → Fin 3 → F)) (hsurj : Function.Surjective Φ)
    (T : (Fin k → F) →ₗ[F] (Fin k → F) →ₗ[F] F) (v : Fin k → F)
    (hT : ∀ a b, T a b = ∑ i : Fin r, std3 (Φ v i) (Φ a i) (Φ b i)) :
    bilRank T = ∑ i : Fin r, if Φ v i = 0 then 0 else 2 := by
  let L : (Fin r → Fin 3 → F) →ₗ[F] (Fin r → (Fin 3 → F) →ₗ[F] F) :=
    LinearMap.pi fun i => (std3Lin (Φ v i)).comp (LinearMap.proj i)
  -- Pullback map from (Fin r → (Fin 3 → F) →ₗ[F] F) to ((Fin k → F) →ₗ[F] F)
  let pb : (Fin r → (Fin 3 → F) →ₗ[F] F) →ₗ[F] ((Fin k → F) →ₗ[F] F) :=
    { toFun := fun g =>
        { toFun := fun b => ∑ i : Fin r, g i (Φ b i)
          map_add' := fun b1 b2 => by simp [map_add, Finset.sum_add_distrib]
          map_smul' := fun s b => by simp [map_smul, Finset.mul_sum] }
      map_add' := fun g1 g2 => LinearMap.ext fun b => by simp [Finset.sum_add_distrib]
      map_smul' := fun s g => LinearMap.ext fun b => by simp [Finset.mul_sum] }
  have hpb_inj : Function.Injective pb := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    funext i
    apply LinearMap.ext; intro c
    let t : Fin r → Fin 3 → F := fun j => if j = i then c else 0
    obtain ⟨b, hb⟩ := hsurj t
    have h0 := congrArg (fun f => f b) hg
    simp only [pb, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, hb] at h0
    rw [Finset.sum_eq_single i] at h0
    · simpa [t] using h0
    · intro j _ hji; simp [t, hji]
    · intro hm; exact absurd (Finset.mem_univ i) hm
  have hT_eq : T = pb.comp (L.comp Φ) := by
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
    simp only [LinearMap.comp_apply, pb, L, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply,
      LinearMap.proj_apply, std3Lin]
    exact hT a b
  rw [bilRank, hT_eq, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hsurj, Submodule.map_top,
    (Submodule.equivMapOfInjective pb hpb_inj (LinearMap.range L)).finrank_eq.symm]
  rw [finrank_range_block_sum (fun i => std3Lin (Φ v i))]
  refine Finset.sum_congr rfl fun i _ => bilRank_std3 (Φ v i)

private lemma bilRank_direct_sum {n m k : ℕ}
    (g : (Fin n → F) → F) (hg : isCubic g)
    (e : (Fin n ⊕ (Fin m × Fin 3)) ≃ Fin k)
    (target : (Fin k → F) → F)
    (htarget_def : ∀ y, target y = g (fun i => y (e (Sum.inl i))) +
      ∑ j : Fin m, y (e (Sum.inr (j, 0))) * y (e (Sum.inr (j, 1))) * y (e (Sum.inr (j, 2))))
    (htarget_cub : isCubic target)
    (w : Fin k → F) :
    bilRank (thirdLin target htarget_cub w) =
      bilRank (thirdLin g hg (fun i => w (e (Sum.inl i)))) +
      ∑ j : Fin m, if (fun t : Fin 3 => w (e (Sum.inr (j, t)))) = 0 then 0 else 2 := by
  let wV : Fin n → F := fun i => w (e (Sum.inl i))
  let wP : Fin m → Fin 3 → F := fun j t => w (e (Sum.inr (j, t)))
  -- Compute thirdF target a b c as thirdF g aV bV cV + ∑ j, std3 (aP j) (bP j) (cP j)
  have hthird_decomp : ∀ a b c : Fin k → F,
      thirdF target a b c =
        thirdF g (fun i => a (e (Sum.inl i))) (fun i => b (e (Sum.inl i))) (fun i => c (e (Sum.inl i))) +
        ∑ j : Fin m, std3 (fun t => a (e (Sum.inr (j, t))))
          (fun t => b (e (Sum.inr (j, t)))) (fun t => c (e (Sum.inr (j, t)))) := by
    intro a b c
    have hfun : target = fun y => g (fun i => y (e (Sum.inl i))) +
        ∑ j : Fin m, (LinearMap.proj (R := F) (e (Sum.inr (j, 0))) y) *
          (LinearMap.proj (R := F) (e (Sum.inr (j, 1))) y) * (LinearMap.proj (R := F) (e (Sum.inr (j, 2))) y) := by
      funext y; exact htarget_def y
    rw [hfun, thirdF_add_fun,
      show thirdF (fun y => g (fun i => y (e (Sum.inl i)))) a b c =
        thirdF g (fun i => a (e (Sum.inl i))) (fun i => b (e (Sum.inl i))) (fun i => c (e (Sum.inl i))) from rfl]
    congr 1
    have hsum3 : ∀ (s : Finset (Fin m)) (f : Fin m → (Fin k → F) → F),
        thirdF (fun y => ∑ j ∈ s, f j y) a b c = ∑ j ∈ s, thirdF (f j) a b c := by
      intro s f; classical
      induction s using Finset.induction with
      | empty => simp [thirdF, diffF]
      | @insert j s hj ih =>
        have : (fun y => ∑ i ∈ insert j s, f i y) = fun y => f j y + ∑ i ∈ s, f i y := by
          funext y; exact Finset.sum_insert hj
        rw [this, thirdF_add_fun, ih, Finset.sum_insert hj]
    rw [hsum3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [thirdF_mul3]
    simp only [wedge3, std3, LinearMap.proj_apply]
    ring
  -- Isomorphism (Fin k → F) ≃ₗ (Fin n → F) × (Fin m → Fin 3 → F)
  let splitE : (Fin k → F) ≃ₗ[F] ((Fin n → F) × (Fin m → Fin 3 → F)) :=
    { toFun := fun y => (fun i => y (e (Sum.inl i)), fun j t => y (e (Sum.inr (j, t))))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p idx => match e.symm idx with
        | Sum.inl i => p.1 i
        | Sum.inr (j, t) => p.2 j t
      left_inv := fun y => by
        funext idx; cases h : e.symm idx with
        | inl i =>
          have : e (Sum.inl i) = idx := by rw [← h, e.apply_symm_apply]
          simp [h, this]
        | inr jt =>
          have : e (Sum.inr jt) = idx := by rw [← h, e.apply_symm_apply]
          simp [h, this]
      right_inv := fun ⟨p1, p2⟩ => by
        ext <;> simp }
  let L1 : (Fin n → F) →ₗ[F] ((Fin n → F) →ₗ[F] F) := thirdLin g hg wV
  let L2 : (Fin m → Fin 3 → F) →ₗ[F] (Fin m → (Fin 3 → F) →ₗ[F] F) :=
    LinearMap.pi fun j => (std3Lin (wP j)).comp (LinearMap.proj j)
  let Lprod : ((Fin n → F) × (Fin m → Fin 3 → F)) →ₗ[F]
      (((Fin n → F) →ₗ[F] F) × (Fin m → (Fin 3 → F) →ₗ[F] F)) :=
    LinearMap.prodMap L1 L2
  let pb : (((Fin n → F) →ₗ[F] F) × (Fin m → (Fin 3 → F) →ₗ[F] F)) ≃ₗ[F] ((Fin k → F) →ₗ[F] F) :=
    { toFun := fun p =>
        { toFun := fun b => p.1 (splitE b).1 + ∑ j : Fin m, p.2 j ((splitE b).2 j)
          map_add' := fun b1 b2 => by
            simp [map_add, Finset.sum_add_distrib]
            ring
          map_smul' := fun s b => by
            simp only [map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            rw [← Finset.mul_sum]; ring }
      map_add' := fun p1 p2 => LinearMap.ext fun b => by
        simp [Finset.sum_add_distrib]; ring
      map_smul' := fun s p => LinearMap.ext fun b => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Prod.smul_fst, Prod.smul_snd,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← Finset.mul_sum]; ring
      invFun := fun f =>
        ({ toFun := fun u => f (splitE.symm (u, 0))
           map_add' := fun u1 u2 => by
             have : (u1 + u2, (0 : Fin m → Fin 3 → F)) = (u1, 0) + (u2, 0) := by ext <;> simp
             rw [this, map_add, map_add]
           map_smul' := fun s u => by
             have : (s • u, (0 : Fin m → Fin 3 → F)) = s • (u, 0) := by ext <;> simp
             rw [this, map_smul, map_smul]; rfl },
         fun j =>
           { toFun := fun c => f (splitE.symm (0, fun j' => if j' = j then c else 0))
             map_add' := fun c1 c2 => by
               have : ((0 : Fin n → F), fun j' => if j' = j then c1 + c2 else 0) =
                   (0, fun j' => if j' = j then c1 else 0) + (0, fun j' => if j' = j then c2 else 0) := by
                 apply Prod.ext
                 · simp
                 · funext j'; simp only [Pi.add_apply]; by_cases hj : j' = j <;> simp [hj]
               rw [this, map_add, map_add]
             map_smul' := fun s c => by
               have : ((0 : Fin n → F), fun j' => if j' = j then s • c else 0) =
                   s • (0, fun j' => if j' = j then c else 0) := by
                 apply Prod.ext
                 · simp
                 · funext j'; simp only [Pi.smul_apply]; by_cases hj : j' = j <;> simp [hj]
               rw [this, map_smul, map_smul]; rfl })
      left_inv := fun ⟨p1, p2⟩ => by
        apply Prod.ext
        · apply LinearMap.ext; intro u; simp [splitE.apply_symm_apply]
        · funext j; apply LinearMap.ext; intro c
          simp only [LinearMap.coe_mk, AddHom.coe_mk, splitE.apply_symm_apply, map_zero, zero_add]
          rw [Finset.sum_eq_single j]
          · simp
          · intro j' _ hne; simp [hne]
          · intro hm; exact absurd (Finset.mem_univ j) hm
      right_inv := fun f => by
        apply LinearMap.ext; intro b
        have hdecomp : b = splitE.symm ((splitE b).1, 0) +
            ∑ j : Fin m, splitE.symm (0, fun j' => if j' = j then (splitE b).2 j else 0) := by
          apply splitE.injective
          simp only [map_add, map_sum, splitE.apply_symm_apply]
          apply Prod.ext
          · simp [Prod.fst_sum]
          · funext i
            simp only [Prod.snd_add, Prod.snd_sum, Pi.add_apply, zero_add, Finset.sum_apply]
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hji; simp [Ne.symm hji]
            · intro hm; exact absurd (Finset.mem_univ i) hm
        conv_rhs => rw [hdecomp]
        simp [map_add, map_sum] }
  have hcomp : thirdLin target htarget_cub w = pb.toLinearMap.comp (Lprod.comp splitE.toLinearMap) := by
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
    simpa [thirdLin, pb, Lprod, L1, L2, splitE, std3Lin, wV, wP] using hthird_decomp w a b
  rw [bilRank, hcomp, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr splitE.surjective, Submodule.map_top,
    LinearEquiv.finrank_map_eq pb]
  have hprod_rg : Module.finrank F (LinearMap.range Lprod) =
      Module.finrank F (LinearMap.range L1) + Module.finrank F (LinearMap.range L2) := by
    let M1 := (Fin n → F) →ₗ[F] F
    let M2 := Fin m → (Fin 3 → F) →ₗ[F] F
    let S1 : Submodule F (M1 × M2) := (LinearMap.range L1).map (LinearMap.inl F M1 M2)
    let S2 : Submodule F (M1 × M2) := (LinearMap.range L2).map (LinearMap.inr F M1 M2)
    have hsup : S1 ⊔ S2 = LinearMap.range Lprod := by
      apply le_antisymm
      · refine sup_le ?_ ?_
        · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
          exact ⟨(x, 0), by simp [Lprod, L1, L2]⟩
        · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
          exact ⟨(0, y), by simp [Lprod, L1, L2]⟩
      · rintro _ ⟨⟨x, y⟩, rfl⟩
        have hdecomp : Lprod (x, y) = (L1 x, 0) + (0, L2 y) := by
          apply Prod.ext <;> simp [Lprod]
        rw [hdecomp]
        exact Submodule.add_mem_sup ⟨L1 x, ⟨x, rfl⟩, rfl⟩ ⟨L2 y, ⟨y, rfl⟩, rfl⟩
    have hinf : S1 ⊓ S2 = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨a, b⟩ ⟨⟨a', _, ha⟩, ⟨b', _, hb⟩⟩
      simp only [LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk.injEq] at ha hb
      rw [Submodule.mem_bot]
      exact Prod.ext hb.1.symm ha.2.symm
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq S1 S2
    rw [hsup, hinf, finrank_bot, add_zero] at hadd
    have h1 : Module.finrank F S1 = Module.finrank F (LinearMap.range L1) :=
      (Submodule.equivMapOfInjective (LinearMap.inl F M1 M2) (fun _ _ h => congrArg Prod.fst h) (LinearMap.range L1)).finrank_eq.symm
    have h2 : Module.finrank F S2 = Module.finrank F (LinearMap.range L2) :=
      (Submodule.equivMapOfInjective (LinearMap.inr F M1 M2) (fun _ _ h => congrArg Prod.snd h) (LinearMap.range L2)).finrank_eq.symm
    rw [hadd, h1, h2]
  rw [hprod_rg, finrank_range_block_sum (fun j => std3Lin (wP j))]
  congr 1
  refine Finset.sum_congr rfl fun j _ => bilRank_std3 (wP j)

private lemma yslp_dim_and_dichotomy {n m k r : ℕ}
    (g : (Fin n → F) → F) (R : Submodule F (Fin n → F)) (hg : isCubic g)
    (hR : ∀ u, u ∈ R ↔ ∀ v w, thirdF g u v w = 0)
    (e : (Fin n ⊕ (Fin m × Fin 3)) ≃ Fin k)
    (target : (Fin k → F) → F)
    (htarget_def : ∀ y, target y = g (fun i => y (e (Sum.inl i))) +
      ∑ j : Fin m, y (e (Sum.inr (j, 0))) * y (e (Sum.inr (j, 1))) * y (e (Sum.inr (j, 2))))
    (hr_le : r ≤ m + 2)
    (Y : YSLP k r) (Q : (Fin k → F) → F) (hQ : isQuad Q)
    (htarget_eq : ∀ y, target y = Q y + ∑ a : Fin r, (Y.ℓ a y + Y.lc a) * Y.q a y) :
    n - Module.finrank F R ≤ 5 ∨
      (n - Module.finrank F R = 6 ∧ ∃ u v : Fin n → F,
        bilRank (thirdLin g hg u) = 2 ∧
        bilRank (thirdLin g hg v) = 2 ∧
        bilRank (thirdLin g hg (u + v)) = 4) := by
  have hk_eq : k = n + 3 * m := by
    have hcard := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hcard
    omega
  have htarget_cub : isCubic target := by
    have hfun : target = fun y => g (fun i => y (e (Sum.inl i))) +
        ∑ j : Fin m, (LinearMap.proj (R := F) (e (Sum.inr (j, 0))) y) *
          (LinearMap.proj (R := F) (e (Sum.inr (j, 1))) y) * (LinearMap.proj (R := F) (e (Sum.inr (j, 2))) y) := by
      funext y; exact htarget_def y
    rw [hfun]
    apply isCubic_add
    · intro a b c d x
      have h := hg (fun i => a (e (Sum.inl i))) (fun i => b (e (Sum.inl i)))
        (fun i => c (e (Sum.inl i))) (fun i => d (e (Sum.inl i))) (fun i => x (e (Sum.inl i)))
      exact h
    · have hsum_cub : ∀ (s : Finset (Fin m)),
          isCubic (fun y => ∑ j ∈ s, (LinearMap.proj (R := F) (e (Sum.inr (j, 0))) y) *
            (LinearMap.proj (R := F) (e (Sum.inr (j, 1))) y) * (LinearMap.proj (R := F) (e (Sum.inr (j, 2))) y)) := by
        intro s; classical
        induction s using Finset.induction with
        | empty => intro a b c d x; simp [diffF]
        | @insert j s hj ih =>
          have : (fun y : Fin k → F => ∑ i ∈ insert j s, (LinearMap.proj (R := F) (e (Sum.inr (i, 0))) y) *
              (LinearMap.proj (R := F) (e (Sum.inr (i, 1))) y) * (LinearMap.proj (R := F) (e (Sum.inr (i, 2))) y)) =
              fun y : Fin k → F => (LinearMap.proj (R := F) (e (Sum.inr (j, 0))) y) *
                (LinearMap.proj (R := F) (e (Sum.inr (j, 1))) y) * (LinearMap.proj (R := F) (e (Sum.inr (j, 2))) y) +
                ∑ i ∈ s, (LinearMap.proj (R := F) (e (Sum.inr (i, 0))) y) *
                  (LinearMap.proj (R := F) (e (Sum.inr (i, 1))) y) * (LinearMap.proj (R := F) (e (Sum.inr (i, 2))) y) := by
            funext y; exact Finset.sum_insert hj
          rw [this]
          exact isCubic_add (isCubic_mul3 _ _ _) ih
      exact hsum_cub Finset.univ
  -- Radical R_T of target
  let RT : Submodule F (Fin k → F) :=
    { carrier := { u | ∀ v w, thirdF target u v w = 0 }
      zero_mem' := fun v w => thirdF_zero_left target v w, add_mem' := fun ha hb v w => by rw [thirdF_add_left htarget_cub, ha v w, hb v w, add_zero]
      smul_mem' := fun s _ ha v w => by rw [thirdF_smul_left htarget_cub, ha v w, mul_zero] }
  have hRT_iff : ∀ u : Fin k → F, u ∈ RT ↔
      (fun i => u (e (Sum.inl i))) ∈ R ∧ ∀ j : Fin m, (fun t : Fin 3 => u (e (Sum.inr (j, t)))) = 0 := by
    intro u
    have hrank_zero : (u ∈ RT) ↔ bilRank (thirdLin target htarget_cub u) = 0 := by
      constructor
      · intro hu
        have h0 : thirdLin target htarget_cub u = 0 :=
          LinearMap.ext fun v => LinearMap.ext fun w => hu v w
        simp [bilRank, h0]
      · intro hr v w
        have hbot : LinearMap.range (thirdLin target htarget_cub u) = ⊥ :=
          Submodule.finrank_eq_zero.mp hr
        have hmem : thirdLin target htarget_cub u v ∈ LinearMap.range (thirdLin target htarget_cub u) :=
          ⟨v, rfl⟩
        rw [hbot, Submodule.mem_bot] at hmem
        exact congrArg (fun f => f w) hmem
    have hrank_g_zero : ((fun i => u (e (Sum.inl i))) ∈ R) ↔
        bilRank (thirdLin g hg (fun i => u (e (Sum.inl i)))) = 0 := by
      constructor
      · intro hu
        have h0 : thirdLin g hg (fun i => u (e (Sum.inl i))) = 0 :=
          LinearMap.ext fun v => LinearMap.ext fun w => (hR _).mp hu v w
        simp [bilRank, h0]
      · intro hr
        rw [hR]; intro v w
        have hbot : LinearMap.range (thirdLin g hg (fun i => u (e (Sum.inl i)))) = ⊥ :=
          Submodule.finrank_eq_zero.mp hr
        have hmem : thirdLin g hg (fun i => u (e (Sum.inl i))) v ∈
            LinearMap.range (thirdLin g hg (fun i => u (e (Sum.inl i)))) := ⟨v, rfl⟩
        rw [hbot, Submodule.mem_bot] at hmem
        exact congrArg (fun f => f w) hmem
    rw [hrank_zero, hrank_g_zero, bilRank_direct_sum g hg e target htarget_def htarget_cub u]
    constructor
    · intro h0
      have h1 : bilRank (thirdLin g hg (fun i => u (e (Sum.inl i)))) = 0 := by omega
      have h2 : ∑ j : Fin m, (if (fun t : Fin 3 => u (e (Sum.inr (j, t)))) = 0 then 0 else 2) = 0 := by omega
      refine ⟨h1, fun j => ?_⟩
      have hj := Finset.sum_eq_zero_iff.mp h2 j (Finset.mem_univ j)
      split_ifs at hj with hz
      · exact hz
    · rintro ⟨h1, h2⟩
      rw [h1, zero_add]
      exact Finset.sum_eq_zero fun j _ => by simp [h2 j]
  have hRT_rank : Module.finrank F RT = Module.finrank F R := by
    let eR : RT ≃ₗ[F] R :=
      { toFun := fun ⟨u, hu⟩ => ⟨fun i => u (e (Sum.inl i)), ((hRT_iff u).mp hu).1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun ⟨v, hv⟩ =>
          ⟨fun idx => match e.symm idx with
            | Sum.inl i => v i
            | Sum.inr _ => 0, by
            rw [hRT_iff]; constructor
            · simpa using hv
            · intro j; funext t; simp⟩
        left_inv := fun ⟨u, hu⟩ => by
          apply Subtype.ext; funext idx
          cases h : e.symm idx with
          | inl i =>
            have he : e (Sum.inl i) = idx := by rw [← h, e.apply_symm_apply]
            simp [h, he]
          | inr jt =>
            have he : e (Sum.inr jt) = idx := by rw [← h, e.apply_symm_apply]
            have h0 := congrFun (((hRT_iff u).mp hu).2 jt.1) jt.2
            simp [h, ← he, h0]
        right_inv := fun ⟨v, _⟩ => by apply Subtype.ext; funext i; simp }
    exact eR.finrank_eq
  -- Define Φ : (Fin k → F) →ₗ (Fin r → Fin 3 → F) sending y ↦ a ↦ (ℓ a y, α a y, β a y)
  let Φ : (Fin k → F) →ₗ[F] (Fin r → Fin 3 → F) :=
    { toFun := fun y a t => match t with
        | 0 => Y.ℓ a y
        | 1 => Y.α a y
        | 2 => Y.β a y
      map_add' := fun y1 y2 => by
        funext a t; fin_cases t <;> simp [map_add]
      map_smul' := fun s y => by
        funext a t; fin_cases t <;> simp [map_smul] }
  -- Invariance of Y.q a under shifts that vanish on α b, β b for all b ≤ a
  have hq_inv : ∀ (u : Fin k → F) (a : Fin r),
      (∀ b : Fin r, b.val ≤ a.val → Y.α b u = 0 ∧ Y.β b u = 0) →
      ∀ y : Fin k → F, Y.q a (y + u) = Y.q a y := by
    intro u a
    suffices h : ∀ (m : ℕ) (hm : m < r),
        (∀ b : Fin r, b.val ≤ m → Y.α b u = 0 ∧ Y.β b u = 0) →
        ∀ y : Fin k → F, Y.q ⟨m, hm⟩ (y + u) = Y.q ⟨m, hm⟩ y from h a.val a.isLt
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm hvan y
      rw [Y.hq ⟨m, hm⟩ (y + u), Y.hq ⟨m, hm⟩ y]
      have ha0 := hvan ⟨m, hm⟩ le_rfl
      simp only [map_add, ha0.1, ha0.2, add_zero]
      have hsum_eq : ∀ (coeff : Fin r → F),
          (∑ b : Fin r, if b.val < m then coeff b * Y.q b (y + u) else 0) =
          (∑ b : Fin r, if b.val < m then coeff b * Y.q b y else 0) := by
        intro coeff
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs with hlt
        · rw [ih b.val hlt b.isLt (fun c hc => hvan c (by omega)) y]
        · rfl
      rw [hsum_eq (Y.ap ⟨m, hm⟩), hsum_eq (Y.bp ⟨m, hm⟩)]
  have hker_le_RT : LinearMap.ker Φ ≤ RT := by
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hvan : ∀ a : Fin r, Y.ℓ a u = 0 ∧ Y.α a u = 0 ∧ Y.β a u = 0 := fun a =>
      ⟨congrFun (congrFun hu a) 0, congrFun (congrFun hu a) 1, congrFun (congrFun hu a) 2⟩
    have hdiff_eq : diffF target u = diffF Q u := by
      funext y
      simp only [diffF_eq_add, htarget_eq]
      have hsum_eq : (∑ a : Fin r, (Y.ℓ a (y + u) + Y.lc a) * Y.q a (y + u)) =
          ∑ a : Fin r, (Y.ℓ a y + Y.lc a) * Y.q a y := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_add, (hvan a).1, add_zero, hq_inv u a (fun b _ => ⟨(hvan b).2.1, (hvan b).2.2⟩) y]
      rw [hsum_eq]; ring_nf; simp [show (2 : F) = 0 by decide]
    intro v w
    change diffF (diffF (diffF target u) v) w 0 = 0
    rw [hdiff_eq]
    exact hQ u v w 0
  have hrnΦ := LinearMap.finrank_range_add_finrank_ker Φ
  rw [Module.finrank_fin_fun] at hrnΦ
  have hrgΦ_le : Module.finrank F (LinearMap.range Φ) ≤ 3 * r := by
    have h1 := Submodule.finrank_le (LinearMap.range Φ)
    simp only [Module.finrank_pi_fintype, Module.finrank_fin_fun, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
    omega
  have hker_mono : Module.finrank F (LinearMap.ker Φ) ≤ Module.finrank F RT :=
    Submodule.finrank_mono hker_le_RT
  have hR_le_n : Module.finrank F R ≤ n := by
    have := Submodule.finrank_le R; rwa [Module.finrank_fin_fun] at this
  have hd_le_6 : n - Module.finrank F R ≤ 6 := by omega
  by_cases hd5 : n - Module.finrank F R ≤ 5
  · exact Or.inl hd5
  · -- Saturation case: d = 6!
    right
    have hd6 : n - Module.finrank F R = 6 := by omega
    refine ⟨hd6, ?_⟩
    have hr_eq : r = m + 2 := by omega
    have hrgΦ_eq : Module.finrank F (LinearMap.range Φ) = 3 * r := by omega
    have hker_eq : LinearMap.ker Φ = RT :=
      Submodule.eq_of_le_of_finrank_eq hker_le_RT (by omega)
    have hsurj : Function.Surjective Φ := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [hrgΦ_eq]
      simp only [Module.finrank_pi_fintype, Module.finrank_fin_fun, Module.finrank_self,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      ring
    -- Pick preimages eΦ b t with Φ (eΦ b t) = single (b, t)
    let single : Fin r → Fin 3 → (Fin r → Fin 3 → F) := fun b t a s =>
      if a = b ∧ s = t then 1 else 0
    choose eΦ heΦ using fun (b : Fin r) (t : Fin 3) => hsurj (single b t)
    have hΦ_e : ∀ b t a s, Φ (eΦ b t) a s = if a = b ∧ s = t then 1 else 0 := fun b t a s =>
      congrFun (congrFun (heΦ b t) a) s
    have hℓ_e : ∀ b t c, Y.ℓ c (eΦ b t) = if c = b ∧ (0 : Fin 3) = t then 1 else 0 :=
      fun b t c => hΦ_e b t c 0
    have hα_e : ∀ b t c, Y.α c (eΦ b t) = if c = b ∧ (1 : Fin 3) = t then 1 else 0 :=
      fun b t c => hΦ_e b t c 1
    have hβ_e : ∀ b t c, Y.β c (eΦ b t) = if c = b ∧ (2 : Fin 3) = t then 1 else 0 :=
      fun b t c => hΦ_e b t c 2
    -- Step 1: Every Y.q b is quadratic!
    have hq_quad : ∀ b : Fin r, isQuad (Y.q b) := by
      intro b
      have hvan0 : ∀ c : Fin r, Y.α c (eΦ b 0) = 0 ∧ Y.β c (eΦ b 0) = 0 := fun c =>
        ⟨by simp [hα_e], by simp [hβ_e]⟩
      have hdiff_b : diffF target (eΦ b 0) = fun y => diffF Q (eΦ b 0) y + Y.q b y := by
        funext y
        simp only [diffF_eq_add, htarget_eq]
        have hsum_diff :
            (∑ c : Fin r, (Y.ℓ c (y + eΦ b 0) + Y.lc c) * Y.q c (y + eΦ b 0)) =
            (∑ c : Fin r, (Y.ℓ c y + Y.lc c) * Y.q c y) + Y.q b y := by
          have hterm : ∀ c : Fin r,
              (Y.ℓ c (y + eΦ b 0) + Y.lc c) * Y.q c (y + eΦ b 0) =
              (Y.ℓ c y + Y.lc c) * Y.q c y + (if c = b then Y.q b y else 0) := by
            intro c
            rw [map_add, hq_inv (eΦ b 0) c (fun d _ => hvan0 d) y]
            have hℓc : Y.ℓ c (eΦ b 0) = if c = b then 1 else 0 := by simp [hℓ_e]
            rw [hℓc]
            split_ifs with hcb
            · subst hcb; ring
            · ring
          simp only [hterm, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single b]
          · simp
          · intro c _ hcb; simp [hcb]
          · intro hm; exact absurd (Finset.mem_univ b) hm
        rw [hsum_diff]; ring_nf; simp [show (2 : F) = 0 by decide]
      have hqb_eq : Y.q b = fun y => diffF target (eΦ b 0) y + diffF Q (eΦ b 0) y := by
        funext y; rw [hdiff_b]; ring_nf; simp [show (2 : F) = 0 by decide]
      rw [hqb_eq]
      apply isQuad_add
      · intro u v w x; exact htarget_cub (eΦ b 0) u v w x
      · intro u v w x
        have h : diffF (diffF (diffF Q (eΦ b 0)) u) v = fun _ => 0 := funext (hQ (eΦ b 0) u v)
        rw [h, diffF_const]
    -- Step 2: Every A_b and B_b is affine!
    let Afun : Fin r → (Fin k → F) → F := fun b y =>
      Y.α b y + Y.ac b + ∑ c : Fin r, if c.val < b.val then Y.ap b c * Y.q c y else 0
    let Bfun : Fin r → (Fin k → F) → F := fun b y =>
      Y.β b y + Y.bc b + ∑ c : Fin r, if c.val < b.val then Y.bp b c * Y.q c y else 0
    have hAB_aff : ∀ b : Fin r, isAff (Afun b) ∧ isAff (Bfun b) := by
      intro b
      have hB : diffF (Y.q b) (eΦ b 1) = Bfun b := by
        funext y
        rw [diffF_eq_add, Y.hq b (y + eΦ b 1), Y.hq b y]
        have hvan1 : ∀ c : Fin r, c.val < b.val → Y.α c (eΦ b 1) = 0 ∧ Y.β c (eΦ b 1) = 0 := by
          intro c hc
          have hne : c ≠ b := fun h => by subst h; omega
          exact ⟨by simp [hα_e, hne], by simp [hβ_e]⟩
        have hA1 : Afun b (y + eΦ b 1) = Afun b y + 1 := by
          dsimp only [Afun]
          have hαb : Y.α b (eΦ b 1) = 1 := by simp [hα_e]
          rw [map_add, hαb]
          have hsum : (∑ c : Fin r, if c.val < b.val then Y.ap b c * Y.q c (y + eΦ b 1) else 0) =
              ∑ c : Fin r, if c.val < b.val then Y.ap b c * Y.q c y else 0 := by
            refine Finset.sum_congr rfl fun c _ => ?_
            split_ifs with hc
            · rw [hq_inv (eΦ b 1) c (fun d hd => hvan1 d (by omega)) y]
            · rfl
          rw [hsum]; ring
        have hB1 : Bfun b (y + eΦ b 1) = Bfun b y := by
          dsimp only [Bfun]
          have hβb : Y.β b (eΦ b 1) = 0 := by simp [hβ_e]
          rw [map_add, hβb, add_zero]
          have hsum : (∑ c : Fin r, if c.val < b.val then Y.bp b c * Y.q c (y + eΦ b 1) else 0) =
              ∑ c : Fin r, if c.val < b.val then Y.bp b c * Y.q c y else 0 := by
            refine Finset.sum_congr rfl fun c _ => ?_
            split_ifs with hc
            · rw [hq_inv (eΦ b 1) c (fun d hd => hvan1 d (by omega)) y]
            · rfl
          rw [hsum]
        change Afun b (y + eΦ b 1) * Bfun b (y + eΦ b 1) + Afun b y * Bfun b y = Bfun b y
        rw [hA1, hB1]; ring_nf; simp [show (2 : F) = 0 by decide]
      have hA : diffF (Y.q b) (eΦ b 2) = Afun b := by
        funext y
        rw [diffF_eq_add, Y.hq b (y + eΦ b 2), Y.hq b y]
        have hvan2 : ∀ c : Fin r, c.val < b.val → Y.α c (eΦ b 2) = 0 ∧ Y.β c (eΦ b 2) = 0 := by
          intro c hc
          have hne : c ≠ b := fun h => by subst h; omega
          exact ⟨by simp [hα_e], by simp [hβ_e, hne]⟩
        have hA2 : Afun b (y + eΦ b 2) = Afun b y := by
          dsimp only [Afun]
          have hαb : Y.α b (eΦ b 2) = 0 := by simp [hα_e]
          rw [map_add, hαb, add_zero]
          have hsum : (∑ c : Fin r, if c.val < b.val then Y.ap b c * Y.q c (y + eΦ b 2) else 0) =
              ∑ c : Fin r, if c.val < b.val then Y.ap b c * Y.q c y else 0 := by
            refine Finset.sum_congr rfl fun c _ => ?_
            split_ifs with hc
            · rw [hq_inv (eΦ b 2) c (fun d hd => hvan2 d (by omega)) y]
            · rfl
          rw [hsum]
        have hB2 : Bfun b (y + eΦ b 2) = Bfun b y + 1 := by
          dsimp only [Bfun]
          have hβb : Y.β b (eΦ b 2) = 1 := by simp [hβ_e]
          rw [map_add, hβb]
          have hsum : (∑ c : Fin r, if c.val < b.val then Y.bp b c * Y.q c (y + eΦ b 2) else 0) =
              ∑ c : Fin r, if c.val < b.val then Y.bp b c * Y.q c y else 0 := by
            refine Finset.sum_congr rfl fun c _ => ?_
            split_ifs with hc
            · rw [hq_inv (eΦ b 2) c (fun d hd => hvan2 d (by omega)) y]
            · rfl
          rw [hsum]; ring
        change Afun b (y + eΦ b 2) * Bfun b (y + eΦ b 2) + Afun b y * Bfun b y = Afun b y
        rw [hA2, hB2]; ring_nf; simp [show (2 : F) = 0 by decide]
      exact ⟨fun u v x => by rw [← hA]; exact hq_quad b (eΦ b 2) u v x,
             fun u v x => by rw [← hB]; exact hq_quad b (eΦ b 1) u v x⟩
    -- Step 3: Deduce ap b c = 0 and bp b c = 0 for all c < b!
    have hcoeff_zero : ∀ b : Fin r, (∀ c : Fin r, c.val < b.val → Y.ap b c = 0 ∧ Y.bp b c = 0) := by
      have hq_diag : ∀ c : Fin r, diffF (diffF (Y.q c) (eΦ c 1)) (eΦ c 2) 0 = 1 := by
        intro c
        have hvan : ∀ d : Fin r, d.val < c.val →
            (Y.α d (eΦ c 1) = 0 ∧ Y.β d (eΦ c 1) = 0) ∧
            (Y.α d (eΦ c 2) = 0 ∧ Y.β d (eΦ c 2) = 0) := by
          intro d hd
          have hne : d ≠ c := fun h => by subst h; omega
          exact ⟨⟨by simp [hα_e, hne], by simp [hβ_e]⟩,
                 ⟨by simp [hα_e], by simp [hβ_e, hne]⟩⟩
        have hB1 : diffF (Y.q c) (eΦ c 1) = Bfun c := by
          funext y
          rw [diffF_eq_add, Y.hq c (y + eΦ c 1), Y.hq c y]
          have hA1 : Afun c (y + eΦ c 1) = Afun c y + 1 := by
            dsimp only [Afun]; rw [map_add, show Y.α c (eΦ c 1) = 1 by simp [hα_e]]
            have hsum : (∑ d : Fin r, if d.val < c.val then Y.ap c d * Y.q d (y + eΦ c 1) else 0) =
                ∑ d : Fin r, if d.val < c.val then Y.ap c d * Y.q d y else 0 := by
              refine Finset.sum_congr rfl fun d _ => ?_
              split_ifs with hd
              · rw [hq_inv (eΦ c 1) d (fun d' hd' => (hvan d' (by omega)).1) y]
              · rfl
            rw [hsum]; ring
          have hB1' : Bfun c (y + eΦ c 1) = Bfun c y := by
            dsimp only [Bfun]; rw [map_add, show Y.β c (eΦ c 1) = 0 by simp [hβ_e], add_zero]
            have hsum : (∑ d : Fin r, if d.val < c.val then Y.bp c d * Y.q d (y + eΦ c 1) else 0) =
                ∑ d : Fin r, if d.val < c.val then Y.bp c d * Y.q d y else 0 := by
              refine Finset.sum_congr rfl fun d _ => ?_
              split_ifs with hd
              · rw [hq_inv (eΦ c 1) d (fun d' hd' => (hvan d' (by omega)).1) y]
              · rfl
            rw [hsum]
          change Afun c (y + eΦ c 1) * Bfun c (y + eΦ c 1) + Afun c y * Bfun c y = Bfun c y
          rw [hA1, hB1']; ring_nf; simp [show (2 : F) = 0 by decide]
        rw [hB1, diffF_eq_add, zero_add]
        dsimp only [Bfun]
        rw [show Y.β c (eΦ c 2) = 1 by simp [hβ_e], map_zero]
        have hsum : (∑ d : Fin r, if d.val < c.val then Y.bp c d * Y.q d (eΦ c 2) else 0) =
            ∑ d : Fin r, if d.val < c.val then Y.bp c d * Y.q d 0 else 0 := by
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs with hd
          · have hinv := hq_inv (eΦ c 2) d (fun d' hd' => (hvan d' (by omega)).2) 0
            rw [zero_add] at hinv
            rw [hinv]
          · rfl
        rw [hsum]; ring_nf; simp [show (2 : F) = 0 by decide]
      have haux : ∀ (b : Fin r) (coeff : Fin r → F) (lin : (Fin k → F) →ₗ[F] F) (c0 : F),
          isAff (fun y => lin y + c0 + ∑ c : Fin r, if c.val < b.val then coeff c * Y.q c y else 0) →
          ∀ c : Fin r, c.val < b.val → coeff c = 0 := by
        intro b coeff lin c0 haff
        -- Downward induction on c.val from b.val - 1 down to 0
        suffices h : ∀ d : ℕ, ∀ c : Fin r, c.val < b.val → b.val - c.val ≤ d → coeff c = 0 from
          fun c hc => h (b.val - c.val) c hc le_rfl
        intro d
        induction d with
        | zero => intro c hc hle; omega
        | succ d ih =>
          intro c hc hle
          have hhi : ∀ c' : Fin r, c.val < c'.val → c'.val < b.val → coeff c' = 0 :=
            fun c' h1 h2 => ih c' h2 (by omega)
          have h0 := haff (eΦ c 1) (eΦ c 2) 0
          have hlin_zero : diffF (diffF (fun y => lin y + c0) (eΦ c 1)) (eΦ c 2) 0 = 0 := by
            have h1 : diffF (fun y => lin y + c0) (eΦ c 1) = fun _ => lin (eΦ c 1) := by
              funext y; simp [diffF_eq_add, map_add]; ring_nf; simp [show (2 : F) = 0 by decide]
            rw [h1, diffF_const]
          have hsplit : diffF (diffF (fun y => lin y + c0 +
                ∑ c' : Fin r, if c'.val < b.val then coeff c' * Y.q c' y else 0) (eΦ c 1)) (eΦ c 2) 0 =
              diffF (diffF (fun y => lin y + c0) (eΦ c 1)) (eΦ c 2) 0 +
              ∑ c' : Fin r, diffF (diffF (fun y => if c'.val < b.val then coeff c' * Y.q c' y else 0)
                (eΦ c 1)) (eΦ c 2) 0 := by
            have ha1 : diffF (fun y => lin y + c0 +
                  ∑ c' : Fin r, if c'.val < b.val then coeff c' * Y.q c' y else 0) (eΦ c 1) =
                fun y => diffF (fun y => lin y + c0) (eΦ c 1) y +
                  ∑ c' : Fin r, diffF (fun y => if c'.val < b.val then coeff c' * Y.q c' y else 0)
                    (eΦ c 1) y := by
              funext y; rw [diffF_add_fun, diffF_sum_fun]
            rw [ha1, diffF_add_fun, diffF_sum_fun]
          rw [hsplit, hlin_zero, zero_add] at h0
          rw [Finset.sum_eq_single c] at h0
          · simp only [hc, ↓reduceIte] at h0
            have hsmul : diffF (diffF (fun y => coeff c * Y.q c y) (eΦ c 1)) (eΦ c 2) 0 =
                coeff c * diffF (diffF (Y.q c) (eΦ c 1)) (eΦ c 2) 0 := by
              have h1 : diffF (fun y => coeff c * Y.q c y) (eΦ c 1) =
                  fun y => coeff c * diffF (Y.q c) (eΦ c 1) y := funext (diffF_smul_fun _ _ _)
              rw [h1, diffF_smul_fun]
            rw [hsmul, hq_diag c, mul_one] at h0
            exact h0
          · intro c' _ hc'ne
            by_cases hlt_b : c'.val < b.val
            · simp only [hlt_b, ↓reduceIte]
              by_cases hgt : c.val < c'.val
              · simp [hhi c' hgt hlt_b, diffF]
              · have hlt_c : c'.val < c.val := by omega
                have hvan1 : ∀ d : Fin r, d.val ≤ c'.val → Y.α d (eΦ c 1) = 0 ∧ Y.β d (eΦ c 1) = 0 := by
                  intro d hd
                  have hne : d ≠ c := fun h => by subst h; omega
                  exact ⟨by simp [hα_e, hne], by simp [hβ_e]⟩
                have hinv1 : diffF (fun y => coeff c' * Y.q c' y) (eΦ c 1) = fun _ => 0 := by
                  funext y; rw [diffF_eq_add, hq_inv (eΦ c 1) c' hvan1 y, f_add_self]
                rw [hinv1, diffF_const]
            · simp [hlt_b, diffF]
          · intro hm; exact absurd (Finset.mem_univ c) hm
      intro b c hc
      exact ⟨haux b (Y.ap b) (Y.α b) (Y.ac b) (hAB_aff b).1 c hc,
             haux b (Y.bp b) (Y.β b) (Y.bc b) (hAB_aff b).2 c hc⟩
    -- Step 4: Now target y = Q' y + ∑ b, ℓ b y * α b y * β b y, so thirdF target = ∑ b, std3 (Φ _ b)
    have hthird_Φ : ∀ u v w : Fin k → F,
        thirdF target u v w = ∑ b : Fin r, std3 (Φ u b) (Φ v b) (Φ w b) := by
      intro u v w
      have hq_simple : ∀ b y, Y.q b y = (Y.α b y + Y.ac b) * (Y.β b y + Y.bc b) := by
        intro b y
        rw [Y.hq b y]
        have h1 : (∑ c : Fin r, if c.val < b.val then Y.ap b c * Y.q c y else 0) = 0 :=
          Finset.sum_eq_zero fun c _ => by
            split_ifs with hc
            · simp [(hcoeff_zero b c hc).1]
            · rfl
        have h2 : (∑ c : Fin r, if c.val < b.val then Y.bp b c * Y.q c y else 0) = 0 :=
          Finset.sum_eq_zero fun c _ => by
            split_ifs with hc
            · simp [(hcoeff_zero b c hc).2]
            · rfl
        rw [h1, h2, add_zero, add_zero]
      have hterm_third : ∀ b : Fin r,
          thirdF (fun y => (Y.ℓ b y + Y.lc b) * Y.q b y) u v w = std3 (Φ u b) (Φ v b) (Φ w b) := by
        intro b
        have hexp : (fun y => (Y.ℓ b y + Y.lc b) * Y.q b y) = fun y =>
            Y.ℓ b y * Y.α b y * Y.β b y +
            (Y.bc b * (Y.ℓ b y * Y.α b y) + Y.ac b * (Y.ℓ b y * Y.β b y) +
             Y.lc b * (Y.α b y * Y.β b y) +
             (Y.ac b * Y.bc b) * Y.ℓ b y + (Y.lc b * Y.bc b) * Y.α b y +
             (Y.lc b * Y.ac b) * Y.β b y + Y.lc b * Y.ac b * Y.bc b) := by
          funext y; rw [hq_simple b y]; ring
        rw [hexp, thirdF_add_fun, thirdF_mul3]
        have hrem_quad : isQuad (fun y =>
            Y.bc b * (Y.ℓ b y * Y.α b y) + Y.ac b * (Y.ℓ b y * Y.β b y) +
            Y.lc b * (Y.α b y * Y.β b y) +
            (Y.ac b * Y.bc b) * Y.ℓ b y + (Y.lc b * Y.bc b) * Y.α b y +
            (Y.lc b * Y.ac b) * Y.β b y + Y.lc b * Y.ac b * Y.bc b) := by
          have hq_smul : ∀ (c : F) (f : (Fin k → F) → F), isQuad f → isQuad (fun y => c * f y) := by
            intro c f hf a1 a2 a3 x
            have h1 : diffF (fun y => c * f y) a1 = fun y => c * diffF f a1 y := funext (diffF_smul_fun _ _ _)
            rw [h1]
            have h2 : diffF (fun y => c * diffF f a1 y) a2 = fun y => c * diffF (diffF f a1) a2 y :=
              funext (diffF_smul_fun _ _ _)
            rw [h2, diffF_smul_fun, hf a1 a2 a3 x, mul_zero]
          have hlin_q : ∀ (c : F) (L : (Fin k → F) →ₗ[F] F), isQuad (fun y => c * L y) := fun c L =>
            hq_smul c L (isAff_isQuad (fun a1 a2 x => by
              have h1 : diffF L a1 = fun _ => L a1 := funext fun y => by
                simp [diffF_eq_add, map_add]; ring_nf; simp [show (2 : F) = 0 by decide]
              rw [h1, diffF_const]))
          exact isQuad_add (isQuad_add (isQuad_add (isQuad_add (isQuad_add (isQuad_add
            (hq_smul _ _ (isQuad_mul_lin (Y.ℓ b) (Y.α b)))
            (hq_smul _ _ (isQuad_mul_lin (Y.ℓ b) (Y.β b))))
            (hq_smul _ _ (isQuad_mul_lin (Y.α b) (Y.β b))))
            (hlin_q _ (Y.ℓ b))) (hlin_q _ (Y.α b))) (hlin_q _ (Y.β b)))
            (fun a1 a2 a3 x => by simp [diffF])
        rw [show thirdF _ u v w = 0 from hrem_quad u v w 0, add_zero]
        simp only [wedge3, std3, Φ, LinearMap.coe_mk, AddHom.coe_mk]
        ring
      have hfun : target = fun y => Q y + ∑ b : Fin r, (Y.ℓ b y + Y.lc b) * Y.q b y :=
        funext htarget_eq
      rw [hfun, thirdF_add_fun, show thirdF Q u v w = 0 from hQ u v w 0, zero_add]
      have hsum3 : ∀ (s : Finset (Fin r)) (f : Fin r → (Fin k → F) → F),
          thirdF (fun y => ∑ j ∈ s, f j y) u v w = ∑ j ∈ s, thirdF (f j) u v w := by
        intro s f; classical
        induction s using Finset.induction with
        | empty => simp [thirdF, diffF]
        | @insert j s hj ih =>
          have : (fun y => ∑ i ∈ insert j s, f i y) = fun y => f j y + ∑ i ∈ s, f i y := by
            funext y; exact Finset.sum_insert hj
          rw [this, thirdF_add_fun, ih, Finset.sum_insert hj]
      rw [hsum3]
      exact Finset.sum_congr rfl fun b _ => hterm_third b
    -- Step 5: Every 3-dim block B_b in (Fin r → Fin 3 → F) lies wholly in ImV or wholly in ImP!
    let injV : (Fin n → F) →ₗ[F] (Fin k → F) :=
      { toFun := fun v idx => match e.symm idx with | Sum.inl i => v i | Sum.inr _ => 0
        map_add' := fun _ _ => by funext idx; simp only [Pi.add_apply]; cases e.symm idx <;> simp
        map_smul' := fun _ _ => by funext idx; simp only [Pi.smul_apply, RingHom.id_apply]; cases e.symm idx <;> simp }
    let injP : (Fin m → Fin 3 → F) →ₗ[F] (Fin k → F) :=
      { toFun := fun p idx => match e.symm idx with | Sum.inl _ => 0 | Sum.inr (j, t) => p j t
        map_add' := fun _ _ => by funext idx; simp only [Pi.add_apply]; cases e.symm idx <;> simp
        map_smul' := fun _ _ => by funext idx; simp only [Pi.smul_apply, RingHom.id_apply]; cases e.symm idx <;> simp }
    let ImV : Submodule F (Fin r → Fin 3 → F) := LinearMap.range (Φ.comp injV)
    let ImP : Submodule F (Fin r → Fin 3 → F) := LinearMap.range (Φ.comp injP)
    have hdisj_VP : Disjoint ImV ImP := by
      rw [Submodule.disjoint_def]
      rintro y ⟨v, hv⟩ ⟨p, hp⟩
      have hker_vp : injV v + injP p ∈ LinearMap.ker Φ := by
        rw [LinearMap.mem_ker, map_add]
        change (Φ.comp injV) v + (Φ.comp injP) p = 0
        rw [hv, hp]
        funext a t; exact f_add_self _
      rw [hker_eq, hRT_iff] at hker_vp
      have hp0 : p = 0 := by
        funext j t
        have := congrFun (hker_vp.2 j) t
        simpa [injV, injP] using this
      rw [← hp, hp0, map_zero]
    have hImP_rank : Module.finrank F ImP ≤ 3 * m := by
      have h := LinearMap.finrank_range_le (Φ.comp injP)
      simp only [Module.finrank_pi_fintype, Module.finrank_self,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
      dsimp only [ImP]; omega
    -- Every nonzero single-block vector lies in ImV ∪ ImP!
    have hsingle_mem : ∀ (b : Fin r) (c : Fin 3 → F), c ≠ 0 →
        (fun a => if a = b then c else 0) ∈ ImV ∨ (fun a => if a = b then c else 0) ∈ ImP := by
      intro b c hc
      obtain ⟨w, hw⟩ := hsurj (fun a => if a = b then c else 0)
      have hrank2 : bilRank (thirdLin target htarget_cub w) = 2 := by
        rw [bilRank_of_surj_std3 Φ hsurj (thirdLin target htarget_cub w) w (hthird_Φ w)]
        rw [Finset.sum_eq_single b]
        · simp [hw, hc]
        · intro a _ hab; simp [hw, hab]
        · intro hm; exact absurd (Finset.mem_univ b) hm
      rw [bilRank_direct_sum g hg e target htarget_def htarget_cub w] at hrank2
      obtain ⟨rg, hrg⟩ := altBil_even_rank (thirdLin g hg (fun i => w (e (Sum.inl i))))
        (fun x => thirdF_alt_23 g _ x)
      have hP_even : ∃ rp, (∑ j : Fin m, if (fun t : Fin 3 => w (e (Sum.inr (j, t)))) = 0 then 0 else 2) = 2 * rp := by
        refine ⟨(Finset.univ.filter (fun j : Fin m => (fun t : Fin 3 => w (e (Sum.inr (j, t)))) ≠ 0)).card, ?_⟩
        have hrew : (∑ j : Fin m, if (fun t : Fin 3 => w (e (Sum.inr (j, t)))) = 0 then 0 else 2) =
            ∑ j : Fin m, if (fun t : Fin 3 => w (e (Sum.inr (j, t)))) ≠ 0 then 2 else 0 :=
          Finset.sum_congr rfl fun j _ => by by_cases h : (fun t : Fin 3 => w (e (Sum.inr (j, t)))) = 0 <;> simp [h]
        rw [hrew, ← Finset.sum_filter]
        simp [mul_comm]
      rcases hP_even with ⟨rp, hrp⟩
      have hcases : rg = 0 ∨ rp = 0 := by omega
      rcases hcases with rfl | rfl
      · -- rg = 0 ⇒ w_V ∈ R ⇒ injV w_V ∈ RT = ker Φ ⇒ Φ w = Φ (injP w_P) ∈ ImP!
        right
        refine ⟨fun j t => w (e (Sum.inr (j, t))), ?_⟩
        have hdiff_ker : w + injP (fun j t => w (e (Sum.inr (j, t)))) ∈ LinearMap.ker Φ := by
          rw [hker_eq, hRT_iff]
          constructor
          · have hrg0 : Module.finrank F (LinearMap.range (thirdLin g hg (fun i => w (e (Sum.inl i))))) = 0 := by
              change bilRank (thirdLin g hg (fun i => w (e (Sum.inl i)))) = 0; omega
            have hbot : LinearMap.range (thirdLin g hg (fun i => w (e (Sum.inl i)))) = ⊥ :=
              Submodule.finrank_eq_zero.mp hrg0
            rw [hR]; intro u1 u2
            have hmem : thirdLin g hg (fun i => w (e (Sum.inl i))) u1 ∈
                LinearMap.range (thirdLin g hg (fun i => w (e (Sum.inl i)))) := ⟨u1, rfl⟩
            rw [hbot, Submodule.mem_bot] at hmem
            have heq : (fun i => (w + injP (fun j t => w (e (Sum.inr (j, t))))) (e (Sum.inl i))) =
                (fun i => w (e (Sum.inl i))) := by funext i; simp [injP]
            rw [heq]; exact congrArg (fun f => f u2) hmem
          · intro j; funext t; simp [injP, f_add_self]
        rw [LinearMap.mem_ker, map_add] at hdiff_ker
        have h2 := congrArg (· + Φ (injP (fun j t => w (e (Sum.inr (j, t)))))) hdiff_ker
        have hadd0 : Φ (injP (fun j t => w (e (Sum.inr (j, t))))) +
            Φ (injP (fun j t => w (e (Sum.inr (j, t))))) = 0 := by funext a t; exact f_add_self _
        rw [add_assoc, hadd0, add_zero, zero_add] at h2
        simpa [← h2] using hw
      · -- rp = 0 ⇒ w_P = 0 ⇒ w = injV w_V ⇒ Φ w ∈ ImV!
        left
        refine ⟨fun i => w (e (Sum.inl i)), ?_⟩
        have hwP0 : ∀ j : Fin m, (fun t : Fin 3 => w (e (Sum.inr (j, t)))) = 0 := by
          intro j
          have hsum0 : (∑ j' : Fin m, if (fun t : Fin 3 => w (e (Sum.inr (j', t)))) = 0 then 0 else 2) = 0 := by
            omega
          have hj := Finset.sum_eq_zero_iff.mp hsum0 j (Finset.mem_univ j)
          by_cases hz : (fun t : Fin 3 => w (e (Sum.inr (j, t)))) = 0
          · exact hz
          · simp [hz] at hj
        have hweq : injV (fun i => w (e (Sum.inl i))) = w := by
          funext idx
          cases h : e.symm idx with
          | inl i =>
            have he : e (Sum.inl i) = idx := by rw [← h, e.apply_symm_apply]
            simp [injV, h, he]
          | inr jt =>
            have he : e (Sum.inr jt) = idx := by rw [← h, e.apply_symm_apply]
            have h0 := congrFun (hwP0 jt.1) jt.2
            simp [injV, h, ← he, h0]
        change Φ (injV (fun i => w (e (Sum.inl i)))) = _
        rw [hweq, hw]
    -- Each block b lies wholly in ImV or wholly in ImP!
    have hblock_split : ∀ b : Fin r,
        (∀ c : Fin 3 → F, (fun a => if a = b then c else 0) ∈ ImV) ∨
        (∀ c : Fin 3 → F, (fun a => if a = b then c else 0) ∈ ImP) := by
      intro b
      have h0_ne : unitF (0 : Fin 3) ≠ 0 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by simpa [unitF] using congrFun h 0)
      rcases hsingle_mem b (unitF 0) h0_ne with h0V | h0P
      · left
        intro c
        by_cases hc0 : c = 0
        · subst hc0; convert ImV.zero_mem; funext a; simp
        rcases hsingle_mem b c hc0 with hcV | hcP
        · exact hcV
        · exfalso
          have hsum_ne : unitF (0 : Fin 3) + c ≠ 0 := by
            intro hsum
            have heq : (fun a => if a = b then unitF (0 : Fin 3) else 0) =
                (fun a => if a = b then c else 0) := by
              funext a; split_ifs with hab
              · have h1 := congrArg (· + c) hsum
                rw [add_assoc, vec_add_self, add_zero, zero_add] at h1; exact h1
              · rfl
            rw [heq] at h0V
            have hbot := Submodule.disjoint_def.mp hdisj_VP _ h0V hcP
            exact hc0 (by simpa using congrFun hbot b)
          have hsum_eq : (fun a => if a = b then unitF (0 : Fin 3) + c else 0) =
              (fun a => if a = b then unitF (0 : Fin 3) else 0) +
              (fun a => if a = b then c else 0) := by
            funext a; by_cases hab : a = b <;> simp [hab]
          rcases hsingle_mem b (unitF 0 + c) hsum_ne with hsV | hsP
          · rw [hsum_eq] at hsV
            have hcV' : (fun a => if a = b then c else 0) ∈ ImV := by
              have h := ImV.add_mem hsV h0V
              have heq : ((fun a => if a = b then unitF (0 : Fin 3) else 0) +
                  (fun a => if a = b then c else 0)) +
                  (fun a => if a = b then unitF (0 : Fin 3) else 0) =
                  (fun a => if a = b then c else 0) := by
                funext a t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
              rwa [heq] at h
            have hbot := Submodule.disjoint_def.mp hdisj_VP _ hcV' hcP
            exact hc0 (by simpa using congrFun hbot b)
          · rw [hsum_eq] at hsP
            have h0P' : (fun a => if a = b then unitF (0 : Fin 3) else 0) ∈ ImP := by
              have h := ImP.add_mem hsP hcP
              have heq : ((fun a => if a = b then unitF (0 : Fin 3) else 0) +
                  (fun a => if a = b then c else 0)) +
                  (fun a => if a = b then c else 0) =
                  (fun a => if a = b then unitF (0 : Fin 3) else 0) := by
                funext a t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
              rwa [heq] at h
            have hbot := Submodule.disjoint_def.mp hdisj_VP _ h0V h0P'
            exact h0_ne (by simpa using congrFun hbot b)
      · right
        intro c
        by_cases hc0 : c = 0
        · subst hc0; convert ImP.zero_mem; funext a; simp
        rcases hsingle_mem b c hc0 with hcV | hcP
        · exfalso
          have hsum_ne : unitF (0 : Fin 3) + c ≠ 0 := by
            intro hsum
            have heq : (fun a => if a = b then unitF (0 : Fin 3) else 0) =
                (fun a => if a = b then c else 0) := by
              funext a; split_ifs with hab
              · have h1 := congrArg (· + c) hsum
                rw [add_assoc, vec_add_self, add_zero, zero_add] at h1; exact h1
              · rfl
            rw [heq] at h0P
            have hbot := Submodule.disjoint_def.mp hdisj_VP _ hcV h0P
            exact hc0 (by simpa using congrFun hbot b)
          have hsum_eq : (fun a => if a = b then unitF (0 : Fin 3) + c else 0) =
              (fun a => if a = b then unitF (0 : Fin 3) else 0) +
              (fun a => if a = b then c else 0) := by
            funext a; by_cases hab : a = b <;> simp [hab]
          rcases hsingle_mem b (unitF 0 + c) hsum_ne with hsV | hsP
          · rw [hsum_eq] at hsV
            have h0V' : (fun a => if a = b then unitF (0 : Fin 3) else 0) ∈ ImV := by
              have h := ImV.add_mem hsV hcV
              have heq : ((fun a => if a = b then unitF (0 : Fin 3) else 0) +
                  (fun a => if a = b then c else 0)) +
                  (fun a => if a = b then c else 0) =
                  (fun a => if a = b then unitF (0 : Fin 3) else 0) := by
                funext a t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
              rwa [heq] at h
            have hbot := Submodule.disjoint_def.mp hdisj_VP _ h0V' h0P
            exact h0_ne (by simpa using congrFun hbot b)
          · rw [hsum_eq] at hsP
            have hcP' : (fun a => if a = b then c else 0) ∈ ImP := by
              have h := ImP.add_mem hsP h0P
              have heq : ((fun a => if a = b then unitF (0 : Fin 3) else 0) +
                  (fun a => if a = b then c else 0)) +
                  (fun a => if a = b then unitF (0 : Fin 3) else 0) =
                  (fun a => if a = b then c else 0) := by
                funext a t; simp only [Pi.add_apply]; ring_nf; simp [show (2 : F) = 0 by decide]
              rwa [heq] at h
            have hbot := Submodule.disjoint_def.mp hdisj_VP _ hcV hcP'
            exact hc0 (by simpa using congrFun hbot b)
        · exact hcP
    -- Count blocks in ImP: at most m! So at least 2 distinct blocks lie in ImV!
    classical
    let SP : Finset (Fin r) := Finset.univ.filter (fun b => ∀ c : Fin 3 → F, (fun a => if a = b then c else 0) ∈ ImP)
    let SV : Finset (Fin r) := Finset.univ.filter (fun b => ∀ c : Fin 3 → F, (fun a => if a = b then c else 0) ∈ ImV)
    have hSP_card : SP.card ≤ m := by
      let embP : (SP → Fin 3 → F) →ₗ[F] ImP :=
        { toFun := fun f =>
            ⟨fun a => if h : a ∈ SP then f ⟨a, h⟩ else 0, by
              have heq : (fun a => if h : a ∈ SP then f ⟨a, h⟩ else 0) =
                  ∑ b ∈ SP.attach, (fun a => if a = b.1 then f b else 0) := by
                funext a
                by_cases ha : a ∈ SP
                · simp only [ha, ↓reduceDIte, Finset.sum_apply]
                  rw [Finset.sum_eq_single ⟨a, ha⟩]
                  · simp
                  · intro b _ hne
                    have : a ≠ b.1 := fun h => hne (Subtype.ext h.symm)
                    simp [this]
                  · intro hm; exact absurd (Finset.mem_attach _ _) hm
                · simp only [ha, ↓reduceDIte, Finset.sum_apply]
                  symm
                  refine Finset.sum_eq_zero fun b _ => ?_
                  have : a ≠ b.1 := fun h => ha (h ▸ b.2)
                  simp [this]
              rw [heq]
              exact ImP.sum_mem fun b _ => (Finset.mem_filter.mp b.2).2 (f b)⟩
          map_add' := fun f1 f2 => by
            apply Subtype.ext; funext a; simp only [Submodule.coe_add, Pi.add_apply]; split_ifs <;> simp
          map_smul' := fun s f => by
            apply Subtype.ext; funext a; simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
      have hemb_inj : Function.Injective embP := by
        rw [injective_iff_map_eq_zero]
        intro f hf
        funext ⟨b, hb⟩
        have h := congrFun (congrArg Subtype.val hf) b
        simpa [embP, hb] using h
      have hfr := LinearMap.finrank_le_finrank_of_injective hemb_inj
      simp only [Module.finrank_pi_fintype, Module.finrank_self,
        Finset.sum_const, Finset.card_univ, Fintype.card_coe, Fintype.card_fin, smul_eq_mul, mul_one] at hfr
      omega
    have hSV_card : 2 ≤ SV.card := by
      have hunion : SP ∪ SV = Finset.univ := by
        ext b
        simp only [SP, SV, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact (hblock_split b).symm
      have hle := Finset.card_union_le SP SV
      rw [hunion, Finset.card_univ, Fintype.card_fin] at hle
      omega
    obtain ⟨b1, hb1, b2, hb2, hb12⟩ := Finset.one_lt_card.mp (by omega : 1 < SV.card)
    have h1V : (fun a => if a = b1 then unitF (0 : Fin 3) else 0) ∈ ImV :=
      (Finset.mem_filter.mp hb1).2 (unitF 0)
    have h2V : (fun a => if a = b2 then unitF (0 : Fin 3) else 0) ∈ ImV :=
      (Finset.mem_filter.mp hb2).2 (unitF 0)
    rcases h1V with ⟨u, hu⟩
    rcases h2V with ⟨v, hv⟩
    have hrank_injV : ∀ x : Fin n → F,
        bilRank (thirdLin g hg x) = ∑ a : Fin r, if Φ (injV x) a = 0 then 0 else 2 := by
      intro x
      have h1 := bilRank_direct_sum g hg e target htarget_def htarget_cub (injV x)
      have h2 := bilRank_of_surj_std3 Φ hsurj (thirdLin target htarget_cub (injV x)) (injV x)
        (hthird_Φ (injV x))
      have hprojV : (fun i => injV x (e (Sum.inl i))) = x := by funext i; simp [injV]
      have hprojP : ∀ j : Fin m, (fun t : Fin 3 => injV x (e (Sum.inr (j, t)))) = 0 := by
        intro j; funext t; simp [injV]
      rw [hprojV] at h1
      simp only [hprojP, ↓reduceIte, Finset.sum_const_zero, add_zero] at h1
      rw [← h1, h2]
    have h0_ne : unitF (0 : Fin 3) ≠ 0 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by simpa [unitF] using congrFun h 0)
    refine ⟨u, v, ?_, ?_, ?_⟩
    · rw [hrank_injV u]
      change (∑ a : Fin r, if (Φ.comp injV) u a = 0 then 0 else 2) = 2
      rw [hu, Finset.sum_eq_single b1]
      · simp [h0_ne]
      · intro a _ hab; simp [hab]
      · intro hm; exact absurd (Finset.mem_univ b1) hm
    · rw [hrank_injV v]
      change (∑ a : Fin r, if (Φ.comp injV) v a = 0 then 0 else 2) = 2
      rw [hv, Finset.sum_eq_single b2]
      · simp [h0_ne]
      · intro a _ hab; simp [hab]
      · intro hm; exact absurd (Finset.mem_univ b2) hm
    · rw [hrank_injV (u + v)]
      change (∑ a : Fin r, if (Φ.comp injV) (u + v) a = 0 then 0 else 2) = 4
      rw [map_add, hu, hv]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b1)]
      have hb2_mem : b2 ∈ Finset.univ.erase b1 := Finset.mem_erase.mpr ⟨Ne.symm hb12, Finset.mem_univ b2⟩
      rw [← Finset.sum_erase_add _ _ hb2_mem]
      have hrest : ∑ a ∈ (Finset.univ.erase b1).erase b2,
          (if ((fun a => if a = b1 then unitF (0 : Fin 3) else 0) +
               (fun a => if a = b2 then unitF (0 : Fin 3) else 0)) a = 0 then 0 else 2) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        have h1 : a ≠ b2 := (Finset.mem_erase.mp ha).1
        have h2 : a ≠ b1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
        simp [h1, h2]
      rw [hrest, zero_add]
      simp [hb12, Ne.symm hb12, h0_ne]

end PEqualNP.Outside.L_meta_30643_aux

open PEqualNP.Outside.L_meta_30643_aux

theorem PEqualNP.Outside.L_meta_30643 :
    ∀ (n m k : ℕ),
      let F := ZMod 2
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let legal := fun (n : ℕ) (C : Circ) =>
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
          (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
            (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
      let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
        ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
      let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
      let V := Fin n → F
      let diff := fun (g : V → F) (a x : V) => g (x+a) - g x
      let third := fun (g : V → F) (a b c : V) => diff (diff (diff g a) b) c 0
      let cubic := fun (g : V → F) => ∀ a b c d x, diff (diff (diff (diff g a) b) c) d x = 0
      let unit := fun (i j : Fin n) => if i = j then (1 : F) else 0
      let rankAt := fun (g : V → F) (u : V) =>
        (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).rank
      ∀ (g : V → F) (R : Submodule F V), cubic g →
        (∀ u : V, u ∈ R ↔ ∀ v w : V, third g u v w = 0) →
        let d := n - Module.finrank F R
        ∀ e : (Fin n ⊕ (Fin m × Fin 3)) ≃ Fin k,
          let target := fun (y : Fin k → F) =>
            g (fun i => y (e (Sum.inl i))) + ∑ j : Fin m,
              y (e (Sum.inr (j,0))) * y (e (Sum.inr (j,1))) * y (e (Sum.inr (j,2)))
          (∃ C : Circ, legal (2*k) C ∧ cost C ≤ k+m+2 ∧ ∀ x y : Fin k → F,
            C.eval (bits k x ++ bits k y) = decide (dotProduct x y + target y = 1)) ↔
            d ≤ 5 ∨ (d = 6 ∧ ∃ u v : V,
              rankAt g u = 2 ∧ rankAt g v = 2 ∧ rankAt g (u+v) = 4) := by
  intro n m k F0 Circ legal cost bits V diff third cubic unit rankAt g R hg hR d e target
  have hrank_eq : ∀ u : Fin n → F, rankAt g u = bilRank (thirdLin g hg u) := fun u =>
    matrix_rank_eq_bilRank (thirdLin g hg u) (fun a b => thirdF_symm_23 g u a b)
  constructor
  · rintro ⟨C, hleg, hcost, heval⟩
    obtain ⟨S, hS⟩ := circuit_to_slp (k := k) C.gates hleg.2
    have htarget_aff : isAffRep S (fun x y => dotProduct x y + target y) := by
      have hEq : (fun x y => dotProduct x y + target y) =
          (fun x y => ofBool (((PEqualNP.CircuitLowerBounds.Circuit.mk C.gates 0).wires (bitsVec k x ++ bitsVec k y)).getD C.output false)) := by
        funext x y
        change dotProduct x y + target y = ofBool (C.eval (bits k x ++ bits k y))
        rw [heval x y, ofBool_decide_eq_one]
      rw [hEq]
      exact hS C.output
    obtain ⟨r, hkr, Y, Q, hQ, htarget_eq⟩ := slp_elim_x S target htarget_aff
    have hr_le : r ≤ m + 2 := by
      have hc : costCirc ⟨C.gates, 0⟩ ≤ k + m + 2 := hcost
      omega
    have hres := yslp_dim_and_dichotomy g R hg hR e target (fun _ => rfl) hr_le Y Q hQ htarget_eq
    rcases hres with h5 | ⟨h6, u, v, hu, hv, huv⟩
    · exact Or.inl h5
    · exact Or.inr ⟨h6, u, v, by rw [hrank_eq]; exact hu, by rw [hrank_eq]; exact hv,
        by rw [hrank_eq]; exact huv⟩
  · intro hcond
    have htwo : ∃ α₁ β₁ γ₁ α₂ β₂ γ₂ : (Fin n → F) →ₗ[F] F,
        ∀ a b c, thirdF g a b c = wedge3 α₁ β₁ γ₁ a b c + wedge3 α₂ β₂ γ₂ a b c := by
      rcases hcond with h5 | ⟨h6, u, v, hu, hv, huv⟩
      · exact exists_two_wedge3_of_le_five g R hg hR h5
      · exact exists_two_wedge3_of_eq_six g R hg hR h6 u v
          (by rw [← hrank_eq]; exact hu) (by rw [← hrank_eq]; exact hv)
          (by rw [← hrank_eq]; exact huv)
    rcases htwo with ⟨α₁, β₁, γ₁, α₂, β₂, γ₂, htwo⟩
    -- Lift the 2 + m triples to Fin (m + 2) → (Fin k → F) →ₗ[F] F
    let projV : (Fin k → F) →ₗ[F] (Fin n → F) :=
      { toFun := fun y i => y (e (Sum.inl i))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let α : Fin (m + 2) → (Fin k → F) →ₗ[F] F := fun idx =>
      if h0 : idx.val = 0 then α₁.comp projV
      else if h1 : idx.val = 1 then α₂.comp projV
      else LinearMap.proj (e (Sum.inr (⟨idx.val - 2, by omega⟩, 0)))
    let β : Fin (m + 2) → (Fin k → F) →ₗ[F] F := fun idx =>
      if h0 : idx.val = 0 then β₁.comp projV
      else if h1 : idx.val = 1 then β₂.comp projV
      else LinearMap.proj (e (Sum.inr (⟨idx.val - 2, by omega⟩, 1)))
    let γ : Fin (m + 2) → (Fin k → F) →ₗ[F] F := fun idx =>
      if h0 : idx.val = 0 then γ₁.comp projV
      else if h1 : idx.val = 1 then γ₂.comp projV
      else LinearMap.proj (e (Sum.inr (⟨idx.val - 2, by omega⟩, 2)))
    -- Show q(y) = g(y_V) + α₁(y_V) β₁(y_V) γ₁(y_V) + α₂(y_V) β₂(y_V) γ₂(y_V) is quadratic
    have hq_quad : isQuad (fun y : Fin k → F =>
        g (projV y) + (α₁ (projV y) * β₁ (projV y) * γ₁ (projV y) +
          α₂ (projV y) * β₂ (projV y) * γ₂ (projV y))) := by
      have hgV : isCubic (fun y : Fin k → F => g (projV y)) := fun a b c d x => by
        simpa [diffF] using hg (projV a) (projV b) (projV c) (projV d) (projV x)
      have h2V : isCubic (fun y : Fin k → F =>
          α₁ (projV y) * β₁ (projV y) * γ₁ (projV y) +
          α₂ (projV y) * β₂ (projV y) * γ₂ (projV y)) :=
        isCubic_add (isCubic_mul3 (α₁.comp projV) (β₁.comp projV) (γ₁.comp projV))
          (isCubic_mul3 (α₂.comp projV) (β₂.comp projV) (γ₂.comp projV))
      refine isQuad_of_thirdF_eq hgV h2V fun a b c => ?_
      have hlhs : thirdF (fun y => g (projV y)) a b c = thirdF g (projV a) (projV b) (projV c) := by
        unfold thirdF diffF; simp
      rw [hlhs, htwo (projV a) (projV b) (projV c)]
      change wedge3 α₁ β₁ γ₁ (projV a) (projV b) (projV c) +
          wedge3 α₂ β₂ γ₂ (projV a) (projV b) (projV c) =
        thirdF (fun y => (α₁.comp projV) y * (β₁.comp projV) y * (γ₁.comp projV) y +
          (α₂.comp projV) y * (β₂.comp projV) y * (γ₂.comp projV) y) a b c
      rw [thirdF_add_fun,
        thirdF_mul3 (α₁.comp projV) (β₁.comp projV) (γ₁.comp projV),
        thirdF_mul3 (α₂.comp projV) (β₂.comp projV) (γ₂.comp projV)]
      rfl
    obtain ⟨c0, l, Q, hQ⟩ := isQuad_repr hq_quad
    obtain ⟨C, hleg, hcost, heval⟩ := build_circuit_of_cubics c0 l Q α β γ
    refine ⟨C, hleg, by change costCirc C ≤ k + m + 2; omega, fun x y => ?_⟩
    change C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + target y = 1)
    rw [heval x y]
    apply congrArg (fun z : F => decide (dotProduct x y + z = 1))
    have hsum_m2 : (∑ a : Fin (m + 2), α a y * β a y * γ a y) =
        α₁ (projV y) * β₁ (projV y) * γ₁ (projV y) +
        α₂ (projV y) * β₂ (projV y) * γ₂ (projV y) +
        ∑ j : Fin m, y (e (Sum.inr (j, 0))) * y (e (Sum.inr (j, 1))) * y (e (Sum.inr (j, 2))) := by
      have h0mem : (⟨0, by omega⟩ : Fin (m + 2)) ∈ Finset.univ := Finset.mem_univ _
      rw [← Finset.sum_erase_add _ _ h0mem]
      have h1mem : (⟨1, by omega⟩ : Fin (m + 2)) ∈ Finset.univ.erase ⟨0, by omega⟩ :=
        Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩
      rw [← Finset.sum_erase_add _ _ h1mem]
      have hrest : (∑ a ∈ (Finset.univ.erase ⟨0, by omega⟩).erase ⟨1, by omega⟩,
          α a y * β a y * γ a y) =
          ∑ j : Fin m, y (e (Sum.inr (j, 0))) * y (e (Sum.inr (j, 1))) * y (e (Sum.inr (j, 2))) := by
        refine Finset.sum_bij (fun a ha => (⟨a.val - 2, by
            have h1 : a ≠ ⟨1, by omega⟩ := (Finset.mem_erase.mp ha).1
            have h0 : a ≠ ⟨0, by omega⟩ := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
            have : a.val ≠ 0 := fun h => h0 (Fin.ext h)
            have : a.val ≠ 1 := fun h => h1 (Fin.ext h)
            omega⟩ : Fin m)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a1 ha1 a2 ha2 h
          have h11 : a1.val ≠ 1 := fun h => (Finset.mem_erase.mp ha1).1 (Fin.ext h)
          have h10 : a1.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp ha1).2).1 (Fin.ext h)
          have h21 : a2.val ≠ 1 := fun h => (Finset.mem_erase.mp ha2).1 (Fin.ext h)
          have h20 : a2.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp ha2).2).1 (Fin.ext h)
          have hv := congrArg Fin.val h
          exact Fin.ext (by dsimp only at hv; omega)
        · intro j _
          refine ⟨⟨j.val + 2, by omega⟩, Finset.mem_erase.mpr ⟨by simp [Fin.ext_iff],
            Finset.mem_erase.mpr ⟨by simp [Fin.ext_iff], Finset.mem_univ _⟩⟩, Fin.ext (by simp)⟩
        · intro a ha
          have h1 : a.val ≠ 1 := fun h => (Finset.mem_erase.mp ha).1 (Fin.ext h)
          have h0 : a.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1 (Fin.ext h)
          have h0' : a ≠ 0 := fun h => h0 (by rw [h]; rfl)
          simp [α, β, γ, h0', h1]
      rw [hrest]
      simp only [α, β, γ, ↓reduceDIte, Nat.one_ne_zero, LinearMap.comp_apply]
      ring
    rw [hsum_m2]
    have hqy := hQ y
    have hgt : g (projV y) = (c0 + ∑ i : Fin k, l i * y i +
        ∑ i : Fin k, ∑ j : Fin k, if i < j then Q i j * y i * y j else 0) +
        (α₁ (projV y) * β₁ (projV y) * γ₁ (projV y) +
         α₂ (projV y) * β₂ (projV y) * γ₂ (projV y)) := by
      have h2 := congrArg (· + (α₁ (projV y) * β₁ (projV y) * γ₁ (projV y) +
        α₂ (projV y) * β₂ (projV y) * γ₂ (projV y))) hqy
      rw [add_assoc, f_add_self, add_zero] at h2
      exact h2
    dsimp only [target]
    change _ = g (projV y) + _
    rw [hgt]; ring

