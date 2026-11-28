import Mathlib


namespace PEqualNP.Outside.L_meta_32055_aux.Leaves

noncomputable section
open Classical

abbrev F := ZMod 2

def bit (a : F) : ℕ := if a = 0 then 0 else 1

lemma bit_le (a : F) : bit a ≤ 1 := by
  unfold bit; split <;> omega

lemma bit_injective : Function.Injective bit := by
  intro a b
  revert a b
  decide

def runList {α V : Type} (ask : α → ℕ → V → F) (l : List α) (x : V) : ℕ :=
  l.foldl (fun t j => 2 * t + bit (ask j t x)) 0

lemma runList_append {α V : Type} (ask : α → ℕ → V → F) (l : List α) (a : α) (x : V) :
    runList ask (l ++ [a]) x = 2 * runList ask l x + bit (ask a (runList ask l x) x) := by
  simp [runList, List.foldl_append]

lemma runList_congr_iff {α V : Type} (ask : α → ℕ → V → F) (l : List α) (x y : V) :
    runList ask l x = runList ask l y ↔
      ∀ j : Fin l.length, ask (l.get j) (runList ask (l.take j.val) y) x =
        ask (l.get j) (runList ask (l.take j.val) y) y := by
  induction l using List.reverseRecOn with
  | nil => simp [runList]
  | append_singleton l a ih =>
    rw [runList_append, runList_append]
    have hlast : ∀ x', ask ((l ++ [a]).get ⟨l.length, by simp⟩)
        (runList ask ((l ++ [a]).take l.length) y) x' = ask a (runList ask l y) x' := by
      intro x'
      simp [List.get_eq_getElem, List.getElem_append_right]
    have hinitial (j : ℕ) (hj : j < l.length) (x' : V) :
        ask ((l ++ [a]).get ⟨j, by simpa using Nat.lt_succ_of_lt hj⟩)
          (runList ask ((l ++ [a]).take j) y) x' = ask (l.get ⟨j, hj⟩) (runList ask (l.take j) y) x' := by
      simp only [List.get_eq_getElem, List.getElem_append_left hj, List.take_append_of_le_length hj.le]
    constructor
    · intro he
      have h1 := bit_le (ask a (runList ask l x) x)
      have h2 := bit_le (ask a (runList ask l y) y)
      have hp : runList ask l x = runList ask l y := by omega
      have ha : bit (ask a (runList ask l y) x) = bit (ask a (runList ask l y) y) := by
        rw [hp] at he; omega
      intro j
      by_cases hj : j.val < l.length
      · simpa only [hinitial _ hj] using ih.mp hp ⟨j.val, hj⟩
      · have h : j.val = l.length := by have := j.isLt; simp at this; omega
        simpa only [show j = ⟨l.length, by simp⟩ from Fin.ext h, hlast] using bit_injective ha
    · intro he
      have hp : runList ask l x = runList ask l y := ih.mpr fun j => by
        simpa only [hinitial _ j.isLt] using he ⟨j.val, by simp⟩
      have ha : ask a (runList ask l y) x = ask a (runList ask l y) y := by
        simpa only [hlast] using he ⟨l.length, by simp⟩
      rw [hp, ha]

lemma sum_fiber_natAbs {X Y : Type} [Fintype X] [DecidableEq Y] (code : X → Y) (g : X → ℤ)
    (M N : ℕ)
    (bound : ∀ y ∈ Finset.univ.image code,
      M * (∑ x ∈ Finset.univ.filter (fun x => code x = y), g x).natAbs ≤
        (Finset.univ.filter (fun x => code x = y)).card * N) :
    M * (∑ x, g x).natAbs ≤ Fintype.card X * N := by
  let T := Finset.univ.image code
  let A := fun y => Finset.univ.filter (fun x => code x = y)
  have sumG : ∑ y ∈ T, ∑ x ∈ A y, g x = ∑ x, g x :=
    Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)) g
  have sumC : ∑ y ∈ T, (A y).card = Fintype.card X := by
    simpa [A] using
      (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset X)) (t := T) (g := code)
        (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)) (fun _ => 1 : X → ℕ))
  have tri (s : Finset Y) (f : Y → ℤ) : (∑ y ∈ s, f y).natAbs ≤ ∑ y ∈ s, (f y).natAbs := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
  rw [← sumG, ← sumC, Finset.sum_mul]
  refine (Nat.mul_le_mul_left _ (tri T _)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum bound
def dif {V : Type} [Add V] (f : V → F) (v x : V) : F := f (x + v) - f x

def Van3 {V : Type} [Add V] (f : V → F) : Prop :=
  ∀ (v : Fin 3 → V) x, (List.ofFn v).foldl dif f x = 0

lemma Van3.affine {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {f : W → F} (hf : Van3 f) (E : V →ₗ[F] W) (b : W) :
    Van3 (fun x => f (E x + b)) := by
  have aux (l : List V) (g : W → F) (x : V) :
      l.foldl dif (fun z => g (E z + b)) x =
        (l.map E).foldl dif g (E x + b) := by
    induction l generalizing g x with
    | nil => rfl
    | cons v l ih =>
      simp only [List.foldl_cons, List.map_cons]
      have hd : dif (fun z => g (E z + b)) v = fun z => dif g (E v) (E z + b) := by
        funext z
        simp only [dif, map_add]
        rw [add_right_comm (E z) (E v) b]
      rw [hd, ih]
  intro v x
  rw [aux, List.map_ofFn]
  exact hf _ _

lemma Van3.sub {V : Type} [Add V] {f g : V → F} (hf : Van3 f) (hg : Van3 g) :
    Van3 (fun x => f x - g x) := by
  intro v x
  have aux (l : List V) (f g : V → F) (x : V) :
      l.foldl dif (fun z => f z - g z) x = l.foldl dif f x - l.foldl dif g x := by
    induction l generalizing f g x with
    | nil => rfl
    | cons a l ih =>
      simp only [List.foldl_cons]
      have hd : dif (fun z => f z - g z) a = fun z => dif f a z - dif g a z := by
        funext z
        simp only [dif]
        abel
      rw [hd, ih]
  rw [aux, hf v x, hg v x, sub_zero]

lemma quadratic_matrix {ι : Type} [Fintype ι] [DecidableEq ι] {f : (ι → F) → F}
    (hf : Van3 f) :
    ∃ (M : ι → ι → F) (c : F), ∀ y, f y = (∑ i, ∑ j, M i j * y i * y j) + c := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have second (a b x : ι → F) : dif (dif f a) b x = dif (dif f a) b 0 := by
    have h := hf ![a, b, x] 0
    change dif (dif (dif f a) b) x 0 = 0 at h
    exact sub_eq_zero.mp (by simpa only [dif, zero_add] using h)
  let e : ι → (ι → F) := fun i => Pi.single i 1
  let M : ι → ι → F := fun i j =>
    if i = j then dif f (e i) 0 else if j < i then dif (dif f (e i)) (e j) 0 else 0
  refine ⟨M, f 0, fun y => ?_⟩
  let z : ι → (ι → F) := fun i => Pi.single i (y i)
  have z0 (i : ι) (h : y i = 0) : z i = 0 := by simp [z, h]
  have z1 (i : ι) (h : y i = 1) : z i = e i := by simp [z, e, h]
  have zerodif (g : (ι → F) → F) : dif g 0 = 0 := by funext x; simp [dif]
  have yd (i : ι) : y i = 0 ∨ y i = 1 := by
    generalize y i = a
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  have first_term (i : ι) : dif f (z i) 0 = M i i * y i * y i := by
    rcases yd i with hi | hi <;> simp [M, hi, z0, z1, zerodif]
  have second_term (i j : ι) (h : j < i) :
      dif (dif f (z i)) (z j) 0 = M i j * y i * y j := by
    rcases yd i with hi | hi <;> rcases yd j with hj | hj <;>
      simp [M, hi, hj, z0, z1, dif, h, ne_of_gt h]
  have first_expand (a : ι → F) (s : Finset ι) :
      dif f a (∑ i ∈ s, z i) = dif f a 0 + ∑ i ∈ s, dif (dif f a) (z i) 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [add_comm (z i)]
      have h := second a (z i) (∑ j ∈ s, z j)
      simp only [dif] at h ⊢
      simp only [dif] at ih
      abel_nf at *
      linear_combination h + ih
  have expand (s : Finset ι) :
      f (∑ i ∈ s, z i) = (∑ i ∈ s, ∑ j ∈ s, M i j * y i * y j) + f 0 := by
    refine Finset.induction_on_max s (by simp) ?_
    intro i s hi ih
    have hin : i ∉ s := fun h => (lt_irrefl i) (hi i h)
    simp only [Finset.sum_insert hin]
    rw [Finset.sum_add_distrib]
    have hz : (∑ j ∈ s, M j i * y j * y i) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := hi j hj
      simp [M, hj'.ne, not_lt_of_ge hj'.le]
    rw [hz, zero_add, add_assoc (_ + _), ← ih, ← first_term]
    have ho : (∑ j ∈ s, M i j * y i * y j) = ∑ j ∈ s, dif (dif f (z i)) (z j) 0 :=
      Finset.sum_congr rfl (fun j hj => (second_term i j (hi j hj)).symm)
    rw [ho]
    rw [add_comm (z i)]
    have hd := first_expand (z i) s
    simp only [dif] at hd ⊢
    linear_combination hd
  have h := expand Finset.univ
  change f (∑ i, Pi.single i (y i)) = _ at h
  rw [Finset.univ_sum_single] at h
  exact h

def sign (a : F) : ℤ := if a = 0 then 1 else -1

def cubic {ι : Type} {m : ℕ} (pos : Fin m × Fin 3 ↪ ι) (y : ι → F) : F :=
  ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))

def MatrixQuad {ι : Type} [Fintype ι] (Q : (ι → F) → F) : Prop :=
  ∃ (M : ι → ι → F) (b : F), ∀ y, Q y = (∑ i, ∑ j, M i j * y i * y j) + b

def FiberBound : Prop :=
  ∀ (c : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (pos : Fin m × Fin 3 ↪ ι)
    (Q : (ι → F) → F), MatrixQuad Q →
    ∀ (eqs : Fin c → (ι → F) × F),
      let A : Finset (ι → F) := Finset.univ.filter
        (fun y => ∀ r : Fin c, (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2)
      4 ^ (m - c) * (∑ y ∈ A, sign (Q y + cubic pos y)).natAbs ≤ A.card * 3 ^ (m - c)

/-- Apply the disjoint-cubic bound to every transcript on an affine cube, then sum
the absolute biases. The affine embedding need not be injective for this estimate. -/
theorem adaptive_cube_bound (fiberBound : FiberBound) {ι W α : Type}
    [Fintype ι] [DecidableEq ι] [AddCommGroup W] [Module F W]
    {m : ℕ} (pos : Fin m × Fin 3 ↪ ι) (E : (ι → F) →ₗ[F] W) (b : W)
    (test : α → ℕ → W →ₗ[F] F) (l : List α)
    (target : W → F) (out : ℕ → W → F) (hout : ∀ t, Van3 (out t))
    (Q : (ι → F) → F) (hQ : Van3 Q)
    (htarget : ∀ y, target (E y + b) = Q y + cubic pos y) :
    let run := fun w => runList (fun j t => test j t) l w
    4 ^ (m - l.length) * (∑ y : ι → F,
      sign (target (E y + b) - out (run (E y + b)) (E y + b))).natAbs ≤
      Fintype.card (ι → F) * 3 ^ (m - l.length) := by
  dsimp only
  let a : α → ℕ → W → F := fun j t => test j t
  let code : (ι → F) → ℕ := fun y => runList a l (E y + b)
  let g : (ι → F) → ℤ := fun y => sign (target (E y + b) - out (code y) (E y + b))
  change 4 ^ (m - l.length) * (∑ y, g y).natAbs ≤ _
  apply sum_fiber_natAbs code g
  intro t ht
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp ht
  let form : Fin l.length → W →ₗ[F] F :=
    fun j => test (l.get j) (runList a (l.take j.val) (E z + b))
  let eqs : Fin l.length → (ι → F) × F := fun j =>
    (fun i => form j (E (Pi.single i 1)), form j (E z + b) - form j b)
  have linear_sum (j : Fin l.length) (y : ι → F) :
      (∑ i : ι, (eqs j).1 i * y i) = form j (E y) := by
    nth_rw 2 [← Finset.univ_sum_single y]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : Pi.single i (y i) = y i • (Pi.single i 1 : ι → F) := by
      rw [← Pi.single_smul i]
      simp
    rw [hs, map_smul, map_smul]
    exact mul_comm _ _
  let A : Finset (ι → F) := Finset.univ.filter (fun y => code y = t)
  have hA : A = Finset.univ.filter
      (fun y => ∀ j : Fin l.length, (∑ i : ι, (eqs j).1 i * y i) = (eqs j).2) := by
    ext y
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz]
    change runList a l (E y + b) = runList a l (E z + b) ↔ _
    rw [runList_congr_iff]
    apply forall_congr'
    intro j
    change form j (E y + b) = form j (E z + b) ↔ _
    rw [linear_sum, map_add]
    exact eq_sub_iff_add_eq.symm
  let R : (ι → F) → F := fun y => Q y - out t (E y + b)
  have hR : MatrixQuad R := quadratic_matrix (hQ.sub ((hout t).affine E b))
  have hG : ∑ y ∈ A, g y = ∑ y ∈ A, sign (R y + cubic pos y) := by
    apply Finset.sum_congr rfl
    intro y hy
    have hyt : code y = t := (Finset.mem_filter.mp hy).2
    simp only [g, R, hyt, htarget]
    congr 1
    abel
  change 4 ^ (m - l.length) * (∑ y ∈ A, g y).natAbs ≤ A.card * _
  rw [hG, hA]
  exact fiberBound l.length m pos R hR eqs

lemma bound_of_all_translates {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] [AddGroup X]
    (shift : Y → X) (g : X → ℤ) (M N : ℕ)
    (h : ∀ x : X, M * (∑ y : Y, g (x + shift y)).natAbs ≤ Fintype.card Y * N) :
    M * (∑ x : X, g x).natAbs ≤ Fintype.card X * N := by
  have htranslate (y : Y) : (∑ x : X, g (x + shift y)) = ∑ x : X, g x := by
    let e : X ≃ X :=
      ⟨fun x => x + shift y, fun w => w - shift y,
        fun x => add_sub_cancel_right _ _, fun x => sub_add_cancel _ _⟩
    exact e.sum_comp g
  have hsum : (∑ x : X, ∑ y : Y, g (x + shift y)) =
      (Fintype.card Y : ℤ) * ∑ x : X, g x := by
    rw [Finset.sum_comm]
    simp only [htranslate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have habs : (∑ x : X, ∑ y : Y, g (x + shift y)).natAbs ≤
      ∑ x : X, (∑ y : Y, g (x + shift y)).natAbs := by
    have tri (s : Finset X) (f : X → ℤ) : (∑ x ∈ s, f x).natAbs ≤ ∑ x ∈ s, (f x).natAbs := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert z s hz ih =>
        simp only [Finset.sum_insert hz]
        exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
    exact tri _ _
  rw [hsum, Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hstep : M * (∑ x : X, (∑ y : Y, g (x + shift y)).natAbs) ≤
      Fintype.card X * (Fintype.card Y * N) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _ : X, Fintype.card Y * N := Finset.sum_le_sum (fun x _ => h x)
      _ = _ := by simp
  have htotal := (Nat.mul_le_mul_left M habs).trans hstep
  apply Nat.le_of_mul_le_mul_left _ (Fintype.card_pos (α := Y))
  convert htotal using 1 <;> ac_rfl

lemma sum_sign_eq_hits {X : Type} [Fintype X] (f g : X → F) :
    (∑ x : X, sign (f x - g x)) =
      2 * (Nat.card {x : X // f x = g x} : ℤ) - (Fintype.card X : ℤ) := by
  have h (x : X) : sign (f x - g x) = 2 * (if f x = g x then 1 else 0) - 1 := by
    by_cases hxy : f x = g x <;> simp [sign, sub_eq_zero, hxy]
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter]
  simp


/- Disjoint-cubic fiber estimate ported from e5eb43659fdc210299daa288589367628e7185e7,
   lean/PEqualNP/Outside/L_meta_29766.lean. Only its supporting lemmas are retained;
   the helpers are adapted for standalone checking. -/
namespace Pinned29766

def chi (a : F) : ℤ := if a = 0 then 1 else -1

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_mul_self (a : F) : a * a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_eq_one_of_ne_zero {a : F} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma chi_natAbs (a : F) : (chi a).natAbs = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> decide


lemma sum_zmod2 {α : Type*} [AddCommMonoid α] (f : F → α) : ∑ u : F, f u = f 0 + f 1 := by
  rw [Fintype.sum_eq_add (0 : F) (1 : F) (by decide)
    (fun u ⟨h0, h1⟩ => by rcases zmod2_cases u with rfl | rfl; exact absurd rfl h0; exact absurd rfl h1)]

lemma sum_zmod2_shift (α : F) (f : F → ℤ) : ∑ u : F, f u = f α + f (α + 1) := by
  rw [sum_zmod2]
  rcases zmod2_cases α with rfl | rfl
  · simp
  · simp [show (1 : F) + 1 = 0 by decide, add_comm]


lemma sum_chi_two_vars (lb lc : F) :
    ∑ u : F, ∑ v : F, chi (u * v + u * lb + v * lc) = 2 * chi (lb * lc) := by
  rcases zmod2_cases lb with rfl | rfl <;> rcases zmod2_cases lc with rfl | rfl <;> decide


lemma natAbs_sum_le {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ a ∈ s, f a).natAbs ≤ ∑ a ∈ s, (f a).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

lemma natAbs_sum_chi_le {α : Type*} (s : Finset α) (f : α → F) :
    (∑ a ∈ s, chi (f a)).natAbs ≤ s.card := by
  calc (∑ a ∈ s, chi (f a)).natAbs
      ≤ ∑ a ∈ s, (chi (f a)).natAbs := natAbs_sum_le s (fun a => chi (f a))
    _ = ∑ _a ∈ s, 1 := Finset.sum_congr rfl (fun a _ => chi_natAbs (f a))
    _ = s.card := by simp

lemma pow_three_four_mono {a b : ℕ} (h : a ≤ b) (X Y : ℕ)
    (hY : 4 ^ b * X ≤ Y * 3 ^ b) : 4 ^ a * X ≤ Y * 3 ^ a := by
  have hpow : 3 ^ (b - a) ≤ 4 ^ (b - a) := Nat.pow_le_pow_left (by omega) _
  have h1 : 4 ^ a * 3 ^ (b - a) * X ≤ 4 ^ b * X := by
    have hsplit : 4 ^ b = 4 ^ a * 4 ^ (b - a) := by rw [← pow_add, Nat.add_sub_of_le h]
    rw [hsplit]
    calc 4 ^ a * 3 ^ (b - a) * X
        = (4 ^ a * X) * 3 ^ (b - a) := by ring
      _ ≤ (4 ^ a * X) * 4 ^ (b - a) := Nat.mul_le_mul_left _ hpow
      _ = 4 ^ a * 4 ^ (b - a) * X := by ring
  have h2 : 4 ^ a * 3 ^ (b - a) * X ≤ Y * 3 ^ a * 3 ^ (b - a) := by
    have hsplit : 3 ^ b = 3 ^ a * 3 ^ (b - a) := by rw [← pow_add, Nat.add_sub_of_le h]
    rw [hsplit] at hY
    calc 4 ^ a * 3 ^ (b - a) * X ≤ 4 ^ b * X := h1
      _ ≤ Y * (3 ^ a * 3 ^ (b - a)) := hY
      _ = Y * 3 ^ a * 3 ^ (b - a) := by ring
  have hpos : 0 < 3 ^ (b - a) := Nat.pow_pos (by omega)
  have h3 : (4 ^ a * X) * 3 ^ (b - a) ≤ (Y * 3 ^ a) * 3 ^ (b - a) := by
    calc (4 ^ a * X) * 3 ^ (b - a) = 4 ^ a * 3 ^ (b - a) * X := by ring
      _ ≤ Y * 3 ^ a * 3 ^ (b - a) := h2
  exact Nat.le_of_mul_le_mul_right h3 hpos


def IsAffine {ι : Type} [Fintype ι] (L : (ι → F) → F) : Prop :=
  ∃ (v : ι → F) (c : F), ∀ y, L y = (∑ i, v i * y i) + c

def IsQuad {ι : Type} [Fintype ι] (Q : (ι → F) → F) : Prop :=
  ∃ (M : ι → ι → F) (c : F), ∀ y, Q y = (∑ i, ∑ j, M i j * y i * y j) + c

lemma isQuad_add {ι : Type} [Fintype ι] {Q1 Q2 : (ι → F) → F}
    (h1 : IsQuad Q1) (h2 : IsQuad Q2) : IsQuad (fun y => Q1 y + Q2 y) := by
  obtain ⟨M1, c1, hM1⟩ := h1
  obtain ⟨M2, c2, hM2⟩ := h2
  refine ⟨fun i j => M1 i j + M2 i j, c1 + c2, fun y => ?_⟩
  dsimp only
  rw [hM1 y, hM2 y]
  have hsum : ∑ i, ∑ j, (M1 i j + M2 i j) * y i * y j =
      (∑ i, ∑ j, M1 i j * y i * y j) + (∑ i, ∑ j, M2 i j * y i * y j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum]; ring

lemma isQuad_of_isAffine {ι : Type} [Fintype ι] [DecidableEq ι] {L : (ι → F) → F}
    (hL : IsAffine L) : IsQuad L := by
  obtain ⟨v, c, hv⟩ := hL
  refine ⟨fun i j => if i = j then v i else 0, c, fun y => ?_⟩
  rw [hv y]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have : ∑ j, (if i = j then v i else 0) * y i * y j = v i * y i * y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Ne.symm hji]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [this, mul_assoc, zmod2_mul_self]

lemma isQuad_mul_affine {ι : Type} [Fintype ι] [DecidableEq ι] {L1 L2 : (ι → F) → F}
    (h1 : IsAffine L1) (h2 : IsAffine L2) : IsQuad (fun y => L1 y * L2 y) := by
  obtain ⟨v1, c1, hv1⟩ := h1
  obtain ⟨v2, c2, hv2⟩ := h2
  have hq0 : IsQuad (fun y => (∑ i, v1 i * y i) * (∑ j, v2 j * y j)) := by
    refine ⟨fun i j => v1 i * v2 j, 0, fun y => ?_⟩
    dsimp only
    rw [add_zero, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have hq1 : IsQuad (fun y => c2 * (∑ i, v1 i * y i) + c1 * (∑ j, v2 j * y j) + c1 * c2) := by
    apply isQuad_of_isAffine
    refine ⟨fun i => c2 * v1 i + c1 * v2 i, c1 * c2, fun y => ?_⟩
    dsimp only
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  obtain ⟨M, c, hM⟩ := isQuad_add hq0 hq1
  refine ⟨M, c, fun y => ?_⟩
  dsimp only
  have heq : L1 y * L2 y = (∑ i, v1 i * y i) * (∑ j, v2 j * y j) +
      (c2 * (∑ i, v1 i * y i) + c1 * (∑ j, v2 j * y j) + c1 * c2) := by
    rw [hv1 y, hv2 y]; ring
  rw [heq]; exact hM y

lemma isQuad_sum {α ι : Type} [Fintype ι] (s : Finset α) (f : α → (ι → F) → F)
    (hf : ∀ a ∈ s, IsQuad (f a)) : IsQuad (fun y => ∑ a ∈ s, f a y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => 0, 0, fun _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨M, c, hM⟩ := isQuad_add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
    refine ⟨M, c, fun y => ?_⟩
    dsimp only
    rw [Finset.sum_insert ha]
    exact hM y

lemma isQuad_comp_affine {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    {Q : (ι → F) → F} (hQ : IsQuad Q) {φ : (ι' → F) → (ι → F)}
    (hφ : ∀ i, IsAffine (fun z => φ z i)) : IsQuad (fun z => Q (φ z)) := by
  obtain ⟨M, c, hM⟩ := hQ
  have hterm : ∀ i j : ι, IsQuad (fun z => M i j * φ z i * φ z j) := by
    intro i j
    have h1 : IsAffine (fun z => M i j * φ z i) := by
      obtain ⟨v, c0, hv⟩ := hφ i
      refine ⟨fun x => M i j * v x, M i j * c0, fun z => ?_⟩
      dsimp only
      have hvi := hv z
      dsimp only at hvi
      rw [hvi, mul_add, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    exact isQuad_mul_affine h1 (hφ j)
  have hdouble : IsQuad (fun z => ∑ i : ι, ∑ j : ι, M i j * φ z i * φ z j) :=
    isQuad_sum Finset.univ _ (fun i _ => isQuad_sum Finset.univ _ (fun j _ => hterm i j))
  have hc_quad : IsQuad (fun _ : ι' → F => c) := ⟨fun _ _ => 0, c, fun _ => by simp⟩
  obtain ⟨M0, c0, hM0⟩ := isQuad_add hdouble hc_quad
  refine ⟨M0, c0, fun z => ?_⟩
  dsimp only
  rw [hM (φ z)]
  exact hM0 z

theorem cubic_bound_unconstrained :
    ∀ (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (pos : Fin m × Fin 3 ↪ ι)
      (Q : (ι → F) → F), IsQuad Q →
      4 ^ m * (∑ y : ι → F, chi (Q y + ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))).natAbs
        ≤ Fintype.card (ι → F) * 3 ^ m := by
  intro m
  induction m with
  | zero =>
    intro ι _ _ _ Q _
    simp only [pow_zero, one_mul, mul_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact natAbs_sum_chi_le Finset.univ Q
  | succ m ih =>
    intro ι _ _ pos Q hQ
    let a : ι := pos (Fin.last m, 0)
    let b : ι := pos (Fin.last m, 1)
    let c : ι := pos (Fin.last m, 2)
    have hab : a ≠ b := fun h => by have := pos.injective h; simp at this
    have hac : a ≠ c := fun h => by have := pos.injective h; simp at this
    have hbc : b ≠ c := fun h => by have := pos.injective h; simp at this
    let ι' := {x : ι // x ≠ a ∧ x ≠ b ∧ x ≠ c}
    let embed : (F × F × F) × (ι' → F) → (ι → F) := fun p x =>
      if h1 : x = a then p.1.1
      else if h2 : x = b then p.1.2.1
      else if h3 : x = c then p.1.2.2
      else p.2 ⟨x, h1, h2, h3⟩
    let split : (ι → F) → (F × F × F) × (ι' → F) := fun y =>
      ((y a, y b, y c), fun x => y x.1)
    let hEquiv : (ι → F) ≃ (F × F × F) × (ι' → F) :=
      { toFun := split
        invFun := embed
        left_inv := fun y => by
          funext x
          dsimp [embed, split]
          split_ifs with h1 h2 h3
          · subst h1; rfl
          · subst h2; rfl
          · subst h3; rfl
          · rfl
        right_inv := fun ⟨⟨ua, ub, uc⟩, yr⟩ => by
          apply Prod.ext
          · apply Prod.ext
            · simp [embed, split]
            · apply Prod.ext
              · simp [embed, split, Ne.symm hab]
              · simp [embed, split, Ne.symm hac, Ne.symm hbc]
          · funext x
            simp [embed, split, x.2.1, x.2.2.1, x.2.2.2] }
    have hcard : Fintype.card (ι → F) = 8 * Fintype.card (ι' → F) := by
      rw [Fintype.card_congr hEquiv, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ZMod.card 2]
    let pos' : Fin m × Fin 3 ↪ ι' :=
      ⟨fun p => ⟨pos (p.1.castSucc, p.2), by
        refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h' := pos.injective h
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1⟩,
       fun p1 p2 h => by
        have h1 : pos (p1.1.castSucc, p1.2) = pos (p2.1.castSucc, p2.2) := congrArg Subtype.val h
        have h2 := pos.injective h1
        exact Prod.ext (Fin.castSucc_injective m (Prod.mk.inj h2).1) (Prod.mk.inj h2).2⟩
    let gRest : (ι' → F) → F := fun yr =>
      ∑ i : Fin m, yr (pos' (i, 0)) * yr (pos' (i, 1)) * yr (pos' (i, 2))
    have hg_embed : ∀ ua ub uc yr,
        (∑ i : Fin (m + 1), embed ((ua, ub, uc), yr) (pos (i, 0)) *
          embed ((ua, ub, uc), yr) (pos (i, 1)) * embed ((ua, ub, uc), yr) (pos (i, 2))) =
        gRest yr + ua * ub * uc := by
      intro ua ub uc yr
      rw [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        have hval : ∀ t : Fin 3, embed ((ua, ub, uc), yr) (pos (i.castSucc, t)) = yr (pos' (i, t)) := by
          intro t
          have hp := (pos' (i, t)).2
          have hp1 : pos (i.castSucc, t) ≠ a := hp.1
          have hp2 : pos (i.castSucc, t) ≠ b := hp.2.1
          have hp3 : pos (i.castSucc, t) ≠ c := hp.2.2
          dsimp [embed, pos']
          simp only [hp1, hp2, hp3, ↓reduceDIte]
          rfl
        rw [hval 0, hval 1, hval 2]
      · have h0 : embed ((ua, ub, uc), yr) a = ua := by simp [embed]
        have h1 : embed ((ua, ub, uc), yr) b = ub := by simp [embed, Ne.symm hab]
        have h2 : embed ((ua, ub, uc), yr) c = uc := by simp [embed, Ne.symm hac, Ne.symm hbc]
        exact congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2
    obtain ⟨M, c0, hM⟩ := hQ
    let α : F := M b c + M c b
    let Lb : F → (ι' → F) → F := fun ua yr =>
      M b b + (M b a + M a b) * ua + ∑ x : ι', (M b x.1 + M x.1 b) * yr x
    let Lc : F → (ι' → F) → F := fun ua yr =>
      M c c + (M c a + M a c) * ua + ∑ x : ι', (M c x.1 + M x.1 c) * yr x
    let R : F → (ι' → F) → F := fun ua yr =>
      Q (embed ((ua, 0, 0), yr))
    have hLb_aff : ∀ ua, IsAffine (Lb ua) := fun ua =>
      ⟨fun x => M b x.1 + M x.1 b, M b b + (M b a + M a b) * ua, fun yr => by dsimp [Lb]; ring⟩
    have hLc_aff : ∀ ua, IsAffine (Lc ua) := fun ua =>
      ⟨fun x => M c x.1 + M x.1 c, M c c + (M c a + M a c) * ua, fun yr => by dsimp [Lc]; ring⟩
    have hR_quad : ∀ ua, IsQuad (R ua) := by
      intro ua
      apply isQuad_comp_affine ⟨M, c0, hM⟩
      intro i
      dsimp [embed]
      split_ifs with h1 h2 h3
      · exact ⟨fun _ => 0, ua, fun _ => by simp⟩
      · exact ⟨fun _ => 0, 0, fun _ => by simp⟩
      · exact ⟨fun _ => 0, 0, fun _ => by simp⟩
      · exact ⟨fun x => if x = ⟨i, h1, h2, h3⟩ then 1 else 0, 0, fun yr => by simp⟩
    have hQ_decomp : ∀ ua ub uc yr,
        Q (embed ((ua, ub, uc), yr)) = α * ub * uc + ub * Lb ua yr + uc * Lc ua yr + R ua yr := by
      intro ua ub uc yr
      have hterm : ∀ f : ι → F,
          ∑ i : ι, f i = f a + f b + f c + ∑ x : ι', f x.1 := by
        intro f
        let S : Finset ι := {a, b, c}
        have hcomp : ∑ i : ι, f i = (∑ i ∈ S, f i) + ∑ i ∈ Finset.univ \ S, f i :=
          (Finset.sum_add_sum_compl S f).symm
        rw [hcomp]
        have hS : ∑ i ∈ S, f i = f a + f b + f c := by
          dsimp [S]
          rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
            Finset.sum_singleton, add_assoc]
        rw [hS]
        congr 1
        symm
        refine Finset.sum_bij (fun (x : ι') _ => x.1) ?_ ?_ ?_ ?_
        · intro x _; simp [S, x.2.1, x.2.2.1, x.2.2.2]
        · intro x1 _ x2 _ h; exact Subtype.ext h
        · intro i hi
          simp only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
            Finset.mem_singleton, true_and, not_or] at hi
          exact ⟨⟨i, hi.1, hi.2.1, hi.2.2⟩, Finset.mem_univ _, rfl⟩
        · intro _ _; rfl
      have hval : ∀ y : ι → F,
          Q y = (M b c + M c b) * y b * y c +
            y b * (M b b + (M b a + M a b) * y a + ∑ x : ι', (M b x.1 + M x.1 b) * y x.1) +
            y c * (M c c + (M c a + M a c) * y a + ∑ x : ι', (M c x.1 + M x.1 c) * y x.1) +
            (M a a * y a * y a + ∑ x : ι', (M a x.1 + M x.1 a) * y a * y x.1 +
              ∑ x : ι', ∑ z : ι', M x.1 z.1 * y x.1 * y z.1 + c0) := by
        intro y
        rw [hM y, hterm]
        simp_rw [hterm]
        have hbb : M b b * y b * y b = y b * M b b := by
          rw [mul_assoc, zmod2_mul_self, mul_comm]
        have hcc : M c c * y c * y c = y c * M c c := by
          rw [mul_assoc, zmod2_mul_self, mul_comm]
        have hsum_b : y b * ∑ x : ι', (M b x.1 + M x.1 b) * y x.1 =
            (∑ x : ι', M b x.1 * y b * y x.1) + (∑ x : ι', M x.1 b * y x.1 * y b) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
        have hsum_c : y c * ∑ x : ι', (M c x.1 + M x.1 c) * y x.1 =
            (∑ x : ι', M c x.1 * y c * y x.1) + (∑ x : ι', M x.1 c * y x.1 * y c) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
        have hsum_a : ∑ x : ι', (M a x.1 + M x.1 a) * y a * y x.1 =
            (∑ x : ι', M a x.1 * y a * y x.1) + (∑ x : ι', M x.1 a * y x.1 * y a) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
        simp only [Finset.sum_add_distrib]
        rw [hbb, hcc]
        have hrhs : y b * (M b b + (M b a + M a b) * y a + ∑ x : ι', (M b x.1 + M x.1 b) * y x.1) =
            y b * M b b + y b * ((M b a + M a b) * y a) +
              ((∑ x : ι', M b x.1 * y b * y x.1) + (∑ x : ι', M x.1 b * y x.1 * y b)) := by
          rw [mul_add, mul_add, hsum_b]
        have hrhs2 : y c * (M c c + (M c a + M a c) * y a + ∑ x : ι', (M c x.1 + M x.1 c) * y x.1) =
            y c * M c c + y c * ((M c a + M a c) * y a) +
              ((∑ x : ι', M c x.1 * y c * y x.1) + (∑ x : ι', M x.1 c * y x.1 * y c)) := by
          rw [mul_add, mul_add, hsum_c]
        rw [hrhs, hrhs2, hsum_a]
        ring
      have hv1 := hval (embed ((ua, ub, uc), yr))
      have hv0 := hval (embed ((ua, 0, 0), yr))
      have he_a : ∀ u1 u2, embed ((ua, u1, u2), yr) a = ua := fun _ _ => by simp [embed]
      have he_b : ∀ u1 u2, embed ((ua, u1, u2), yr) b = u1 := fun _ _ => by simp [embed, Ne.symm hab]
      have he_c : ∀ u1 u2, embed ((ua, u1, u2), yr) c = u2 := fun _ _ => by simp [embed, Ne.symm hac, Ne.symm hbc]
      have he_x : ∀ u1 u2 (x : ι'), embed ((ua, u1, u2), yr) x.1 = yr x := fun _ _ x => by
        simp [embed, x.2.1, x.2.2.1, x.2.2.2]
      simp only [he_a, he_b, he_c, he_x] at hv1 hv0
      dsimp [R, α, Lb, Lc]
      rw [hv1, hv0]
      ring

    let Sfull : ℤ := ∑ y : ι → F, chi (Q y + ∑ i : Fin (m + 1), y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))
    let Sbranch (ua : F) : ℤ :=
      ∑ ub : F, ∑ uc : F, ∑ yr : ι' → F,
        chi ((α + ua) * ub * uc + ub * Lb ua yr + uc * Lc ua yr + R ua yr + gRest yr)
    have hS_split : Sfull = Sbranch α + Sbranch (α + 1) := by
      dsimp [Sfull]
      rw [← Fintype.sum_equiv hEquiv.symm _ _ (fun _ => rfl)]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [sum_zmod2_shift α]
      have hbr : ∀ ua : F,
          (∑ x : F × F, ∑ y : ι' → F,
            chi (Q (hEquiv.symm ((ua, x), y)) +
              ∑ i : Fin (m + 1), hEquiv.symm ((ua, x), y) (pos (i, 0)) *
                hEquiv.symm ((ua, x), y) (pos (i, 1)) * hEquiv.symm ((ua, x), y) (pos (i, 2)))) =
          Sbranch ua := by
        intro ua
        rw [Fintype.sum_prod_type]
        dsimp [Sbranch, hEquiv]
        apply Finset.sum_congr rfl; intro ub _
        apply Finset.sum_congr rfl; intro uc _
        apply Finset.sum_congr rfl; intro yr _
        rw [hg_embed, hQ_decomp]
        congr 1; ring
      rw [hbr α, hbr (α + 1)]

    have hB1 : 4 ^ m * (Sbranch α).natAbs ≤ 4 * Fintype.card (ι' → F) * 3 ^ m := by
      dsimp [Sbranch]
      let inner1 : F → F → ℤ := fun ub uc =>
        ∑ yr : ι' → F, chi ((α + α) * ub * uc + ub * Lb α yr + uc * Lc α yr + R α yr + gRest yr)
      have htri : (∑ ub : F, ∑ uc : F, inner1 ub uc).natAbs ≤
          ∑ ub : F, ∑ uc : F, (inner1 ub uc).natAbs := by
        calc (∑ ub : F, ∑ uc : F, inner1 ub uc).natAbs
            ≤ ∑ ub : F, (∑ uc : F, inner1 ub uc).natAbs := natAbs_sum_le _ _
          _ ≤ ∑ ub : F, ∑ uc : F, (inner1 ub uc).natAbs :=
              Finset.sum_le_sum (fun ub _ => natAbs_sum_le _ _)
      have hterm : ∀ ub uc : F, 4 ^ m * (inner1 ub uc).natAbs ≤ Fintype.card (ι' → F) * 3 ^ m := by
        intro ub uc
        have hq : IsQuad (fun yr => ub * Lb α yr + uc * Lc α yr + R α yr) := by
          have ha1 : IsQuad (fun yr => ub * Lb α yr) := isQuad_of_isAffine (by
            obtain ⟨v, c1, hv⟩ := hLb_aff α
            exact ⟨fun x => ub * v x, ub * c1, fun yr => by
              dsimp only; rw [hv yr, mul_add, Finset.mul_sum]
              congr 1; apply Finset.sum_congr rfl; intro x _; ring⟩)
          have ha2 : IsQuad (fun yr => uc * Lc α yr) := isQuad_of_isAffine (by
            obtain ⟨v, c1, hv⟩ := hLc_aff α
            exact ⟨fun x => uc * v x, uc * c1, fun yr => by
              dsimp only; rw [hv yr, mul_add, Finset.mul_sum]
              congr 1; apply Finset.sum_congr rfl; intro x _; ring⟩)
          exact isQuad_add (isQuad_add ha1 ha2) (hR_quad α)
        have hih := ih pos' _ hq
        have heq : inner1 ub uc =
            ∑ yr : ι' → F, chi ((ub * Lb α yr + uc * Lc α yr + R α yr) + gRest yr) := by
          dsimp [inner1]
          apply Finset.sum_congr rfl; intro yr _
          rw [zmod2_add_self, zero_mul, zero_mul, zero_add]
        rw [heq]
        exact hih
      calc 4 ^ m * (∑ ub : F, ∑ uc : F, inner1 ub uc).natAbs
          ≤ 4 ^ m * ∑ ub : F, ∑ uc : F, (inner1 ub uc).natAbs := Nat.mul_le_mul_left _ htri
        _ = ∑ ub : F, ∑ uc : F, 4 ^ m * (inner1 ub uc).natAbs := by
            simp only [Finset.mul_sum]
        _ ≤ ∑ _ub : F, ∑ _uc : F, Fintype.card (ι' → F) * 3 ^ m :=
            Finset.sum_le_sum (fun ub _ => Finset.sum_le_sum (fun uc _ => hterm ub uc))
        _ = 4 * Fintype.card (ι' → F) * 3 ^ m := by
            simp only [Finset.sum_const, Finset.card_univ, ZMod.card 2, smul_eq_mul]; ring

    have hB2 : 4 ^ m * (Sbranch (α + 1)).natAbs ≤ 2 * Fintype.card (ι' → F) * 3 ^ m := by
      have hS2 : Sbranch (α + 1) =
          2 * ∑ yr : ι' → F, chi ((Lb (α + 1) yr * Lc (α + 1) yr + R (α + 1) yr) + gRest yr) := by
        dsimp [Sbranch]
        have hswap : ∀ (f : F → F → (ι' → F) → ℤ),
            ∑ ub : F, ∑ uc : F, ∑ yr : ι' → F, f ub uc yr =
            ∑ yr : ι' → F, ∑ ub : F, ∑ uc : F, f ub uc yr := by
          intro f
          conv_lhs => arg 2; ext ub; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
        rw [hswap, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro yr _
        have hα1 : α + (α + 1) = 1 := by rw [← add_assoc, zmod2_add_self, zero_add]
        have hfac : ∀ ub uc : F,
            chi ((α + (α + 1)) * ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr + R (α + 1) yr + gRest yr) =
            chi (ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr) * chi (R (α + 1) yr + gRest yr) := by
          intro ub uc
          rw [hα1, one_mul, ← chi_add]
          congr 1; ring
        simp_rw [hfac]
        have hpull : (∑ ub : F, ∑ uc : F,
            chi (ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr) * chi (R (α + 1) yr + gRest yr)) =
            (∑ ub : F, ∑ uc : F, chi (ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr)) *
              chi (R (α + 1) yr + gRest yr) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro ub _
          rw [Finset.sum_mul]
        rw [hpull, sum_chi_two_vars, mul_assoc, ← chi_add]
        congr 2; ring
      rw [hS2, Int.natAbs_mul]
      have hq : IsQuad (fun yr => Lb (α + 1) yr * Lc (α + 1) yr + R (α + 1) yr) :=
        isQuad_add (isQuad_mul_affine (hLb_aff (α + 1)) (hLc_aff (α + 1))) (hR_quad (α + 1))
      have hih := ih pos' _ hq
      have h2abs : (2 : ℤ).natAbs = 2 := rfl
      rw [h2abs]
      calc 4 ^ m * (2 * _) = 2 * (4 ^ m * _) := by ring
        _ ≤ 2 * (Fintype.card (ι' → F) * 3 ^ m) := Nat.mul_le_mul_left 2 hih
        _ = 2 * Fintype.card (ι' → F) * 3 ^ m := by ring

    have hcomb : 4 ^ m * Sfull.natAbs ≤ 6 * Fintype.card (ι' → F) * 3 ^ m := by
      rw [hS_split]
      calc 4 ^ m * (Sbranch α + Sbranch (α + 1)).natAbs
          ≤ 4 ^ m * ((Sbranch α).natAbs + (Sbranch (α + 1)).natAbs) :=
            Nat.mul_le_mul_left _ (Int.natAbs_add_le _ _)
        _ = 4 ^ m * (Sbranch α).natAbs + 4 ^ m * (Sbranch (α + 1)).natAbs := Nat.mul_add _ _ _
        _ ≤ 4 * Fintype.card (ι' → F) * 3 ^ m + 2 * Fintype.card (ι' → F) * 3 ^ m :=
            Nat.add_le_add hB1 hB2
        _ = 6 * Fintype.card (ι' → F) * 3 ^ m := by ring
    rw [hcard, pow_succ, pow_succ]
    calc 4 ^ m * 4 * Sfull.natAbs = 4 * (4 ^ m * Sfull.natAbs) := by ring
      _ ≤ 4 * (6 * Fintype.card (ι' → F) * 3 ^ m) := Nat.mul_le_mul_left 4 hcomb
      _ = 8 * Fintype.card (ι' → F) * (3 ^ m * 3) := by ring

theorem cubic_fiber_bound :
    ∀ (c : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (pos : Fin m × Fin 3 ↪ ι)
      (Q : (ι → F) → F), IsQuad Q →
      ∀ (eqs : Fin c → (ι → F) × F),
        let A : Finset (ι → F) :=
          Finset.univ.filter (fun y => ∀ r : Fin c, (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2)
        4 ^ (m - c) * (∑ y ∈ A, chi (Q y + ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))).natAbs
          ≤ A.card * 3 ^ (m - c) := by
  intro c
  induction c with
  | zero =>
    intro ι _ _ m pos Q hQ eqs
    simp only [Nat.sub_zero]
    have hA : Finset.univ.filter (fun y : ι → F => ∀ r : Fin 0, (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2) =
        Finset.univ := by
      ext y; simp
    rw [hA, Finset.card_univ]
    exact cubic_bound_unconstrained m pos Q hQ
  | succ c ih =>
    intro ι _ _ m pos Q hQ eqs
    dsimp only
    set A : Finset (ι → F) :=
      Finset.univ.filter (fun y => ∀ r : Fin (c + 1), (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2)
    let v : ι → F := (eqs (Fin.last c)).1
    let γ : F := (eqs (Fin.last c)).2
    by_cases hv0 : ∀ i : ι, v i = 0
    · by_cases hγ : γ = 0
      · let eqs' : Fin c → (ι → F) × F := fun r => eqs r.castSucc
        have hAeq : A = Finset.univ.filter (fun y => ∀ r : Fin c, (∑ i : ι, (eqs' r).1 i * y i) = (eqs' r).2) := by
          ext y
          simp only [A, eqs', Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h r; exact h r.castSucc
          · intro h r
            refine Fin.lastCases ?_ (fun r0 => h r0) r
            change (∑ i : ι, v i * y i) = γ
            rw [hγ]
            exact Finset.sum_eq_zero (fun i _ => by rw [hv0 i, zero_mul])
        rw [hAeq]
        exact pow_three_four_mono (by omega : m - (c + 1) ≤ m - c) _ _ (ih m pos Q hQ eqs')
      · have hAempty : A = ∅ := by
          ext y
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h
          have hlast : (∑ i : ι, v i * y i) = γ := h (Fin.last c)
          have hzero : (∑ i : ι, v i * y i) = 0 :=
            Finset.sum_eq_zero (fun i _ => by rw [hv0 i, zero_mul])
          rw [hzero] at hlast
          exact hγ hlast.symm
        rw [hAempty]; simp
    · push Not at hv0
      obtain ⟨p, hpne⟩ := hv0
      have hp1 : v p = 1 := zmod2_eq_one_of_ne_zero hpne
      let ι1 := {x : ι // x ≠ p}
      let L : (ι1 → F) → F := fun yr => γ + ∑ x : ι1, v x.1 * yr x
      let lift : (ι1 → F) → (ι → F) := fun yr i => if h : i = p then L yr else yr ⟨i, h⟩
      have hlift_p : ∀ yr, lift yr p = L yr := fun yr => by simp [lift]
      have hlift_ne : ∀ yr (x : ι1), lift yr x.1 = yr x := fun yr x => by simp [lift, x.2]
      have hsum_split : ∀ (f : ι → F), ∑ i : ι, f i = f p + ∑ x : ι1, f x.1 := by
        intro f
        rw [← Finset.sum_add_sum_compl ({p} : Finset ι) f, Finset.sum_singleton]
        congr 1
        symm
        refine Finset.sum_bij (fun (x : ι1) _ => x.1) ?_ ?_ ?_ ?_
        · intro x _; simp [x.2]
        · intro x1 _ x2 _ h; exact Subtype.ext h
        · intro i hi
          simp only [Finset.mem_compl, Finset.mem_singleton] at hi
          exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
        · intro _ _; rfl
      let eqs1 : Fin c → (ι1 → F) × F := fun r =>
        (fun x => (eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1,
         (eqs r.castSucc).2 + (eqs r.castSucc).1 p * γ)
      let A1 : Finset (ι1 → F) :=
        Finset.univ.filter (fun yr => ∀ r : Fin c, (∑ x : ι1, (eqs1 r).1 x * yr x) = (eqs1 r).2)
      have hlift_eq_iff : ∀ yr (r : Fin c),
          (∑ i : ι, (eqs r.castSucc).1 i * lift yr i) = (eqs r.castSucc).2 ↔
          (∑ x : ι1, (eqs1 r).1 x * yr x) = (eqs1 r).2 := by
        intro yr r
        rw [hsum_split, hlift_p]
        simp_rw [hlift_ne]
        dsimp [eqs1, L]
        have h1 : (eqs r.castSucc).1 p * (γ + ∑ x : ι1, v x.1 * yr x) +
            ∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x =
            (∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x) +
              (eqs r.castSucc).1 p * γ := by
          rw [mul_add, Finset.mul_sum]
          have hadd : (∑ x : ι1, (eqs r.castSucc).1 p * (v x.1 * yr x)) +
              (∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x) =
              ∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro x _; ring
          calc (eqs r.castSucc).1 p * γ + (∑ x : ι1, (eqs r.castSucc).1 p * (v x.1 * yr x)) +
                ∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x
              = ((∑ x : ι1, (eqs r.castSucc).1 p * (v x.1 * yr x)) +
                  ∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x) + (eqs r.castSucc).1 p * γ := by ring
            _ = _ := by rw [hadd]
        rw [h1]
        constructor
        · intro h
          calc ∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x
              = ((∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x) +
                  (eqs r.castSucc).1 p * γ) + (eqs r.castSucc).1 p * γ := by
                rw [add_assoc, zmod2_add_self, add_zero]
            _ = (eqs r.castSucc).2 + (eqs r.castSucc).1 p * γ := by rw [h]
        · intro h
          rw [h, add_assoc, zmod2_add_self, add_zero]
      have hlift_last : ∀ yr, (∑ i : ι, v i * lift yr i) = γ := by
        intro yr
        rw [hsum_split, hlift_p, hp1, one_mul]
        simp_rw [hlift_ne]
        dsimp [L]
        rw [add_assoc, zmod2_add_self, add_zero]
      have hlift_bij : ∀ (f : (ι → F) → ℤ), ∑ y ∈ A, f y = ∑ yr ∈ A1, f (lift yr) := by
        intro f
        symm
        refine Finset.sum_bij (fun yr _ => lift yr) ?_ ?_ ?_ ?_
        · intro yr hyr
          simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and] at hyr
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          intro r
          refine Fin.lastCases (hlift_last yr) (fun r0 => (hlift_eq_iff yr r0).mpr (hyr r0)) r
        · intro yr1 _ yr2 _ h
          funext x
          have := congrFun h x.1
          simpa [lift, x.2] using this
        · intro y hy
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          let yr : ι1 → F := fun x => y x.1
          have hlast : (∑ i : ι, v i * y i) = γ := hy (Fin.last c)
          rw [hsum_split, hp1, one_mul] at hlast
          have hyp : y p = L yr := by
            dsimp [L, yr]
            calc y p = (y p + ∑ x : ι1, v x.1 * y x.1) + ∑ x : ι1, v x.1 * y x.1 := by
                  rw [add_assoc, zmod2_add_self, add_zero]
              _ = γ + ∑ x : ι1, v x.1 * y x.1 := by rw [hlast]
          have hly : lift yr = y := by
            funext i
            dsimp [lift, yr]
            split_ifs with hi
            · subst hi; exact hyp.symm
            · rfl
          have hyr_mem : yr ∈ A1 := by
            simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and]
            intro r
            exact (hlift_eq_iff yr r).mp (by rw [hly]; exact hy r.castSucc)
          exact ⟨yr, hyr_mem, hly⟩
        · intro _ _; rfl
      have hcardA : A.card = A1.card := by
        have h1 := hlift_bij (fun _ => (1 : ℤ))
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
        exact Int.ofNat.inj h1
      have hQ1 : IsQuad (fun yr => Q (lift yr)) := by
        apply isQuad_comp_affine hQ
        intro i
        dsimp [lift]
        split_ifs with hi
        · exact ⟨fun x => v x.1, γ, fun _ => by dsimp [L]; ring⟩
        · exact ⟨fun x => if x = ⟨i, hi⟩ then 1 else 0, 0, fun yr => by simp⟩
      by_cases hp_in : ∃ i0 : Fin m, ∃ t0 : Fin 3, pos (i0, t0) = p
      · obtain ⟨i0, t0, hpos0⟩ := hp_in
        have hm1 : 0 < m := Fin.pos i0
        let t1 : Fin 3 := ⟨(t0.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
        let t2 : Fin 3 := ⟨(t0.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
        have ht01 : t0 ≠ t1 := by fin_cases t0 <;> decide
        have ht02 : t0 ≠ t2 := by fin_cases t0 <;> decide
        have ht12 : t1 ≠ t2 := by fin_cases t0 <;> decide
        have htriple_prod : ∀ y : ι → F,
            y (pos (i0, 0)) * y (pos (i0, 1)) * y (pos (i0, 2)) =
            y (pos (i0, t0)) * y (pos (i0, t1)) * y (pos (i0, t2)) := by
          intro y; fin_cases t0 <;> dsimp [t1, t2] <;> ring
        have hp1_ne : pos (i0, t1) ≠ p := fun h => by
          rw [← hpos0] at h
          exact ht01 (congrArg Prod.snd (pos.injective h)).symm
        have hp2_ne : pos (i0, t2) ≠ p := fun h => by
          rw [← hpos0] at h
          exact ht02 (congrArg Prod.snd (pos.injective h)).symm
        let p1' : ι1 := ⟨pos (i0, t1), hp1_ne⟩
        let p2' : ι1 := ⟨pos (i0, t2), hp2_ne⟩
        have hp12' : p2' ≠ p1' := fun h =>
          ht12 (congrArg Prod.snd (pos.injective (congrArg Subtype.val h))).symm
        let ι2 := {x : ι1 // x ≠ p1'}
        let lift2 (β : F) (z : ι2 → F) : ι1 → F := fun x => if h : x = p1' then β else z ⟨x, h⟩
        let eqs2 (β : F) : Fin c → (ι2 → F) × F := fun r =>
          (fun x => (eqs1 r).1 x.1, (eqs1 r).2 + (eqs1 r).1 p1' * β)
        let A2 (β : F) : Finset (ι2 → F) :=
          Finset.univ.filter (fun z => ∀ r : Fin c, (∑ x : ι2, (eqs2 β r).1 x * z x) = (eqs2 β r).2)
        have hsum1_split : ∀ (f : ι1 → F), ∑ x : ι1, f x = f p1' + ∑ x : ι2, f x.1 := by
          intro f
          rw [← Finset.sum_add_sum_compl ({p1'} : Finset ι1) f, Finset.sum_singleton]
          congr 1
          symm
          refine Finset.sum_bij (fun (x : ι2) _ => x.1) ?_ ?_ ?_ ?_
          · intro x _; simp [x.2]
          · intro x1 _ x2 _ h; exact Subtype.ext h
          · intro i hi
            simp only [Finset.mem_compl, Finset.mem_singleton] at hi
            exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        have hA1_split : ∀ (f : (ι1 → F) → ℤ),
            ∑ yr ∈ A1, f yr = (∑ z ∈ A2 0, f (lift2 0 z)) + (∑ z ∈ A2 1, f (lift2 1 z)) := by
          intro f
          have hpart : ∑ yr ∈ A1, f yr =
              (∑ yr ∈ A1.filter (fun yr => yr p1' = 0), f yr) +
              (∑ yr ∈ A1.filter (fun yr => yr p1' ≠ 0), f yr) :=
            (Finset.sum_filter_add_sum_filter_not A1 (fun yr => yr p1' = 0) f).symm
          rw [hpart]
          have hbij : ∀ (β : F),
              ∑ yr ∈ A1.filter (fun yr => yr p1' = β), f yr = ∑ z ∈ A2 β, f (lift2 β z) := by
            intro β
            symm
            refine Finset.sum_bij (fun z _ => lift2 β z) ?_ ?_ ?_ ?_
            · intro z hz
              simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and] at hz
              simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨fun r => ?_, by simp [lift2]⟩
              rw [hsum1_split]
              have hval1 : lift2 β z p1' = β := by simp [lift2]
              have hval2 : ∀ x : ι2, lift2 β z x.1 = z x := fun x => by simp [lift2, x.2]
              rw [hval1]
              simp_rw [hval2]
              have hzr := hz r
              dsimp [eqs2] at hzr
              rw [hzr]
              calc (eqs1 r).1 p1' * β + ((eqs1 r).2 + (eqs1 r).1 p1' * β)
                  = (eqs1 r).2 + ((eqs1 r).1 p1' * β + (eqs1 r).1 p1' * β) := by ring
                _ = (eqs1 r).2 := by rw [zmod2_add_self, add_zero]
            · intro z1 _ z2 _ h
              funext x
              have := congrFun h x.1
              simpa [lift2, x.2] using this
            · intro yr hyr
              simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and] at hyr
              let z : ι2 → F := fun x => yr x.1
              have hz_mem : z ∈ A2 β := by
                simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and]
                intro r
                have hr := hyr.1 r
                rw [hsum1_split, hyr.2] at hr
                dsimp [eqs2, z]
                calc ∑ x : ι2, (eqs1 r).1 x.1 * yr x.1
                    = ((eqs1 r).1 p1' * β + ∑ x : ι2, (eqs1 r).1 x.1 * yr x.1) + (eqs1 r).1 p1' * β := by
                      rw [add_comm ((eqs1 r).1 p1' * β), add_assoc, zmod2_add_self, add_zero]
                  _ = (eqs1 r).2 + (eqs1 r).1 p1' * β := by rw [hr]
              refine ⟨z, hz_mem, ?_⟩
              funext x
              dsimp [lift2, z]
              split_ifs with hx
              · subst hx; exact hyr.2.symm
              · rfl
            · intro _ _; rfl
          have hne_eq : A1.filter (fun yr => yr p1' ≠ 0) = A1.filter (fun yr => yr p1' = 1) := by
            ext yr
            simp only [Finset.mem_filter]
            exact ⟨fun ⟨h1, h2⟩ => ⟨h1, zmod2_eq_one_of_ne_zero h2⟩,
                   fun ⟨h1, h2⟩ => ⟨h1, by rw [h2]; decide⟩⟩
          rw [hne_eq, hbij 0, hbij 1]
        have hcardA1 : A1.card = (A2 0).card + (A2 1).card := by
          have h1 := hA1_split (fun _ => (1 : ℤ))
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
          omega

        let m' := m - 1
        have hm' : m' + 1 = m := Nat.sub_add_cancel hm1
        let i0' : Fin (m' + 1) := Fin.cast hm'.symm i0
        let skipIdx : Fin m' ↪ Fin m :=
          ⟨fun j => Fin.cast hm' (i0'.succAbove j),
           fun j1 j2 h => Fin.succAbove_right_injective (p := i0') (Fin.cast_injective hm' h)⟩
        have hskip_ne : ∀ j : Fin m', skipIdx j ≠ i0 := by
          intro j h
          have h' : i0'.succAbove j = i0' := by
            apply Fin.cast_injective hm'
            change Fin.cast hm' (i0'.succAbove j) = i0 at h
            rw [h]; simp [i0']
          exact Fin.succAbove_ne i0' j h'
        let pos2 : Fin m' × Fin 3 ↪ ι2 :=
          ⟨fun q => ⟨⟨pos (skipIdx q.1, q.2), fun h => by
            rw [← hpos0] at h
            exact hskip_ne q.1 (Prod.mk.inj (pos.injective h)).1⟩, fun h => by
            have h' : pos (skipIdx q.1, q.2) = pos (i0, t1) := congrArg Subtype.val h
            exact hskip_ne q.1 (Prod.mk.inj (pos.injective h')).1⟩,
           fun q1 q2 h => by
            have h1 : pos (skipIdx q1.1, q1.2) = pos (skipIdx q2.1, q2.2) :=
              congrArg (fun x : ι2 => x.1.1) h
            have h2 := pos.injective h1
            exact Prod.ext (skipIdx.injective (Prod.mk.inj h2).1) (Prod.mk.inj h2).2⟩
        let Q2 (β : F) (z : ι2 → F) : F :=
          Q (lift (lift2 β z)) + L (lift2 β z) * β * z ⟨p2', hp12'⟩
        have hQ2 : ∀ β : F, IsQuad (Q2 β) := by
          intro β
          have hlift2_aff : ∀ x : ι1, IsAffine (fun z : ι2 → F => lift2 β z x) := by
            intro x
            dsimp [lift2]
            split_ifs with hx
            · exact ⟨fun _ => 0, β, fun _ => by simp⟩
            · exact ⟨fun w => if w = ⟨x, hx⟩ then 1 else 0, 0, fun z => by simp⟩
          have hQ_part : IsQuad (fun z => Q (lift (lift2 β z))) :=
            isQuad_comp_affine hQ1 hlift2_aff
          have hL_part : IsAffine (fun z => L (lift2 β z) * β) := by
            refine ⟨fun w => v w.1.1 * β, (γ + v p1'.1 * β) * β, fun z => ?_⟩
            dsimp only [L]
            rw [hsum1_split]
            have h1 : lift2 β z p1' = β := by simp [lift2]
            have h2 : ∀ w : ι2, lift2 β z w.1 = z w := fun w => by simp [lift2, w.2]
            rw [h1]
            simp_rw [h2]
            rw [add_mul, add_mul, Finset.sum_mul]
            have h3 : (∑ w : ι2, v w.1.1 * z w * β) = ∑ w : ι2, v w.1.1 * β * z w :=
              Finset.sum_congr rfl (fun w _ => by ring)
            rw [h3]; ring
          have hz_aff : IsAffine (fun z : ι2 → F => z ⟨p2', hp12'⟩) :=
            ⟨fun w => if w = ⟨p2', hp12'⟩ then 1 else 0, 0, fun z => by simp⟩
          exact isQuad_add hQ_part (isQuad_mul_affine hL_part hz_aff)
        have hg_split : ∀ (β : F) (z : ι2 → F),
            Q (lift (lift2 β z)) +
              (∑ i : Fin m, lift (lift2 β z) (pos (i, 0)) * lift (lift2 β z) (pos (i, 1)) * lift (lift2 β z) (pos (i, 2))) =
            Q2 β z + ∑ j : Fin m', z (pos2 (j, 0)) * z (pos2 (j, 1)) * z (pos2 (j, 2)) := by
          intro β z
          let y := lift (lift2 β z)
          have hsum_i : ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)) =
              y (pos (i0, 0)) * y (pos (i0, 1)) * y (pos (i0, 2)) +
              ∑ j : Fin m', y (pos (skipIdx j, 0)) * y (pos (skipIdx j, 1)) * y (pos (skipIdx j, 2)) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
            congr 1
            symm
            refine Finset.sum_bij (fun j _ => skipIdx j) ?_ ?_ ?_ ?_
            · intro j _; exact Finset.mem_erase.mpr ⟨hskip_ne j, Finset.mem_univ _⟩
            · intro j1 _ j2 _ h; exact skipIdx.injective h
            · intro i hi
              have hne : Fin.cast hm'.symm i ≠ i0' := fun h =>
                (Finset.mem_erase.mp hi).1 (by
                  have h1 := congrArg (Fin.cast hm') h
                  simpa [i0'] using h1)
              obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
              refine ⟨j, Finset.mem_univ _, ?_⟩
              show Fin.cast hm' (i0'.succAbove j) = i
              rw [hj]; simp
            · intro _ _; rfl
          rw [hsum_i, htriple_prod y]
          have hy0 : y (pos (i0, t0)) = L (lift2 β z) := by
            dsimp [y]; rw [hpos0, hlift_p]
          have hy1 : y (pos (i0, t1)) = β := by
            dsimp [y]
            have : lift (lift2 β z) p1'.1 = lift2 β z p1' := hlift_ne (lift2 β z) p1'
            change lift (lift2 β z) p1'.1 = β
            rw [this]; simp [lift2]
          have hy2 : y (pos (i0, t2)) = z ⟨p2', hp12'⟩ := by
            dsimp [y]
            have : lift (lift2 β z) p2'.1 = lift2 β z p2' := hlift_ne (lift2 β z) p2'
            change lift (lift2 β z) p2'.1 = z ⟨p2', hp12'⟩
            rw [this]; simp [lift2, hp12']
          have hrest : ∀ j : Fin m', ∀ t : Fin 3, y (pos (skipIdx j, t)) = z (pos2 (j, t)) := by
            intro j t
            dsimp [y]
            have h1 : lift (lift2 β z) (pos2 (j, t)).1.1 = lift2 β z (pos2 (j, t)).1 :=
              hlift_ne (lift2 β z) (pos2 (j, t)).1
            change lift (lift2 β z) (pos2 (j, t)).1.1 = z (pos2 (j, t))
            rw [h1]; simp [lift2, (pos2 (j, t)).2]
          rw [hy0, hy1, hy2]
          simp_rw [hrest]
          dsimp [Q2]; ring
        have hsub : m' - c = m - (c + 1) := by dsimp [m']; omega
        have hih0 := ih m' pos2 (Q2 0) (hQ2 0) (eqs2 0)
        have hih1 := ih m' pos2 (Q2 1) (hQ2 1) (eqs2 1)
        rw [hsub] at hih0 hih1
        rw [hlift_bij, hA1_split, hcardA, hcardA1]
        let S0 : ℤ := ∑ z ∈ A2 0, chi (Q2 0 z + ∑ j : Fin m', z (pos2 (j, 0)) * z (pos2 (j, 1)) * z (pos2 (j, 2)))
        let S1 : ℤ := ∑ z ∈ A2 1, chi (Q2 1 z + ∑ j : Fin m', z (pos2 (j, 0)) * z (pos2 (j, 1)) * z (pos2 (j, 2)))
        have hsum0 : (∑ z ∈ A2 0, chi (Q (lift (lift2 0 z)) +
            ∑ i : Fin m, lift (lift2 0 z) (pos (i, 0)) * lift (lift2 0 z) (pos (i, 1)) * lift (lift2 0 z) (pos (i, 2)))) = S0 :=
          Finset.sum_congr rfl (fun z _ => by rw [hg_split 0 z])
        have hsum1 : (∑ z ∈ A2 1, chi (Q (lift (lift2 1 z)) +
            ∑ i : Fin m, lift (lift2 1 z) (pos (i, 0)) * lift (lift2 1 z) (pos (i, 1)) * lift (lift2 1 z) (pos (i, 2)))) = S1 :=
          Finset.sum_congr rfl (fun z _ => by rw [hg_split 1 z])
        rw [hsum0, hsum1]
        calc 4 ^ (m - (c + 1)) * (S0 + S1).natAbs
            ≤ 4 ^ (m - (c + 1)) * (S0.natAbs + S1.natAbs) :=
              Nat.mul_le_mul_left _ (Int.natAbs_add_le S0 S1)
          _ = 4 ^ (m - (c + 1)) * S0.natAbs + 4 ^ (m - (c + 1)) * S1.natAbs := Nat.mul_add _ _ _
          _ ≤ (A2 0).card * 3 ^ (m - (c + 1)) + (A2 1).card * 3 ^ (m - (c + 1)) :=
              Nat.add_le_add hih0 hih1
          _ = ((A2 0).card + (A2 1).card) * 3 ^ (m - (c + 1)) := by ring
      · let pos1 : Fin m × Fin 3 ↪ ι1 :=
          ⟨fun q => ⟨pos q, fun h => hp_in ⟨q.1, q.2, h⟩⟩,
           fun q1 q2 h => pos.injective (congrArg Subtype.val h)⟩
        rw [hlift_bij, hcardA]
        have hsum_eq : (∑ yr ∈ A1, chi (Q (lift yr) +
            ∑ i : Fin m, lift yr (pos (i, 0)) * lift yr (pos (i, 1)) * lift yr (pos (i, 2)))) =
            ∑ yr ∈ A1, chi (Q (lift yr) + ∑ i : Fin m, yr (pos1 (i, 0)) * yr (pos1 (i, 1)) * yr (pos1 (i, 2))) := by
          apply Finset.sum_congr rfl; intro yr _
          congr 2; apply Finset.sum_congr rfl; intro i _
          have h0 : lift yr (pos (i, 0)) = yr (pos1 (i, 0)) := hlift_ne yr (pos1 (i, 0))
          have h1 : lift yr (pos (i, 1)) = yr (pos1 (i, 1)) := hlift_ne yr (pos1 (i, 1))
          have h2 : lift yr (pos (i, 2)) = yr (pos1 (i, 2)) := hlift_ne yr (pos1 (i, 2))
          rw [h0, h1, h2]
        rw [hsum_eq]
        exact pow_three_four_mono (by omega : m - (c + 1) ≤ m - c) _ _ (ih m pos1 (fun yr => Q (lift yr)) hQ1 eqs1)


end Pinned29766

theorem pinned_fiber_bound : FiberBound := Pinned29766.cubic_fiber_bound

/-- Global agreement bias, obtained by averaging a bound on every translate of the
same cube. The cube can contain unused coordinates. -/
theorem adaptive_hits_bound {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [AddCommGroup W] [Module F W]
    {m h : ℕ} (pos : Fin m × Fin 3 ↪ ι) (E : (ι → F) →ₗ[F] W)
    (test : Fin h → ℕ → W →ₗ[F] F)
    (target : W → F) (out : ℕ → W → F) (hout : ∀ t, Van3 (out t))
    (htarget : ∀ b : W, ∃ Q : (ι → F) → F,
      Van3 Q ∧ ∀ y, target (E y + b) = Q y + cubic pos y) :
    let run := fun w => (List.finRange h).foldl (fun t j =>
      2 * t + (if test j t w = 0 then 0 else 1)) (0 : ℕ)
    4 ^ (m - h) *
      ((2 : ℤ) * (Nat.card {w : W // target w = out (run w) w} : ℤ) -
        (Fintype.card W : ℤ)).natAbs ≤ Fintype.card W * 3 ^ (m - h) := by
  let run := fun w => runList (fun j t => test j t) (List.finRange h) w
  let result := fun w => out (run w) w
  change 4 ^ (m - h) *
      ((2 : ℤ) * (Nat.card {w : W // target w = result w} : ℤ) -
        (Fintype.card W : ℤ)).natAbs ≤ _
  rw [← sum_sign_eq_hits target result]
  apply bound_of_all_translates E (fun w => sign (target w - result w))
  intro b
  obtain ⟨Q, hQ, hrepr⟩ := htarget b
  simpa only [List.length_finRange, result, run, add_comm b] using
    (adaptive_cube_bound pinned_fiber_bound pos E b test (List.finRange h) target out hout Q hQ hrepr)

end
end PEqualNP.Outside.L_meta_32055_aux.Leaves

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_32055_aux.Average

private theorem absGap_le {N m : ℕ} (hm : m ≤ N) :
    ((2 : ℤ) * (m : ℤ) - (N : ℤ)).natAbs ≤ N := by
  rw [show (2 : ℤ) * (m : ℤ) = ((2*m : ℕ) : ℤ) by simp]
  by_cases h : N ≤ 2*m
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : 2*m ≤ N)]
    omega

private theorem untruncate {h a g N : ℕ} (hg : g ≤ N)
    (hp : 4^(a-h) * g ≤ 3^(a-h) * N) :
    3^h * 4^a * g ≤ 4^h * 3^a * N := by
  by_cases ha : h ≤ a
  · have e : a = (a-h)+h := by omega
    calc
      3^h * 4^a * g = (3^h * 4^h) * (4^(a-h) * g) := by
        conv_lhs => rw [e, pow_add]
        ac_rfl
      _ ≤ (3^h * 4^h) * (3^(a-h) * N) := Nat.mul_le_mul_left _ hp
      _ = 4^h * 3^a * N := by
        conv_rhs => rw [e, pow_add]
        ac_rfl
  · have e : h = (h-a)+a := by omega
    have hl : 3^(h-a) ≤ 4^(h-a) := Nat.pow_le_pow_left (by decide) _
    calc
      3^h * 4^a * g = (3^a * 4^a) * (3^(h-a) * g) := by
        conv_lhs => rw [e, pow_add]
        ac_rfl
      _ ≤ (3^a * 4^a) * (4^(h-a) * N) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hl hg)
      _ = 4^h * 3^a * N := by
        conv_rhs => rw [e, pow_add]
        ac_rfl

private def pairWeight (v : ZMod 2 × ZMod 2) : ℕ :=
  if v = 0 then 4 else 3

private theorem pairWeight_sum : ∑ v : ZMod 2 × ZMod 2, pairWeight v = 13 := by
  decide

private theorem pairWeight_prod_sum (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (∑ v : ι → ZMod 2 × ZMod 2, ∏ i, pairWeight (v i)) = 13^Fintype.card ι := by
  classical
  simpa only [Fintype.piFinset_univ, pairWeight_sum, Finset.prod_const, Finset.card_univ]
    using (Finset.sum_prod_piFinset (ι := ι) Finset.univ fun _ => pairWeight)

private noncomputable def pairFiberEquiv {W ι : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P : W →ₗ[ZMod 2] (ι → ZMod 2 × ZMod 2)) (hP : Function.Surjective P) :
    W ≃ (ι → ZMod 2 × ZMod 2) × P.ker := by
  let lift : (ι → ZMod 2 × ZMod 2) → W := fun v => Classical.choose (hP v)
  have hl (v : ι → ZMod 2 × ZMod 2) : P (lift v) = v := Classical.choose_spec (hP v)
  refine
    { toFun := fun d => (P d, ⟨d - lift (P d), by simp [hl]⟩)
      invFun := fun v => v.2.1 + lift v.1
      left_inv := fun d => sub_add_cancel ..
      right_inv := ?_ }
  rintro ⟨v, z⟩
  have hz : P z.1 = 0 := z.2
  simp [hz, hl]

private theorem weight_eq (ι : Type*) [Fintype ι] (v : ι → ZMod 2 × ZMod 2) :
    let a := (Finset.univ.filter fun i => v i ≠ 0).card
    4^Fintype.card ι = 4^a * 4^(Fintype.card ι-a) ∧
    (∏ i, pairWeight (v i)) = 3^a * 4^(Fintype.card ι-a) := by
  dsimp only
  let p : ι → Prop := fun i => v i ≠ 0
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι)) p
  have hh : Fintype.card ι - (Finset.univ.filter p).card =
      (Finset.univ.filter fun i => ¬ p i).card := by
    rw [Finset.card_univ] at hc
    omega
  change 4^Fintype.card ι = 4^(Finset.univ.filter p).card * 4^_ ∧ _ =
    3^(Finset.univ.filter p).card * 4^_
  rw [hh, ← pow_add, hc, Finset.card_univ]
  refine ⟨rfl, ?_⟩
  have hval (i : ι) : pairWeight (v i) = if p i then 3 else 4 := by
    simp [pairWeight, p, ite_not]
  simp only [hval, Finset.prod_ite, Finset.prod_const]

/-- A surjective array of tap pairs of linear forms has equally sized fibers. -/
theorem averageOfSurjectiveTapPairs {W ι : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype W] [Fintype ι] (P : W →ₗ[ZMod 2] (ι → ZMod 2 × ZMod 2))
    (hP : Function.Surjective P) (N h : ℕ) (hN : Fintype.card W = N)
    (active gap : W → ℕ)
    (hactive : ∀ d, active d = (Finset.univ.filter fun i => P d i ≠ 0).card)
    (hgap : ∀ d, gap d ≤ N)
    (hpoint : ∀ d, 4^(active d-h) * gap d ≤ 3^(active d-h) * N) :
    3^h * 16^Fintype.card ι * (∑ d, gap d) ≤ 4^h * 13^Fintype.card ι * N^2 := by
  classical
  let n := Fintype.card ι
  let weight (v : ι → ZMod 2 × ZMod 2) := ∏ i, pairWeight (v i)
  let e := pairFiberEquiv P hP
  let K := Fintype.card P.ker
  have hy : Fintype.card (ι → ZMod 2 × ZMod 2) = 4^n := by
    simp [n]
  have hKN : 4^n * K = N := by
    rw [← hN, Fintype.card_congr e, Fintype.card_prod, hy]
  have hsw : (∑ d : W, weight (P d)) = K * 13^n := by
    calc
      (∑ d : W, weight (P d)) = ∑ v : (ι → ZMod 2 × ZMod 2) × P.ker, weight v.1 :=
        e.sum_comp (fun v => weight v.1)
      _ = (∑ v : ι → ZMod 2 × ZMod 2, K * weight v) := by
        rw [Fintype.sum_prod_type]
        simp [K]
      _ = K * 13^n := by rw [← Finset.mul_sum, pairWeight_prod_sum]
  have hp (d : W) : 3^h * 4^n * gap d ≤ 4^h * N * weight (P d) := by
    have hd := untruncate (hgap d) (hpoint d)
    obtain ⟨hw₁, hw₂⟩ := weight_eq ι (P d)
    rw [← hactive d] at hw₁ hw₂
    change 4^n = _ at hw₁
    change weight (P d) = _ at hw₂
    rw [hw₁, hw₂]
    calc
      _ = 4^(n-active d) * (3^h * 4^active d * gap d) := by ac_rfl
      _ ≤ 4^(n-active d) * (4^h * 3^active d * N) := Nat.mul_le_mul_left _ hd
      _ = _ := by ac_rfl
  have hs : 3^h * 4^n * (∑ d, gap d) ≤ 4^h * N * (K * 13^n) := by
    rw [← hsw, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun d _ => hp d
  calc
    3^h * 16^n * (∑ d, gap d) = 4^n * (3^h * 4^n * (∑ d, gap d)) := by
      rw [show (16 : ℕ) = 4*4 by decide, mul_pow]
      ac_rfl
    _ ≤ 4^n * (4^h * N * (K * 13^n)) := Nat.mul_le_mul_left _ hs
    _ = 4^h * 13^n * N^2 := by
      rw [pow_two, ← hKN]
      ac_rfl

private def tap32055 {k : ℕ} (hk : 0 < k) (w : Fin k → ZMod 2) (j : ℕ) : ZMod 2 :=
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) =>
    x i + x (ix (i.val + s)) + x (ix (i.val + k - s % k))
  mix 2 (rot 3 w) (ix j)

private def tapPairs {k : ℕ} (hk : 0 < k) (S : Finset (Fin k)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2 × ZMod 2) where
  toFun d i := (tap32055 hk d (i.val.val+1), tap32055 hk d (i.val.val+5))
  map_add' x y := by
    funext i
    apply Prod.ext <;> simp [tap32055, Pi.add_apply] <;> abel
  map_smul' a x := by
    funext i
    apply Prod.ext <;> simp [tap32055, Pi.smul_apply, mul_add]

private theorem wrap_sub {k a x y : ℕ} (ha : a ≤ k) (e : x ≡ y [MOD k]) :
    x+k-a ≡ y+k-a [MOD k] :=
  (e.add_right k).sub (by omega) (by omega) .rfl

private theorem tap_normalize {k : ℕ} (hk : 0 < k) (hk21 : 21 ≤ k)
    (w : Fin k → ZMod 2) (j : ℕ) :
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    tap32055 hk w j = w (ix (j+k-3)) + w (ix (j+k-1)) + w (ix (j+k-5)) := by
  dsimp [tap32055]
  rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_eq_of_lt (by omega : 3 < k)]
  have hA := wrap_sub (a := 3) (by omega) (Nat.mod_modEq j k)
  have hB : ((j%k+2)%k+k-3) ≡ j+k-1 [MOD k] := by
    have t := (Nat.mod_modEq (j%k+2) k).trans ((Nat.mod_modEq j k).add_right 2)
    convert wrap_sub (a := 3) (by omega) t using 1
    omega
  have hC : ((j%k+k-2)%k+k-3) ≡ j+k-5 [MOD k] := by
    have t := (Nat.mod_modEq (j%k+k-2) k).trans (wrap_sub (a := 2) (by omega) (Nat.mod_modEq j k))
    have t' := wrap_sub (a := 3) (by omega) t
    rw [show j+k-2+k-3 = (j+k-5)+k by omega] at t'
    exact t'.trans (Nat.add_mod_right (j+k-5) k)
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  change w (ix (j%k+k-3)) + w (ix ((j%k+2)%k+k-3)) + w (ix ((j%k+k-2)%k+k-3)) =
    w (ix (j+k-3)) + w (ix (j+k-1)) + w (ix (j+k-5))
  have hi {a b : ℕ} (e : a ≡ b [MOD k]) : ix a = ix b := Fin.ext e
  rw [hi hA, hi hB, hi hC]

private theorem noOverlapOfLT {k x y a b : ℕ} (hy : y < k)
    (hxy : x < y) (ha : a ≤ 8) (hb : b ≤ 8)
    (hf : 21 ≤ (y+k-x)%k) (hr : 21 ≤ (x+k-y)%k)
    (h : x+a ≡ y+b [MOD k]) : False := by
  rw [show y+k-x = (y-x)+k by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega : y-x < k)] at hf
  rw [Nat.mod_eq_of_lt (by omega : x+k-y < k)] at hr
  rw [show y+b = x+(y-x+b) by omega] at h
  have hh : a ≡ y-x+b [MOD k] := h.add_left_cancel' x
  change a % k = (y-x+b)%k at hh
  rw [Nat.mod_eq_of_lt (by omega : a < k), Nat.mod_eq_of_lt (by omega : y-x+b < k)] at hh
  omega

private def coord {k : ℕ} (hk : 0 < k) {S : Finset (Fin k)} (it : S × Fin 5) : Fin k :=
  ⟨(it.1.val.val + k + 2*it.2.val - 4) % k, Nat.mod_lt _ hk⟩

private theorem coord_injective {k : ℕ} (hk : 0 < k) (hk21 : 21 ≤ k) (S : Finset (Fin k))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 21 ≤ (j.val+k-i.val)%k) :
    Function.Injective (coord hk (S := S)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hi := i.val.isLt
  have hj := j.val.isLt
  have ha := a.isLt
  have hb := b.isLt
  have h₀ : i.val.val+k+2*a.val-4 ≡ j.val.val+k+2*b.val-4 [MOD k] := congrArg Fin.val h
  have h₁ := h₀.add_right 4
  rw [show i.val.val+k+2*a.val-4+4 = (i.val.val+2*a.val)+k by omega,
    show j.val.val+k+2*b.val-4+4 = (j.val.val+2*b.val)+k by omega] at h₁
  have h₂ := h₁.add_right_cancel' k
  have hij : i.val = j.val := by
    by_contra hne
    have hf := hS i i.2 j j.2 hne
    have hr := hS j j.2 i i.2 (Ne.symm hne)
    have hnev : i.val.val ≠ j.val.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hnev with hh | hh
    · exact noOverlapOfLT hj hh (by omega) (by omega) hf hr h₂
    · exact noOverlapOfLT hi hh (by omega) (by omega) hr hf h₂.symm
  rw [hij] at h₂
  have h₃ := h₂.add_left_cancel' j.val.val
  change (2*a.val)%k = (2*b.val)%k at h₃
  rw [Nat.mod_eq_of_lt (by omega : 2*a.val < k), Nat.mod_eq_of_lt (by omega : 2*b.val < k)] at h₃
  refine Prod.ext (Subtype.ext hij) (Fin.ext ?_)
  change a.val = b.val
  omega

private theorem tapPairs_surjective {k : ℕ} (hk : 0 < k) (hk21 : 21 ≤ k) (S : Finset (Fin k))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 21 ≤ (j.val+k-i.val)%k) :
    Function.Surjective (tapPairs hk S) := by
  intro v
  let g : S × Fin 5 → ZMod 2 := fun (i, a) =>
    if a = 0 then (v i).1 else if a = 4 then (v i).2 else 0
  let d := Function.extend (coord hk (S := S)) g (fun _ => 0)
  have hval (i : S) (a : Fin 5) : d (coord hk (i,a)) = g (i,a) :=
    (coord_injective hk hk21 S hS).extend_apply g _ _
  refine ⟨d, ?_⟩
  funext i
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  have hc (m : ℕ) (a : Fin 5) (hm : m = i.val.val+k+2*a.val-4) :
      ix m = coord hk (i,a) := by subst m; rfl
  have eq1 : tap32055 hk d (i.val.val+1) =
      d (coord hk (i,1)) + d (coord hk (i,2)) + d (coord hk (i,0)) := by
    rw [tap_normalize hk hk21]
    change d (ix (i.val.val+1+k-3)) + d (ix (i.val.val+1+k-1)) +
      d (ix (i.val.val+1+k-5)) = _
    rw [hc _ 1 (by change i.val.val+1+k-3 = i.val.val+k+2-4; omega),
      hc _ 2 (by change i.val.val+1+k-1 = i.val.val+k+4-4; omega),
      hc _ 0 (by change i.val.val+1+k-5 = i.val.val+k-4; omega)]
  have eq2 : tap32055 hk d (i.val.val+5) =
      d (coord hk (i,3)) + d (coord hk (i,4)) + d (coord hk (i,2)) := by
    rw [tap_normalize hk hk21]
    change d (ix (i.val.val+5+k-3)) + d (ix (i.val.val+5+k-1)) +
      d (ix (i.val.val+5+k-5)) = _
    rw [hc _ 3 (by change i.val.val+5+k-3 = i.val.val+k+6-4; omega),
      hc _ 4 (by change i.val.val+5+k-1 = i.val.val+k+8-4; omega),
      hc _ 2 (by change i.val.val+5+k-5 = i.val.val+k+4-4; omega)]
  change (tap32055 hk d (i.val.val+1), tap32055 hk d (i.val.val+5)) = v i
  rw [eq1, eq2]
  simp [hval, g, show (1 : Fin 5) ≠ 0 by decide, show (1 : Fin 5) ≠ 4 by decide,
    show (2 : Fin 5) ≠ 0 by decide, show (2 : Fin 5) ≠ 4 by decide,
    show (3 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 4 by decide,
    show (4 : Fin 5) ≠ 0 by decide]

theorem averageTap {k : ℕ} (hk : 0 < k) (hk21 : 21 ≤ k) (S : Finset (Fin k))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 21 ≤ (j.val+k-i.val)%k)
    (h : ℕ) (isHit : (Fin k → ZMod 2) → (Fin k → ZMod 2) → Prop) :
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) => x (ix (i.val + k - s % k))
    let mix := fun (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) =>
      x i + x (ix (i.val + s)) + x (ix (i.val + k - s % k))
    let tap := fun (w : Fin k → ZMod 2) (j : ℕ) => mix 2 (rot 3 w) (ix j)
    let active := fun d : Fin k → ZMod 2 => (S.filter fun i =>
      tap d (i.val+1) ≠ 0 ∨ tap d (i.val+5) ≠ 0).card
    let hits := fun d : Fin k → ZMod 2 => Nat.card {w : Fin k → ZMod 2 // isHit d w}
    let gap := fun d : Fin k → ZMod 2 => ((2 : ℤ) * (hits d : ℤ) - (2 : ℤ)^k).natAbs
    (∀ d, 4^(active d-h) * gap d ≤ 3^(active d-h) * 2^k) →
    3^h * 16^S.card * (∑ d, gap d) ≤ 4^h * 13^S.card * (2^k)^2 := by
  intro ix rot mix tap active hits gap hpoint
  have hN : Fintype.card (Fin k → ZMod 2) = 2^k := by simp
  have hgap (d) : gap d ≤ 2^k := by
    dsimp [gap]
    have hh : hits d ≤ 2^k :=
      (Finite.card_subtype_le (isHit d)).trans_eq (Nat.card_eq_fintype_card.trans hN)
    exact_mod_cast absGap_le hh
  have hactive (d) : active d = (Finset.univ.filter fun i : S => tapPairs hk S d i ≠ 0).card := by
    let p : Fin k → Prop := fun i => tap d (i.val+1) ≠ 0 ∨ tap d (i.val+5) ≠ 0
    have hp (i : S) : tapPairs hk S d i ≠ 0 ↔ p i.val := by
      change (tap d (i.val.val+1), tap d (i.val.val+5)) ≠ (0,0) ↔ p i.val
      by_cases h₁ : tap d (i.val.val+1) = 0 <;>
        by_cases h₂ : tap d (i.val.val+5) = 0 <;> simp [p, h₁, h₂]
    calc
      active d = (S.filter p).card := rfl
      _ = (S.attach.filter fun i : S => p i.val).card := by
        have he := congrArg Finset.card (Finset.filter_attach p S)
        rw [Finset.card_map, Finset.card_attach] at he
        exact he.symm
      _ = _ := by
        rw [Finset.univ_eq_attach]
        congr 1
        exact Finset.filter_congr fun i _ => (hp i).symm
  simpa only [Fintype.card_coe] using
    averageOfSurjectiveTapPairs (tapPairs hk S) (tapPairs_surjective hk hk21 S hS)
      (2^k) h hN active gap hactive hgap hpoint

end PEqualNP.Outside.L_meta_32055_aux.Average

-- Degree and round decomposition adapted from upstream e5eb43659fdc210299daa288589367628e7185e7, lean/PEqualNP/Outside/L_meta_29718.lean.
namespace PEqualNP.Outside.L_meta_32055_aux

section Differences

variable {W R : Type} [AddCommGroup W] [CommRing R]

private def delta (f : W → R) (u x : W) : R := f (x + u) - f x

private def differences (f : W → R) (directions : List W) : W → R :=
  directions.foldl delta f

private def degree : ℕ → (W → R) → Prop
  | 0, f => ∀ u x, delta f u x = 0
  | n + 1, f => ∀ u, degree n (delta f u)

private theorem degree_zero_const {f : W → R} (h : degree 0 f) (x : W) : f x = f 0 := by
  have hx := h x 0
  simpa [delta, sub_eq_zero] using hx

private theorem delta_add (f g : W → R) (u : W) :
    delta (fun x => f x + g x) u = fun x => delta f u x + delta g u x := by
  funext x
  unfold delta
  ring

private theorem delta_sub (f g : W → R) (u : W) :
    delta (fun x => f x - g x) u = fun x => delta f u x - delta g u x := by
  funext x
  unfold delta
  ring

private theorem delta_scale (c : R) (f : W → R) (u : W) :
    delta (fun x => c * f x) u = fun x => c * delta f u x := by
  funext x
  unfold delta
  ring

private theorem delta_shift (f : W → R) (u v : W) :
    delta (fun x => f (x + v)) u = fun x => delta f u (x + v) := by
  funext x
  simp only [delta, add_right_comm x u v]

private theorem delta_mul (f g : W → R) (u : W) :
    delta (fun x => f x * g x) u =
      fun x => delta f u x * g (x + u) + f x * delta g u x := by
  funext x
  unfold delta
  ring

private theorem degree_const (n : ℕ) (c : R) : degree n (fun _ : W => c) := by
  induction n generalizing c with
  | zero => intro u x; simp [delta]
  | succ n ih =>
    intro u
    have h : delta (fun _ : W => c) u = fun _ => 0 := by funext x; simp [delta]
    rw [h]
    exact ih 0

private theorem degree_add {n : ℕ} {f g : W → R}
    (hf : degree n f) (hg : degree n g) : degree n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero => intro u x; simpa [hf u x, hg u x] using congrFun (delta_add f g u) x
  | succ n ih =>
    intro u
    rw [delta_add]
    exact ih (hf u) (hg u)

private theorem degree_sub {n : ℕ} {f g : W → R}
    (hf : degree n f) (hg : degree n g) : degree n (fun x => f x - g x) := by
  induction n generalizing f g with
  | zero => intro u x; simpa [hf u x, hg u x] using congrFun (delta_sub f g u) x
  | succ n ih =>
    intro u
    rw [delta_sub]
    exact ih (hf u) (hg u)

private theorem degree_scale {n : ℕ} (c : R) {f : W → R}
    (hf : degree n f) : degree n (fun x => c * f x) := by
  induction n generalizing f with
  | zero => intro u x; simpa [hf u x] using congrFun (delta_scale c f u) x
  | succ n ih =>
    intro u
    rw [delta_scale]
    exact ih (hf u)

private theorem degree_shift {n : ℕ} (v : W) {f : W → R}
    (hf : degree n f) : degree n (fun x => f (x + v)) := by
  induction n generalizing f with
  | zero =>
    intro u x
    rw [delta_shift]
    exact hf u (x + v)
  | succ n ih =>
    intro u
    rw [delta_shift]
    exact ih (hf u)

private theorem degree_raise {n : ℕ} {f : W → R} (hf : degree n f) : degree (n + 1) f := by
  induction n generalizing f with
  | zero =>
    intro u v x
    change delta f u (x + v) - delta f u x = 0
    rw [hf u (x + v), hf u x, sub_self]
  | succ n ih => exact fun u => ih (hf u)

private theorem degree_mul {a b : ℕ} {f g : W → R}
    (hf : degree a f) (hg : degree b g) : degree (a + b) (fun x => f x * g x) := by
  induction a generalizing b f g with
  | zero =>
    have he : (fun x => f x * g x) = fun x => f 0 * g x := by
      funext x
      rw [degree_zero_const hf x]
    simpa only [Nat.zero_add, he] using degree_scale (f 0) hg
  | succ a ia =>
    induction b generalizing f g with
    | zero =>
      have he : (fun x => f x * g x) = fun x => g 0 * f x := by
        funext x
        rw [degree_zero_const hg x, mul_comm]
      simpa only [Nat.add_zero, he] using degree_scale (g 0) hf
    | succ b ib =>
      change degree (a + 1 + b + 1) _
      intro u
      rw [delta_mul]
      have h₁ := ia (hf u) (degree_shift u hg)
      have h₂ := ib hf (hg u)
      rw [show a + (b + 1) = a + 1 + b by omega] at h₁
      exact degree_add h₁ h₂

private theorem degree_sum {ι : Type} (s : Finset ι) {n : ℕ} (f : ι → W → R)
    (hf : ∀ i ∈ s, degree n (f i)) : degree n (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (degree_const n (0 : R) : degree n (fun _ : W => (0 : R)))
  | @insert i s hi ih =>
    have h := degree_add (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

private theorem degree_fold {f : W → R} (us : List W) (n : ℕ)
    (hf : degree (us.length + n) f) : degree n (differences f us) := by
  induction us generalizing f with
  | nil => simpa [differences] using hf
  | cons u us ih =>
    change degree n (differences (delta f u) us)
    apply ih
    rw [show (u :: us).length + n = (us.length + n) + 1 by simp; omega] at hf
    exact hf u

private theorem differences_sub (f g : W → R) (us : List W) (x : W) :
    differences (fun y => f y - g y) us x = differences f us x - differences g us x := by
  induction us generalizing f g with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f y - g y) u) us x = _
    rw [delta_sub, ih]
    rfl

private theorem differences_zero {f : W → R} (us : List W) {n : ℕ} (hu : us.length = n + 1)
    (hf : degree n f) (x : W) : differences f us x = 0 := by
  induction us generalizing n f with
  | nil => simp at hu
  | cons u us ih =>
    cases n with
    | zero =>
      have hnil : us = [] := List.length_eq_zero_iff.1 (by simpa using hu)
      subst us
      exact hf u x
    | succ n => exact ih (Nat.succ.inj hu) (hf u)

end Differences

abbrev Scalar := ZMod 2
abbrev Word (k : ℕ) := Fin k → Scalar

private def index {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

private def rotate {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x (index hk (i.val + k - s % k))

private def mix {k : ℕ} (hk : 0 < k) (g : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x i + x (index hk (i.val + g)) + x (index hk (i.val + k - g % k))

private def step {k : ℕ} (hk : 0 < k) (x : Word k) (i : Fin k) : Scalar :=
  x i + (1 + x (index hk (i.val + 1))) * x (index hk (i.val + 2))

private def gap (b : Bool) : ℕ := if b then 2 else 1

private def spin (b : Bool) : ℕ := if b then 3 else 1

private def linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x)

private def namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x + name b)

private def firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  step hk (namedInput hk name b x) + rotate hk (if b then 4 else 0) x + c₁ b

private def quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) (j : Fin k) : Scalar :=
  linearInput hk b x (index hk (j.val + 1)) * linearInput hk b x (index hk (j.val + 2))

private def outputWord {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (x : Word k) (b : Bool) : Word k :=
  step hk (mix hk (gap b) (firstRow hk name c₁ b x)) +
    rotate hk (if b then 7 else 2) x + c₂ b

private def topWord {k : ℕ} (hk : 0 < k) (x : Word k) (b : Bool) (i : Fin k) : Scalar :=
  mix hk (gap b) (quadratic hk b x) (index hk (i.val + 1)) *
    mix hk (gap b) (quadratic hk b x) (index hk (i.val + 2))

private theorem degree_coord {k : ℕ} (i : Fin k) : degree 1 (fun x : Word k => x i) := by
  intro u v x
  simp only [delta, Pi.add_apply]
  ring

private theorem degree_mix {k n : ℕ} (hk : 0 < k) (g : ℕ) (f : Word k → Word k)
    (hf : ∀ i, degree n (fun x => f x i)) (i : Fin k) :
    degree n (fun x => mix hk g (f x) i) :=
  degree_add (degree_add (hf i) (hf _)) (hf _)

private theorem mix_sub {k : ℕ} (hk : 0 < k) (g : ℕ) (f h : Word k) (i : Fin k) :
    mix hk g f i - mix hk g h i = mix hk g (f - h) i := by
  simp only [mix, Pi.sub_apply]
  ring

private theorem namedInput_eq {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k)
    (i : Fin k) : namedInput hk name b x i = linearInput hk b x i + mix hk (gap b) (name b) i := by
  simp only [namedInput, linearInput, mix, Pi.add_apply]
  ring

private theorem degree_linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => linearInput hk b x i) :=
  degree_mix hk _ _ (fun _ => degree_coord _) i

private theorem degree_namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => namedInput hk name b x i) := by
  simpa only [namedInput_eq] using
    degree_add (degree_linearInput hk b i) (degree_const 1 (mix hk (gap b) (name b) i))

private theorem degree_input_remainder {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 0 (fun x => namedInput hk name b x i - linearInput hk b x i) := by
  simp only [namedInput_eq, add_sub_cancel_left]
  exact degree_const 0 _

private theorem degree_quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => quadratic hk b x i) :=
  degree_mul (degree_linearInput hk b _) (degree_linearInput hk b _)

private theorem product_remainder {k n : ℕ} {a b a₀ b₀ : Word k → Scalar}
    (hb : degree (n + 1) b) (ha₀ : degree (n + 1) a₀)
    (ha : degree n (fun x => a x - a₀ x)) (hb' : degree n (fun x => b x - b₀ x)) :
    degree (n + (n + 1)) (fun x => (1 + a x) * b x - a₀ x * b₀ x) := by
  have hp := degree_mul (degree_add (degree_const n (1 : Scalar)) ha) hb
  have hq := degree_mul ha₀ hb'
  rw [Nat.add_comm (n + 1) n] at hq
  convert degree_add hp hq using 1
  funext x
  ring

private theorem degree_first_remainder {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 1 (fun x => firstRow hk name c₁ b x i - quadratic hk b x i) := by
  have hp := product_remainder (n := 0) (degree_namedInput hk name b (index hk (i.val + 2)))
    (degree_linearInput hk b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 2)))
  have hd := degree_add (degree_add (degree_add (degree_namedInput hk name b i) hp)
    (degree_coord (index hk (i.val + k - (if b then 4 else 0) % k)))) (degree_const 1 (c₁ b i))
  convert hd using 1
  funext x
  simp only [firstRow, step, quadratic, rotate, Pi.add_apply]
  ring

private theorem degree_firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => firstRow hk name c₁ b x i) := by
  simpa only [sub_add_cancel] using
    degree_add (degree_raise (degree_first_remainder hk name c₁ b i)) (degree_quadratic hk b i)

private theorem degree_output_remainder {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 3 (fun x => outputWord hk name c₁ c₂ x b i - topWord hk x b i) := by
  let y := fun x => mix hk (gap b) (firstRow hk name c₁ b x)
  let q := fun x => mix hk (gap b) (quadratic hk b x)
  have hy (j : Fin k) : degree 2 (fun x => y x j) :=
    degree_mix hk _ _ (degree_firstRow hk name c₁ b) j
  have hq (j : Fin k) : degree 2 (fun x => q x j) :=
    degree_mix hk _ _ (degree_quadratic hk b) j
  have hdiff (j : Fin k) : degree 1 (fun x => y x j - q x j) := by
    simpa only [y, q, mix_sub] using
      degree_mix hk (gap b) (fun x => firstRow hk name c₁ b x - quadratic hk b x)
        (degree_first_remainder hk name c₁ b) j
  have hp := product_remainder (n := 1) (hy (index hk (i.val + 2))) (hq (index hk (i.val + 1)))
    (hdiff (index hk (i.val + 1))) (hdiff (index hk (i.val + 2)))
  have hrotate := degree_raise (degree_raise
    (degree_coord (index hk (i.val + k - (if b then 7 else 2) % k))))
  have hd := degree_add (degree_add (degree_add (degree_raise (hy i)) hp) hrotate)
    (degree_const 3 (c₂ b i))
  convert hd using 1
  funext x
  simp only [outputWord, step, topWord, rotate, Pi.add_apply, y, q]
  ring

private theorem degree_topWord {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 4 (fun x => topWord hk x b i) :=
  degree_mul (degree_mix hk _ _ (degree_quadratic hk b) _)
    (degree_mix hk _ _ (degree_quadratic hk b) _)

private def observe {k : ℕ} (mask : Bool → Fin k → Scalar) (y : Bool → Word k) : Scalar :=
  (∑ i, mask false i * y false i) + (∑ i, mask true i * y true i)

private theorem observed_degree {k : ℕ} (hk : 0 < k) (mask : Bool → Fin k → Scalar) :
    degree 4 (fun x => observe mask (topWord hk x)) :=
  degree_add
    (degree_sum Finset.univ _ (fun i _ => degree_scale (mask false i) (degree_topWord hk false i)))
    (degree_sum Finset.univ _ (fun i _ => degree_scale (mask true i) (degree_topWord hk true i)))

private theorem observed_remainder {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k)
    (mask : Bool → Fin k → Scalar) :
    degree 3 (fun x => observe mask (outputWord hk name c₁ c₂ x) - observe mask (topWord hk x)) := by
  have h (b : Bool) := degree_sum Finset.univ _
    (fun i _ => degree_scale (mask b i) (degree_output_remainder hk name c₁ c₂ b i))
  convert degree_add (h false) (h true) using 1
  funext x
  simp only [observe, mul_sub, Finset.sum_sub_distrib]
  ring

private theorem observed_fourth {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k)
    (mask : Bool → Fin k → Scalar) (us : List (Word k)) (hlen : us.length = 4) (x : Word k) :
    differences (fun y => observe mask (outputWord hk name c₁ c₂ y)) us x =
      differences (fun y => observe mask (topWord hk y)) us 0 := by
  have h := differences_zero us hlen (observed_remainder hk name c₁ c₂ mask) x
  rw [differences_sub, sub_eq_zero] at h
  have hc := degree_fold us 0 (by simpa [hlen] using observed_degree hk mask)
  exact h.trans (degree_zero_const hc x)

private theorem degree_affine_comp {U V R : Type} [AddCommGroup U] [AddCommGroup V]
    [CommRing R] (L : U →+ V) (c : V) {f : V → R} (n : ℕ) (hf : degree n f) :
    degree n (fun y => f (c + L y)) := by
  have hd (g : V → R) (v : U) : delta (fun y => g (c + L y)) v =
      fun y => delta g (L v) (c + L y) := by
    funext y
    simp [delta, map_add, add_assoc]
  induction n generalizing f with
  | zero =>
    intro u x
    rw [hd]
    exact hf (L u) (c + L x)
  | succ n ih =>
    intro u
    rw [hd]
    exact ih (hf (L u))

private theorem bit_cases (a : Scalar) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem degree_two_coords {k : ℕ} (a b : Fin k) (g : Scalar → Scalar → Scalar) :
    degree 2 (fun w : Word k => g (w a) (w b)) := by
  have h (x y : Scalar) : g x y =
      g 0 0 + (g 1 0 - g 0 0) * x + (g 0 1 - g 0 0) * y +
        (g 1 1 - g 1 0 - g 0 1 + g 0 0) * (x*y) := by
    rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> ring
  have hd : degree 2 (fun w : Word k =>
      g 0 0 + (g 1 0 - g 0 0) * w a + (g 0 1 - g 0 0) * w b +
        (g 1 1 - g 1 0 - g 0 1 + g 0 0) * (w a * w b)) :=
    degree_add (degree_add (degree_add (degree_const 2 _)
      (degree_raise (degree_scale _ (degree_coord a))))
      (degree_raise (degree_scale _ (degree_coord b))))
      (degree_scale _ (degree_mul (degree_coord a) (degree_coord b)))
  convert hd using 1
  exact funext fun w => h (w a) (w b)

end PEqualNP.Outside.L_meta_32055_aux

namespace PEqualNP.Outside.L_meta_32055_aux

private theorem short_offset_inj {k : ℕ} (hk : 21 ≤ k) {a b : ℤ}
    (ha : -10 ≤ a) (hb : a ≤ 10) (hc : -10 ≤ b) (hd : b ≤ 10)
    (h : (a : ZMod k) = (b : ZMod k)) : a = b := by
  have hz : ((a-b : ℤ) : ZMod k) = 0 := by simp [Int.cast_sub, h]
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
  rcases lt_trichotomy z 0 with hn | he | hp
  · have hmul := mul_le_mul_of_nonneg_left (show z ≤ -1 by omega) (show 0 ≤ (k : ℤ) by positivity)
    simp at hmul
    omega
  · simp [he] at hz
    omega
  · have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ z by omega) (show 0 ≤ (k : ℤ) by positivity)
    simp at hmul
    omega

private theorem separated_short {k : ℕ} (hk : 21 ≤ k) (i j : Fin k)
    (hij : 21 ≤ (j.val + k - i.val) % k)
    (hji : 21 ≤ (i.val + k - j.val) % k) {d : ℤ} (hd₁ : -20 ≤ d) (hd₂ : d ≤ 20)
    (he : (j.val : ZMod k) - (i.val : ZMod k) = (d : ZMod k)) : False := by
  have hf (i j : Fin k) : (((j.val + k - i.val : ℕ) : ZMod k)) = (j.val : ZMod k) - (i.val : ZMod k) := by
    rw [Nat.cast_sub (by omega : i.val ≤ j.val + k), Nat.cast_add, ZMod.natCast_self, add_zero]
  have hsmall (i j : Fin k) (hlarge : 21 ≤ (j.val + k - i.val) % k)
      (e : ℕ) (hs : e ≤ 20) (heq : (j.val : ZMod k) - (i.val : ZMod k) = (e : ZMod k)) : False := by
    rw [← ZMod.val_natCast, hf, heq, ZMod.val_natCast_of_lt (by omega)] at hlarge
    omega
  by_cases h : 0 ≤ d
  · refine hsmall i j hij d.toNat (by omega) ?_
    rw [he, ← Int.cast_natCast, Int.toNat_of_nonneg h]
  · have hneg : (i.val : ZMod k) - (j.val : ZMod k) = ((-d : ℤ) : ZMod k) := by
      rw [Int.cast_neg, ← he, neg_sub]
    refine hsmall j i hji (-d).toNat (by omega) ?_
    rw [hneg, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]

private theorem nearby_sites_eq {k : ℕ} (hk : 21 ≤ k) (i j : Fin k)
    (hsep : i ≠ j → 21 ≤ (j.val + k - i.val) % k ∧ 21 ≤ (i.val + k - j.val) % k)
    (x : ZMod k) (a b p q : ℤ)
    (hab₁ : -10 ≤ a-b) (hab₂ : a-b ≤ 10)
    (hpq₁ : -10 ≤ p-q) (hpq₂ : p-q ≤ 10)
    (hi : x + (a : ZMod k) = (i.val : ZMod k) + (p : ZMod k))
    (hj : x + (b : ZMod k) = (j.val : ZMod k) + (q : ZMod k)) : i = j := by
  by_contra h
  obtain ⟨hij, hji⟩ := hsep h
  apply separated_short hk i j hij hji (d := b-a+p-q) (by omega) (by omega)
  push_cast
  linear_combination hi - hj

private theorem interval_spans_endpoints {k : ℕ} (hk : 21 ≤ k)
    (x y : ZMod k) (a b : ℤ) (ha : -5 ≤ a) (hb : b ≤ 5)
    (hab₁ : -10 ≤ b-a) (hab₂ : b-a ≤ 10)
    (hlo : x + (a : ZMod k) = y + ((-5 : ℤ) : ZMod k))
    (hhi : x + (b : ZMod k) = y + ((5 : ℤ) : ZMod k)) : x = y := by
  have heq : ((b-a : ℤ) : ZMod k) = ((10 : ℤ) : ZMod k) := by
    push_cast at *
    linear_combination hhi - hlo
  have hv := short_offset_inj hk hab₁ hab₂ (by omega) (by omega) heq
  have hv' : a = -5 := by omega
  rw [hv'] at hlo
  exact add_right_cancel hlo

private def offset {k : ℕ} [NeZero k] (i : Fin k) (o : ℤ) : Fin k :=
  ⟨((i.val : ZMod k) + (o : ZMod k)).val, ZMod.val_lt _⟩

private theorem offset_cast {k : ℕ} [NeZero k] (i : Fin k) (o : ℤ) :
    ((offset i o).val : ZMod k) = (i.val : ZMod k) + (o : ZMod k) :=
  ZMod.natCast_zmod_val _

private theorem cast_fin_inj {k : ℕ} {i j : Fin k}
    (h : (i.val : ZMod k) = (j.val : ZMod k)) : i = j := by
  apply Fin.ext
  simpa [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using congrArg ZMod.val h

private def slot (b : Bool) (q : Fin 3) : ℤ :=
  if q = 0 then -5 else if q = 2 then 5 else if b then -4 else 4

private theorem slot_lo (b : Bool) (q : Fin 3) : -5 ≤ slot b q := by
  fin_cases q <;> cases b <;> decide

private theorem slot_hi (b : Bool) (q : Fin 3) : slot b q ≤ 5 := by
  fin_cases q <;> cases b <;> decide

private theorem slot_inj (b : Bool) : Function.Injective (slot b) := by
  intro a c h
  fin_cases a <;> fin_cases c <;> cases b <;> simp_all [slot]

private theorem nearby_offset_same_site {k : ℕ} [NeZero k] (hk : 21 ≤ k) (i j x : Fin k)
    (hsep : i ≠ j → 21 ≤ (j.val + k - i.val) % k ∧ 21 ≤ (i.val + k - j.val) % k)
    (a b : ℤ) (s t : Bool) (p q : Fin 3)
    (ha : -5 ≤ a) (ha' : a ≤ 5) (hb : -5 ≤ b) (hb' : b ≤ 5)
    (h₁ : offset x a = offset i (slot s p)) (h₂ : offset x b = offset j (slot t q)) :
    i = j := by
  have hp := slot_lo s p
  have hp' := slot_hi s p
  have hq := slot_lo t q
  have hq' := slot_hi t q
  apply nearby_sites_eq hk i j hsep (x.val : ZMod k) a b (slot s p) (slot t q)
    (by omega) (by omega) (by omega) (by omega)
  · simpa only [offset_cast] using congrArg (fun f : Fin k => (f.val : ZMod k)) h₁
  · simpa only [offset_cast] using congrArg (fun f : Fin k => (f.val : ZMod k)) h₂

end PEqualNP.Outside.L_meta_32055_aux

namespace PEqualNP.Outside.L_meta_32055_aux

abbrev Bit := ZMod 2

-- The indexes 0 through 10 represent raw offsets -5 through +5 at a column observation.
def colQuartic (w : Fin 11 → Bit) : Bit :=
  let t := fun (a b c : Fin 11) => w a + w b + w c
  let A := t 0 2 4 * t 1 3 5 + t 2 4 6 * t 3 5 7 + t 4 6 8 * t 5 7 9
  let B := t 1 3 5 * t 2 4 6 + t 3 5 7 * t 4 6 8 + t 5 7 9 * t 6 8 10
  A * B

private theorem col_endpoint_coefficient (w : Fin 11 → Bit) (l r : Bit) :
    colQuartic (Function.update (Function.update w 0 l) 10 r) -
    colQuartic (Function.update (Function.update w 0 l) 10 0) -
    colQuartic (Function.update (Function.update w 0 0) 10 r) +
    colQuartic (Function.update (Function.update w 0 0) 10 0) =
    l * r * (w 1 + w 3 + w 5) * (w 5 + w 7 + w 9) := by
  simp only [colQuartic, Function.update_apply]
  norm_num
  ring

private def localDiff (w d : Fin 11 → Bit) (p : Fin 11) (l m r : Bit) : Bit :=
  let x := Function.update (Function.update (Function.update w 0 l) p m) 10 r
  colQuartic (x + d) - colQuartic x

private theorem localDiff_coeff_left (w d : Fin 11 → Bit) (l m r : Bit) :
    localDiff w d 1 l m r - localDiff w d 1 l m 0 -
        localDiff w d 1 0 m r + localDiff w d 1 0 m 0 =
      l*r*((d 5+d 7+d 9)*m +
        (d 1+w 3+d 3+w 5+d 5)*(w 5+d 5+w 7+d 7+w 9+d 9) -
          (w 3+w 5)*(w 5+w 7+w 9)) := by
  simp only [localDiff, colQuartic, Pi.add_apply, Function.update_apply]
  norm_num
  ring

private theorem localDiff_coeff_right (w d : Fin 11 → Bit) (l m r : Bit) :
    localDiff w d 9 l m r - localDiff w d 9 l m 0 -
        localDiff w d 9 0 m r + localDiff w d 9 0 m 0 =
      l*r*((d 1+d 3+d 5)*m +
        (w 1+d 1+w 3+d 3+w 5+d 5)*(w 5+d 5+w 7+d 7+d 9) -
          (w 1+w 3+w 5)*(w 5+w 7)) := by
  simp only [localDiff, colQuartic, Pi.add_apply, Function.update_apply]
  norm_num
  ring

end PEqualNP.Outside.L_meta_32055_aux
namespace PEqualNP.Outside.L_meta_32055_aux

private theorem cast_index {k : ℕ} (hk : 0 < k) (n : ℕ) : ((index hk n).val : ZMod k) = n :=
  ZMod.natCast_mod _ _

private theorem cast_index_plus {k : ℕ} (hk : 0 < k) (i : Fin k) (n : ℕ) :
    ((index hk (i.val+n)).val : ZMod k) = (i.val : ZMod k) + (n : ZMod k) := by
  rw [cast_index, Nat.cast_add]

private theorem cast_index_minus {k : ℕ} (hk : 0 < k) (i : Fin k) (n : ℕ) (hn : n < k) :
    ((index hk (i.val+k-n%k)).val : ZMod k) = (i.val : ZMod k) - (n : ZMod k) := by
  rw [Nat.mod_eq_of_lt hn, cast_index, Nat.cast_sub (by omega : n ≤ i.val+k), Nat.cast_add,
    ZMod.natCast_self, add_zero]

private def colWindow {k : ℕ} [NeZero k] (i : Fin k) (w : Word k) (j : Fin 11) : Bit :=
  w (offset i ((j.val : ℤ)-5))

private theorem index_plus_offset {k : ℕ} [NeZero k] (hk : 0 < k) (i : Fin k) (n : ℕ) :
    index hk (i.val+n) = offset i (n : ℤ) := by
  apply cast_fin_inj
  rw [cast_index_plus, offset_cast, Int.cast_natCast]

private theorem index_minus_offset {k : ℕ} [NeZero k] (hk : 0 < k) (i : Fin k) (n : ℕ)
    (hn : n < k) : index hk (i.val+k-n%k) = offset i (-(n : ℤ)) := by
  apply cast_fin_inj
  rw [cast_index_minus _ _ _ hn, offset_cast, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg]

private theorem offset_offset {k : ℕ} [NeZero k] (i : Fin k) (a b : ℤ) :
    offset (offset i a) b = offset i (a+b) := by
  apply cast_fin_inj
  simp only [offset_cast, Int.cast_add, add_assoc]

private def rowQuartic (w : Fin 7 → Bit) : Bit :=
  let t := fun (a b c : Fin 7) => w a + w b + w c
  let A := t 0 1 2 * t 1 2 3 + t 1 2 3 * t 2 3 4 + t 2 3 4 * t 3 4 5
  let B := t 1 2 3 * t 2 3 4 + t 2 3 4 * t 3 4 5 + t 3 4 5 * t 4 5 6
  A * B

private def rowWindow {k : ℕ} [NeZero k] (i : Fin k) (w : Word k) (j : Fin 7) : Bit :=
  w (offset i ((j.val : ℤ)-1))

private theorem col_top_window {k : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (i : Fin k) (w : Word k) : topWord hk w true i = colQuartic (colWindow i w) := by
  have h₂ : 2 < k := by omega
  have h₃ : 3 < k := by omega
  simp only [topWord, gap, mix, quadratic, linearInput, rotate, spin, if_true,
    colQuartic, colWindow]
  simp only [index_plus_offset, index_minus_offset _ _ 2 h₂, index_minus_offset _ _ 3 h₃,
    offset_offset]
  norm_num
  ring

private theorem row_top_window {k : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (i : Fin k) (w : Word k) : topWord hk w false i = rowQuartic (rowWindow i w) := by
  have h₁ : 1 < k := by omega
  simp only [topWord, gap, mix, quadratic, linearInput, rotate, spin, Bool.false_eq_true,
    if_false, rowQuartic, rowWindow]
  simp only [index_plus_offset, index_minus_offset _ _ 1 h₁, offset_offset]
  norm_num
  ring

private theorem tap1_window {k : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (i : Fin k) (w : Word k) :
    mix hk 2 (rotate hk 3 w) (index hk (i.val+1)) =
      colWindow i w 1 + colWindow i w 3 + colWindow i w 5 := by
  have h₂ : 2 < k := by omega
  have h₃ : 3 < k := by omega
  simp only [mix, rotate, colWindow, index_plus_offset, index_minus_offset _ _ 2 h₂,
    index_minus_offset _ _ 3 h₃, offset_offset]
  norm_num
  ring

private theorem tap5_window {k : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (i : Fin k) (w : Word k) :
    mix hk 2 (rotate hk 3 w) (index hk (i.val+5)) =
      colWindow i w 5 + colWindow i w 7 + colWindow i w 9 := by
  have h₂ : 2 < k := by omega
  have h₃ : 3 < k := by omega
  simp only [mix, rotate, colWindow, index_plus_offset, index_minus_offset _ _ 2 h₂,
    index_minus_offset _ _ 3 h₃, offset_offset]
  norm_num
  ring

end PEqualNP.Outside.L_meta_32055_aux
namespace PEqualNP.Outside.L_meta_32055_aux

private def choices {k : ℕ} [NeZero k] (T : Finset (Fin k)) (side : Fin k → Bool) : Set (Fin k) :=
  {j | ∃ i ∈ T, ∃ q, j = offset i (slot (side i) q)}

private noncomputable def patch {k : ℕ} [NeZero k] (T : Finset (Fin k)) (side : Fin k → Bool)
    (x y : Word k) : Word k := by
  classical
  exact fun j => if j ∈ choices T side then y j else x j

private noncomputable def patchLin {k : ℕ} [NeZero k] (T : Finset (Fin k)) (side : Fin k → Bool) :
    Word k →ₗ[Scalar] Word k := by
  classical
  exact { toFun := fun y j => if j ∈ choices T side then y j else 0
          map_add' := fun a b => by ext j; by_cases hj : j ∈ choices T side <;> simp [hj]
          map_smul' := fun a b => by ext j; by_cases hj : j ∈ choices T side <;> simp [hj] }

private theorem patch_eq {k : ℕ} [NeZero k] (T : Finset (Fin k)) (side : Fin k → Bool) (x y : Word k) :
    patch T side x y = patch T side x 0 + patchLin T side y := by
  classical
  ext j
  by_cases hj : j ∈ choices T side <;> simp [patch, patchLin, hj]

private theorem offset_inj_short {k : ℕ} [NeZero k] (h21 : 21 ≤ k) (i : Fin k) (a b : ℤ)
    (ha : -5 ≤ a) (ha' : a ≤ 5) (hb : -5 ≤ b) (hb' : b ≤ 5)
    (h : offset i a = offset i b) : a = b := by
  have h' := congrArg (fun j : Fin k => (j.val : ZMod k)) h
  simp only [offset_cast] at h'
  exact short_offset_inj h21 (by omega) (by omega) (by omega) (by omega) (add_left_cancel h')

private theorem hits_both {k : ℕ} [NeZero k] (h21 : 21 ≤ k) (i t : Fin k) (a b : ℤ)
    (ha : -5 ≤ a) (ha' : a ≤ 5) (hb : -5 ≤ b) (hb' : b ≤ 5)
    (h₁ : offset i a = offset t (-5)) (h₂ : offset i b = offset t 5) : i = t := by
  apply cast_fin_inj
  apply interval_spans_endpoints h21 _ _ a b ha hb' (by omega) (by omega)
  · simpa only [offset_cast] using congrArg (fun j : Fin k => (j.val : ZMod k)) h₁
  · simpa only [offset_cast] using congrArg (fun j : Fin k => (j.val : ZMod k)) h₂

private theorem row_cannot_hit_both {k : ℕ} [NeZero k] (h21 : 21 ≤ k) (i t : Fin k) (a b : ℤ)
    (ha : -1 ≤ a) (ha' : a ≤ 5) (hb : -1 ≤ b) (hb' : b ≤ 5)
    (h₁ : offset i a = offset t (-5)) (h₂ : offset i b = offset t 5) : False := by
  have h := hits_both h21 i t a b (by omega) ha' (by omega) hb' h₁ h₂
  subst t
  have := offset_inj_short h21 i a (-5) (by omega) ha' (by omega) (by omega) h₁
  omega

private theorem support_degree {k : ℕ} [NeZero k] (i₀ i₁ : Fin k) (T : Finset (Fin k))
    (side : Fin k → Bool) (x : Word k) {J : Type} (loc : J → Fin k) (G : (J → Scalar) → Scalar)
    (h : ∀ j, loc j ∈ choices T side → loc j = i₀ ∨ loc j = i₁) :
    degree 2 (fun y => G (fun j => patch T side x y (loc j))) := by
  classical
  let g : Scalar → Scalar → Scalar := fun a b => G (fun p =>
    if loc p ∈ choices T side then if loc p = i₀ then a else b else x (loc p))
  have he : (fun y => G (fun j => patch T side x y (loc j))) = fun y => g (y i₀) (y i₁) := by
    funext y
    unfold g
    congr 1
    funext j
    by_cases hj : loc j ∈ choices T side
    · simp only [patch, if_pos hj]
      split
      · rename_i ht
        rw [ht]
      · rename_i hn
        rcases h j hj with ht | ht
        · exact (hn ht).elim
        · rw [ht]
    · simp [patch, hj]
  rw [he]
  exact degree_two_coords i₀ i₁ g

private theorem local_support {k : ℕ} [NeZero k] (h21 : 21 ≤ k)
    (T : Finset (Fin k)) (side : Fin k → Bool)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 21 ≤ (j.val + k - i.val) % k)
    (i : Fin k) {J : Type} (o : J → ℤ)
    (ho : ∀ j, -5 ≤ o j ∧ o j ≤ 5)
    (hboth : ∀ t ∈ T, ∀ a b, offset i (o a) = offset t (-5) →
      offset i (o b) = offset t 5 → False) :
    ∃ i₀ i₁ : Fin k, ∀ j, offset i (o j) ∈ choices T side →
      offset i (o j) = i₀ ∨ offset i (o j) = i₁ := by
  classical
  by_cases hex : ∃ j, offset i (o j) ∈ choices T side
  · obtain ⟨a, t, ht, r, hr⟩ := hex
    have hone (j : J) (hj : offset i (o j) ∈ choices T side) :
        ∃ q, offset i (o j) = offset t (slot (side t) q) := by
      obtain ⟨t', ht', q, hq⟩ := hj
      have he : t = t' := nearby_offset_same_site h21 t t' i
        (fun h => ⟨hsep t ht t' ht' h, hsep t' ht' t ht (Ne.symm h)⟩)
        (o a) (o j) (side t) (side t') r q
        (ho a).1 (ho a).2 (ho j).1 (ho j).2 hr hq
      subst t'
      exact ⟨q, hq⟩
    by_cases hl : ∃ j, offset i (o j) = offset t (-5)
    · obtain ⟨l, hl⟩ := hl
      refine ⟨offset t (slot (side t) 0), offset t (slot (side t) 1), ?_⟩
      intro j hj
      obtain ⟨q, hq⟩ := hone j hj
      fin_cases q
      · exact Or.inl hq
      · exact Or.inr hq
      · exact (hboth t ht l j hl (by simpa [slot] using hq)).elim
    · refine ⟨offset t (slot (side t) 1), offset t (slot (side t) 2), ?_⟩
      intro j hj
      obtain ⟨q, hq⟩ := hone j hj
      fin_cases q
      · exact (hl ⟨j, by simpa [slot] using hq⟩).elim
      · exact Or.inl hq
      · exact Or.inr hq
  · exact ⟨i, i, fun j hj => (hex ⟨j, hj⟩).elim⟩

end PEqualNP.Outside.L_meta_32055_aux
namespace PEqualNP.Outside.L_meta_32055_aux

private theorem degree_remove_cubic {k : ℕ} (a b c : Fin k) (g : Bit → Bit → Bit → Bit)
    (C : Bit) (hg : ∀ l m r, g l m r - g l m 0 - g 0 m r + g 0 m 0 = l*r*(m+C)) :
    degree 2 (fun y : Word k => g (y a) (y b) (y c) - y a * y b * y c) := by
  have h := degree_add
    (degree_sub (degree_add (degree_two_coords a b (fun l m => g l m 0))
      (degree_two_coords b c (fun m r => g 0 m r)))
      (degree_two_coords b b (fun m _ => g 0 m 0)))
    (degree_scale C (degree_mul (degree_coord a) (degree_coord c)))
  convert h using 1
  funext y
  linear_combination hg (y a) (y b) (y c)

private theorem own_window_chosen {k : ℕ} [NeZero k] (h21 : 21 ≤ k)
    (T : Finset (Fin k)) (side : Fin k → Bool)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 21 ≤ (j.val + k - i.val) % k)
    (i : Fin k) (hi : i ∈ T) (j : Fin 11) :
    offset i ((j.val : ℤ)-5) ∈ choices T side ↔
      j = 0 ∨ j = (if side i then 1 else 9) ∨ j = 10 := by
  have hj₁ : -5 ≤ (j.val : ℤ)-5 := by omega
  have hj₂ : (j.val : ℤ)-5 ≤ 5 := by omega
  constructor
  · rintro ⟨t, ht, q, hq⟩
    have he : i = t := nearby_offset_same_site h21 i t i
      (fun h => ⟨hsep i hi t ht h, hsep t ht i hi (Ne.symm h)⟩)
      (-5) ((j.val : ℤ)-5) (side i) (side t) 0 q
      (by omega) (by omega) hj₁ hj₂ (by simp [slot]) hq
    subst t
    have h := offset_inj_short h21 i ((j.val : ℤ)-5) (slot (side i) q)
      hj₁ hj₂ (slot_lo _ _) (slot_hi _ _) hq
    fin_cases q <;> by_cases hb : side i = true <;> simp [slot, hb] at h ⊢ <;>
      first | (left; apply Fin.ext; omega) | (right; left; apply Fin.ext; omega) |
        (right; right; apply Fin.ext; omega)
  · rintro (rfl | rfl | rfl)
    · exact ⟨i, hi, 0, by norm_num [slot]⟩
    · refine ⟨i, hi, 1, ?_⟩
      by_cases hb : side i = true <;> norm_num [slot, hb]
    · exact ⟨i, hi, 2, by norm_num [slot]⟩

private theorem selected_col_degree {k : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (T : Finset (Fin k)) (side : Fin k → Bool)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 21 ≤ (j.val + k - i.val) % k)
    (x d : Word k) (i : Fin k) (hi : i ∈ T)
    (hact : if side i then colWindow i d 5 + colWindow i d 7 + colWindow i d 9 = 1
      else colWindow i d 1 + colWindow i d 3 + colWindow i d 5 = 1) :
    degree 2 (fun y => delta (fun w => topWord hk w true i) d (patch T side x y) -
        (y (offset i (slot (side i) 0)) * y (offset i (slot (side i) 1)) *
         y (offset i (slot (side i) 2)))) := by
  classical
  let a := offset i (slot (side i) 0)
  let b := offset i (slot (side i) 1)
  let c := offset i (slot (side i) 2)
  let p : Fin 11 := if side i then 1 else 9
  let g := localDiff (colWindow i x) (colWindow i d) p
  have hpatch (y : Word k) : colWindow i (patch T side x y) =
      Function.update (Function.update (Function.update (colWindow i x) 0 (y a)) p (y b)) 10 (y c) := by
    funext j
    have hj := own_window_chosen h21 T side hsep i hi j
    change (if offset i ((j.val : ℤ)-5) ∈ choices T side then y (offset i ((j.val : ℤ)-5))
      else x (offset i ((j.val : ℤ)-5))) = _
    rw [hj]
    fin_cases j <;> by_cases hb : side i = true <;>
      norm_num [p, a, b, c, hb, slot, Function.update_apply, colWindow]
  have he : (fun y => delta (fun w => topWord hk w true i) d (patch T side x y) -
        (y a * y b * y c)) = fun y => g (y a) (y b) (y c) - y a * y b * y c := by
    funext y
    simp only [delta, col_top_window hk h21, g, localDiff]
    have hsum : colWindow i (patch T side x y + d) = colWindow i (patch T side x y) + colWindow i d := rfl
    rw [hsum, hpatch]
  change degree 2 (fun y => delta (fun w => topWord hk w true i) d (patch T side x y) - y a * y b * y c)
  rw [he]
  by_cases hb : side i = true
  · simp only [hb, ite_true] at hact
    let w := colWindow i x
    let D := colWindow i d
    refine degree_remove_cubic a b c g
      ((D 1+w 3+D 3+w 5+D 5)*(w 5+D 5+w 7+D 7+w 9+D 9) -
        (w 3+w 5)*(w 5+w 7+w 9)) (fun l m r => ?_)
    simp only [g, p, hb, ite_true, localDiff_coeff_left, hact, one_mul, w, D]
    ring
  · simp only [hb, Bool.false_eq_true, ite_false] at hact
    let w := colWindow i x
    let D := colWindow i d
    refine degree_remove_cubic a b c g
      ((w 1+D 1+w 3+D 3+w 5+D 5)*(w 5+D 5+w 7+D 7+D 9) -
        (w 1+w 3+w 5)*(w 5+w 7)) (fun l m r => ?_)
    simp only [g, p, hb, Bool.false_eq_true, ite_false, localDiff_coeff_right, hact, one_mul, w, D]
    ring

end PEqualNP.Outside.L_meta_32055_aux
namespace PEqualNP.Outside.L_meta_32055_aux

private def blockMonomial {k : ℕ} [NeZero k] (side : Fin k → Bool) (i : Fin k) (y : Word k) : Bit :=
  y (offset i (slot (side i) 0)) * y (offset i (slot (side i) 1)) * y (offset i (slot (side i) 2))

private theorem restricted_degree {k : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (T : Finset (Fin k)) (side : Fin k → Bool)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 21 ≤ (j.val + k - i.val) % k)
    (name c₁ c₂ : Bool → Word k) (mask : Bool → Fin k → Bit)
    (hmask : ∀ i ∈ T, mask true i = 1) (d x : Word k)
    (hact : ∀ i ∈ T, if side i then colWindow i d 5 + colWindow i d 7 + colWindow i d 9 = 1
      else colWindow i d 1 + colWindow i d 3 + colWindow i d 5 = 1) :
    degree 2 (fun y => delta (fun w => observe mask (outputWord hk name c₁ c₂ w)) d
      (patch T side x y) - ∑ i ∈ T, blockMonomial side i y) := by
  classical
  let f := fun w => observe mask (outputWord hk name c₁ c₂ w)
  let t := fun w => observe mask (topWord hk w)
  let P := patch T side x
  have hrem : degree 2 (fun y => delta (fun w => f w - t w) d (P y)) := by
    convert degree_affine_comp (patchLin T side).toAddMonoidHom (P 0) 2
      (observed_remainder hk name c₁ c₂ mask d) using 1
    funext y
    change delta (fun w => f w - t w) d (patch T side x y) =
      delta (fun w => f w - t w) d (patch T side x 0 + patchLin T side y)
    rw [patch_eq T side x y]
  have hr (i : Fin k) : degree 2 (fun y => delta (fun w => topWord hk w false i) d (P y)) := by
    let o : Fin 7 → ℤ := fun j => (j.val : ℤ)-1
    have ho (j : Fin 7) : -5 ≤ o j ∧ o j ≤ 5 := by dsimp [o]; omega
    obtain ⟨a, b, h⟩ := local_support h21 T side hsep i o ho (by
      intro t ht a b ha hb
      apply row_cannot_hit_both h21 i t (o a) (o b) _ (ho a).2 _ (ho b).2 ha hb <;>
        dsimp [o] <;> omega)
    have hh := support_degree a b T side x (fun j => offset i (o j))
      (fun w => rowQuartic (w + rowWindow i d) - rowQuartic w) h
    change degree 2 (fun y => rowQuartic (rowWindow i (P y + d)) - rowQuartic (rowWindow i (P y))) at hh
    simpa only [delta, row_top_window hk h21] using hh
  have hc (i : Fin k) : degree 2 (fun y => mask true i *
      delta (fun w => topWord hk w true i) d (P y) - (if i ∈ T then blockMonomial side i y else 0)) := by
    by_cases hi : i ∈ T
    · simp only [hi, ite_true, hmask i hi, one_mul, blockMonomial]
      exact selected_col_degree hk h21 T side hsep x d i hi (hact i hi)
    · simp only [hi, ite_false, sub_zero]
      apply degree_scale
      let o : Fin 11 → ℤ := fun j => (j.val : ℤ)-5
      have ho (j : Fin 11) : -5 ≤ o j ∧ o j ≤ 5 := by dsimp [o]; omega
      obtain ⟨a, b, h⟩ := local_support h21 T side hsep i o ho (by
        intro t ht a b ha hb
        have he := hits_both h21 i t (o a) (o b) (ho a).1 (ho a).2 (ho b).1 (ho b).2 ha hb
        exact hi (he ▸ ht))
      have hh := support_degree a b T side x (fun j => offset i (o j))
        (fun w => colQuartic (w + colWindow i d) - colQuartic w) h
      change degree 2 (fun y => colQuartic (colWindow i (P y + d)) - colQuartic (colWindow i (P y))) at hh
      simpa only [delta, col_top_window hk h21] using hh
  have hsumr := degree_sum Finset.univ _ (fun i _ => degree_scale (mask false i) (hr i))
  have hsumc := degree_sum Finset.univ _ (fun i _ => hc i)
  convert degree_add hrem (degree_add hsumr hsumc) using 1
  funext y
  change delta f d (P y) - (∑ i ∈ T, blockMonomial side i y) =
    delta (fun w => f w - t w) d (P y) + _
  simp only [delta, t, observe, mul_sub, Finset.sum_sub_distrib]
  have hh : (∑ i : Fin k, if i ∈ T then blockMonomial side i y else 0) =
      ∑ i ∈ T, blockMonomial side i y := by
    rw [← Finset.sum_filter]
    simp
  rw [hh]
  ring

end PEqualNP.Outside.L_meta_32055_aux
namespace PEqualNP.Outside.L_meta_32055_aux

open PEqualNP.Outside.L_meta_32055_aux.Leaves (Van3 cubic adaptive_hits_bound)

private def slot_embedding {k : ℕ} [NeZero k] (h21 : 21 ≤ k)
    (T : Finset (Fin k)) (side : Fin k → Bool)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 21 ≤ (j.val + k - i.val) % k) :
    ↥T × Fin 3 ↪ Fin k where
  toFun p := offset p.1 (slot (side p.1) p.2)
  inj' := by
    rintro ⟨⟨i, hi⟩, p⟩ ⟨⟨j, hj⟩, q⟩ h
    have he : i = j := nearby_offset_same_site h21 i j i
      (fun hn => ⟨hsep i hi j hj hn, hsep j hj i hi (Ne.symm hn)⟩)
      (slot (side i) p) (slot (side i) p) (side i) (side j) p q
      (slot_lo _ _) (slot_hi _ _) (slot_lo _ _) (slot_hi _ _) rfl h
    subst j
    have hs := offset_inj_short h21 i _ _ (slot_lo _ _) (slot_hi _ _) (slot_lo _ _) (slot_hi _ _) h
    have heq := slot_inj (side i) hs
    change p = q at heq
    subst q
    rfl

private theorem degree_to_Van3 {k : ℕ} {f : Word k → Scalar} (hf : degree 2 f) : Van3 f := by
  intro v x
  exact differences_zero (List.ofFn v) (by simp) hf x

private theorem patch_translate {k : ℕ} [NeZero k] (T : Finset (Fin k)) (side : Fin k → Bool)
    (x y : Word k) : patchLin T side y + x = patch T side x (y+x) := by
  classical
  ext j
  by_cases hj : j ∈ choices T side <;> simp [patchLin, patch, hj]

private theorem adaptive_observation {k h : ℕ} [NeZero k] (hk : 0 < k) (h21 : 21 ≤ k)
    (T : Finset (Fin k)) (side : Fin k → Bool)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 21 ≤ (j.val + k - i.val) % k)
    (name c₁ c₂ : Bool → Word k) (mask : Bool → Fin k → Bit)
    (hmask : ∀ i ∈ T, mask true i = 1) (d : Word k)
    (hact : ∀ i ∈ T, if side i then colWindow i d 5 + colWindow i d 7 + colWindow i d 9 = 1
      else colWindow i d 1 + colWindow i d 3 + colWindow i d 5 = 1)
    (ask : Fin h → ℕ → Word k →ₗ[Scalar] Scalar) (out : ℕ → Word k → Scalar)
    (hout : ∀ t, Van3 (out t)) :
    let f := fun w => observe mask (outputWord hk name c₁ c₂ w)
    let run := fun w => (List.finRange h).foldl (fun t j =>
      2 * t + (if ask j t w = 0 then 0 else 1)) (0 : ℕ)
    4 ^ (T.card - h) *
      ((2 : ℤ) * (Nat.card {w : Word k // delta f d w = out (run w) w} : ℤ) -
        (2 : ℤ)^k).natAbs ≤ 3 ^ (T.card - h) * 2^k := by
  classical
  let e : Fin T.card ≃ ↥T := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let pos : Fin T.card × Fin 3 ↪ Fin k :=
    (Equiv.prodCongr e (Equiv.refl (Fin 3))).toEmbedding.trans (slot_embedding h21 T side hsep)
  have hmono (y : Word k) : cubic pos y = ∑ i ∈ T, blockMonomial side i y := by
    change (∑ j : Fin T.card, blockMonomial side (e j) y) = _
    rw [← Finset.sum_coe_sort T]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  let f := fun w => observe mask (outputWord hk name c₁ c₂ w)
  have hh := adaptive_hits_bound pos (patchLin T side) ask (delta f d) out hout (by
    intro x
    refine ⟨fun y => delta f d (patchLin T side y + x) - cubic pos y, ?_, fun y => by ring⟩
    apply degree_to_Van3
    simp only [hmono, patch_translate]
    have hr := degree_shift x (restricted_degree hk h21 T side hsep name c₁ c₂ mask hmask d x hact)
    have hmono3 : degree 3 (fun y : Word k => ∑ i ∈ T, blockMonomial side i y) := by
      apply degree_sum (n := 3) T (fun i y => blockMonomial side i y)
      intro i _
      exact degree_mul
        (degree_mul (degree_coord (offset i (slot (side i) 0)))
          (degree_coord (offset i (slot (side i) 1))))
        (degree_coord (offset i (slot (side i) 2)))
    have hc := hmono3 x
    convert degree_add hr hc using 1
    funext y
    simp only [delta]
    ring)
  have hcard : Fintype.card (Word k) = 2^k := by simp [Word, Scalar, ZMod.card]
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat, mul_comm (2^k : ℕ)] using hh

end PEqualNP.Outside.L_meta_32055_aux
open PEqualNP.Outside.L_meta_32055_aux in
theorem PEqualNP.Outside.L_meta_32055 :
∀ (k : ℕ) (hk : 0 < k), 21 ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (s : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + s)) + x (ix (i.val + k - s % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let quad := fun (f : W → F) => ∀ (v : Fin 3 → W) (x : W), (List.ofFn v).foldl diff f x = 0
  let tap := fun (w : W) (j : ℕ) => mix 2 (rot 3 w) (ix j)
  ∀ (u v r₁ r₂ c₁ c₂ : W) (A B : Fin k → Bool),
    let obs := fun (a : Fin k → Bool) (w : W) => ∑ i : Fin k, if a i then w i else 0
    let f := fun w : W =>
      let row := step (mix 1 (rot 1 w + u)) + w + r₁
      let col := step (mix 2 (rot 3 w + v)) + rot 4 w + c₁
      obs A (step (mix 1 row) + rot 2 w + r₂) +
        obs B (step (mix 2 col) + rot 7 w + c₂)
    ∀ S : Finset (Fin k), (∀ i ∈ S, B i = true) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 21 ≤ (j.val+k-i.val) % k) →
      ∀ (h : ℕ) (ask : W → Fin h → ℕ → (W →ₗ[F] F)) (out : W → ℕ → W → F),
        (∀ d t, quad (out d t)) →
        let run := fun (d w : W) => (List.finRange h).foldl (fun t ℓ =>
          2*t + (if ask d ℓ t w = 0 then 0 else 1)) (0 : ℕ)
        let active := fun d : W => (S.filter (fun i =>
          tap d (i.val+1) ≠ 0 ∨ tap d (i.val+5) ≠ 0)).card
        let hits := fun d : W => Nat.card {w : W // diff f d w = out d (run d w) w}
        let gap := fun d : W => ((2 : ℤ) * (hits d : ℤ) - (2 : ℤ)^k).natAbs
        (∀ d : W, 4^(active d-h) * gap d ≤ 3^(active d-h) * 2^k) ∧
        3^h * 16^S.card * (∑ d : W, gap d) ≤ 4^h * 13^S.card * (2^k)^2 := by
  classical
  intro k hk h21 F W ix rot mix step diff quad tap u v r₁ r₂ c₁ c₂ A B obs f S hB hsep h ask out hout run active hits gap
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let name : Bool → Word k := fun b => if b then v else u
  let c : Bool → Word k := fun b => if b then c₁ else r₁
  let cp : Bool → Word k := fun b => if b then c₂ else r₂
  let mask : Bool → Fin k → Scalar := fun b i => if (if b then B i else A i) then 1 else 0
  have hz (w : Word k) : rotate hk 0 w = w := by
    funext i
    have hi : index hk (i.val + k - 0 % k) = i := by
      apply cast_fin_inj
      simp [cast_index, Nat.cast_add, ZMod.natCast_self]
    exact congrArg w hi
  have hf : f = fun w => observe mask (outputWord hk name c cp w) := by
    funext w
    have hm (b : Bool) (i : Fin k) (t : Scalar) : mask b i * t =
        (if (if b then B i else A i) then t else 0) := by
      simp only [mask]
      split <;> simp
    simp only [f, obs, observe, hm, outputWord, firstRow, namedInput,
      PEqualNP.Outside.L_meta_32055_aux.gap, spin, name, c, cp,
      Bool.false_eq_true, ite_false, ite_true, hz] <;> rfl
  have hpoint : ∀ d : W, 4^(active d-h) * gap d ≤ 3^(active d-h) * 2^k := by
    intro d
    let T := S.filter (fun i => tap d (i.val+1) ≠ 0 ∨ tap d (i.val+5) ≠ 0)
    let side : Fin k → Bool := fun i => decide (tap d (i.val+5) ≠ 0)
    have hmem (i : Fin k) (hi : i ∈ T) := Finset.mem_filter.mp hi
    have hmask (i : Fin k) (hi : i ∈ T) : mask true i = 1 := by simp [mask, hB i (hmem i hi).1]
    have hspace (i : Fin k) (hi : i ∈ T) (j : Fin k) (hj : j ∈ T) (hn : i ≠ j) :=
      hsep i (hmem i hi).1 j (hmem j hj).1 hn
    have hact (i : Fin k) (hi : i ∈ T) :
        if side i then colWindow i d 5 + colWindow i d 7 + colWindow i d 9 = 1
        else colWindow i d 1 + colWindow i d 3 + colWindow i d 5 = 1 := by
      rw [← tap1_window hk h21 i d, ← tap5_window hk h21 i d]
      change if side i then tap d (i.val+5) = 1 else tap d (i.val+1) = 1
      by_cases hn : tap d (i.val+5) ≠ 0
      · have hs : side i = true := decide_eq_true hn
        rw [ite_eq_left hs]
        exact (bit_cases _).resolve_left hn
      · have hs : ¬side i = true := fun he => hn (of_decide_eq_true he)
        rw [if_neg hs]
        exact (bit_cases _).resolve_left ((hmem i hi).2.resolve_right hn)
    have hh := adaptive_observation hk h21 T side hspace name c cp mask hmask d hact (ask d) (out d) (hout d)
    change 4^(T.card-h) * ((2 : ℤ) * (Nat.card {w : W // diff f d w = out d (run d w) w} : ℤ) - (2 : ℤ)^k).natAbs ≤ _
    rw [hf]
    exact hh
  refine ⟨hpoint, ?_⟩
  exact PEqualNP.Outside.L_meta_32055_aux.Average.averageTap hk h21 S hsep h (fun d w => diff f d w = out d (run d w) w) hpoint
