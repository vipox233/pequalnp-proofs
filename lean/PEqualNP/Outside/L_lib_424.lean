import Mathlib

namespace PEqualNP.Outside.L_lib_424_aux
abbrev Cube (n : ℕ) := Fin n → ZMod 2
def sgn (b : ZMod 2) : ℤ := if b=0 then 1 else -1
def ch {n : ℕ} (a x : Cube n) : ℤ := sgn (dotProduct a x)

theorem sign_add (a b : ZMod 2) : sgn (a+b) = sgn a * sgn b := by
  revert a b
  decide

theorem symm {n : ℕ} (a x : Cube n) : ch a x = ch x a := by
  simp only [ch,dotProduct,mul_comm (a _) (x _)]

theorem ortho {n : ℕ} (a b : Cube n) :
    (∑ x : Cube n, ch a x * ch b x) = if a=b then (2:ℤ)^n else 0 := by
  classical
  by_cases eq : a=b
  · subst b
    have square (t : ZMod 2) : sgn t * sgn t = 1 := by revert t; decide
    simp [ch,square,ZMod.card]
  · rw [if_neg eq]
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
      by_contra! h
      exact eq (funext h)
    let e : Cube n := fun j => if j=i then 1 else 0
    have shift (p x : Cube n) : ch p (x+e) = ch p x * sgn (p i) := by
      have unit : dotProduct p e = p i := by simp [dotProduct,e,mul_ite]
      rw [ch,dotProduct_add,unit,sign_add]
      rfl
    have opposite : ∀ u v : ZMod 2, u ≠ v → sgn u * sgn v = -1 := by decide
    let f (x : Cube n) := ch a x * ch b x
    have flip (x : Cube n) : f (x+e) = -f x := by
      dsimp only [f]
      rw [shift,shift]
      calc
        _ = (ch a x * ch b x) * (sgn (a i) * sgn (b i)) := by ring
        _ = _ := by rw [opposite _ _ hi]; ring
    have same := Equiv.sum_comp (Equiv.addRight e) f
    change (∑ x : Cube n, f (x+e)) = ∑ x : Cube n, f x at same
    simp_rw [flip] at same
    rw [Finset.sum_neg_distrib] at same
    change (∑ x : Cube n, f x) = 0
    omega

def transform {n : ℕ} (f : Cube n → ℤ) (a : Cube n) := ∑ x : Cube n, f x * ch a x

theorem adj {n : ℕ} (f h : Cube n → ℤ) :
    (∑ a : Cube n, transform f a * h a) = ∑ z : Cube n, f z * transform h z := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  rw [symm x z]
  ring

theorem inv {n : ℕ} (f : Cube n → ℤ) (a : Cube n) :
    transform (transform f) a = (2:ℤ)^n * f a := by
  classical
  change (∑ x : Cube n, transform f x * ch a x) = _
  rw [adj]
  have lookup (z : Cube n) : transform (ch a) z = if a=z then (2:ℤ)^n else 0 := ortho a z
  simp_rw [lookup]
  simp [mul_ite,mul_comm]
theorem parseval {n : ℕ} (f g : Cube n → ℤ) :
    (∑ u, transform f u * transform g u) = (2:ℤ)^n * ∑ x, f x * g x := by
  rw [adj]
  simp_rw [inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem two_zero (u : ZMod 2) : u+u=0 := by revert u; decide

theorem convolution {n : ℕ} (f : Cube n → ℤ) (a : Cube n) :
    transform (fun z => ∑ x, f x * f (z+x)) a = (transform f a)^2 := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  let h (y : Cube n) := f y * ch a y
  have translate := Equiv.sum_comp (Equiv.addRight x) h
  change (∑ z : Cube n, h (z+x)) = ∑ y : Cube n, h y at translate
  change (∑ z : Cube n, f x * f (z+x) * ch a z) = f x * ch a x * ∑ y : Cube n, h y
  rw [← translate,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have add : ch a (z+x)=ch a z * ch a x := by simp only [ch,dotProduct_add,sign_add]
  have sq : ∀ t : ZMod 2, sgn t * sgn t = 1 := by decide
  have one : ch a x * ch a x = 1 := sq _
  dsimp only [h]
  rw [add]
  linear_combination -(f x * f (z+x) * ch a z) * one

theorem signed_count {T : Type*} [Fintype T] (p : T → Prop) [DecidablePred p] :
    (∑ x : T, if p x then (-1:ℤ) else 1) =
      (Fintype.card T : ℤ) - 2 * ((Finset.univ.filter p).card : ℤ) := by
  classical
  calc
    _ = ∑ x : T, ((1:ℤ) - 2*(if p x then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
    _ = _ := by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum]
      simp

theorem baseSign (x y z : ZMod 2) :
    sgn x * sgn y * sgn z = if x+y ≠ z then -1 else 1 := by
  revert x y z
  decide

theorem blr {n : ℕ} (f : Cube n → ZMod 2) :
    let N := (2:ℤ)^n
    let H := fun x => sgn (f x)
    let W := transform H
    let fails := ((Finset.univ.filter (fun xy : Cube n × Cube n => f xy.1 + f xy.2 ≠ f (xy.1+xy.2))).card : ℤ)
    (∑ a : Cube n, (W a)^3) = N * (N^2 - 2*fails) ∧
    ∃ u : Cube n, N * ((Finset.univ.filter (fun z : Cube n => f z ≠ dotProduct u z)).card : ℤ) ≤ fails := by
  classical
  intro N H W fails
  let C (z : Cube n) := ∑ x, H x * H (z+x)
  have card : (Fintype.card (Cube n) : ℤ)=N := by simp [Cube,N,ZMod.card]
  have signed := signed_count fun xy : Cube n × Cube n => f xy.1 + f xy.2 ≠ f (xy.1+xy.2)
  have inputs : (∑ z, C z * H z) = N^2-2*fails := by
    calc
      _ = ∑ xy : Cube n × Cube n, if f xy.1 + f xy.2 ≠ f (xy.1+xy.2) then (-1:ℤ) else 1 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro z _
        simp only [C,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        change sgn (f x) * sgn (f (z+x)) * sgn (f z) = _
        rw [← baseSign]
        ring
      _ = _ := by rw [signed]; simp only [Fintype.card_prod,Nat.cast_mul,card,pow_two,fails]
  have moment : (∑ a : Cube n, (W a)^3) = N*(N^2-2*fails) := by
    calc
      _ = ∑ a : Cube n, transform C a * transform H a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show transform C a = (W a)^2 from convolution H a]
        change (W a)^3 = (W a)^2 * W a
        ring
      _ = _ := (parseval C H).trans (by rw [inputs])
  refine ⟨moment,?_⟩
  obtain ⟨u,_,largest⟩ := Finset.exists_max_image (Finset.univ : Finset (Cube n)) W Finset.univ_nonempty
  refine ⟨u,?_⟩
  have total_squares : (∑ a : Cube n, (W a)^2) = N^2 := by
    have squares : ∀ t : ZMod 2, sgn t * sgn t = 1 := by decide
    simpa only [pow_two, W,H,squares,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card,mul_one] using parseval H H
  have bound : (∑ a, (W a)^3) ≤ W u * ∑ a, (W a)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    calc
      (W a)^3 = W a * (W a)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (largest a ha) (sq_nonneg _)
  rw [moment,total_squares] at bound
  let err := ((Finset.univ.filter (fun z : Cube n => f z ≠ dotProduct u z)).card : ℤ)
  have best : W u = N-2*err := by
    have signs : ∀ x y : ZMod 2, sgn x * sgn y = if x≠y then -1 else 1 := by decide
    simpa only [W,transform,H,ch,signs,card,err] using signed_count (fun z : Cube n => f z ≠ dotProduct u z)
  rw [best] at bound
  have positive : 0 < N := by dsimp [N]; positivity
  change N*err ≤ fails
  by_contra! bad
  have contra := mul_pos positive (sub_pos.mpr bad)
  nlinarith

end PEqualNP.Outside.L_lib_424_aux

theorem PEqualNP.Outside.L_lib_424 : ∀ n : ℕ,
  let V := Fin n → ZMod 2
  let sign := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ f : V → ZMod 2,
    let N := (2:ℤ)^n
    let W := fun (a : V) => ∑ x : V, sign (f x + dotProduct a x)
    let fails := ((Finset.univ.filter (fun xy : V × V =>
      f xy.1 + f xy.2 ≠ f (xy.1+xy.2))).card : ℤ)
    (∑ a : V, (W a)^3) = N * (N^2 - 2*fails) ∧
      ∃ u : V, N * ((Finset.univ.filter (fun z : V => f z ≠ dotProduct u z)).card : ℤ) ≤ fails := by
  intro n V sign f N W fails
  have h := PEqualNP.Outside.L_lib_424_aux.blr f
  have ef (a : V) : W a = PEqualNP.Outside.L_lib_424_aux.transform (fun x => PEqualNP.Outside.L_lib_424_aux.sgn (f x)) a := by
    unfold W PEqualNP.Outside.L_lib_424_aux.transform
    apply Finset.sum_congr rfl
    intro x _
    exact PEqualNP.Outside.L_lib_424_aux.sign_add _ _
  simpa only [ef] using h
