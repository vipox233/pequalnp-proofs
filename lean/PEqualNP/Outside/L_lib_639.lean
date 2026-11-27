import Mathlib

namespace PEqualNP.Outside.L_lib_639_aux
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

theorem sign_inj : Function.Injective sgn := by
  intro a b
  revert a b
  decide

theorem one_or_neg (t : ZMod 2) : sgn t = 1 ∨ sgn t = -1 := by
  revert t
  decide

theorem square (t : ZMod 2) : sgn t * sgn t = 1 := by
  revert t
  decide

def supportSpace {n : ℕ} (F : Cube n → ℕ) (z : Cube n) : Submodule (ZMod 2) (Cube n) := by
  refine { carrier := {a | ∀ x, F x ≠ 0 → dotProduct a x = dotProduct a z}, zero_mem' := ?_, add_mem' := ?_, smul_mem' := ?_ }
  · intro a b ha hb x hx
    rw [add_dotProduct, add_dotProduct, ha x hx, hb x hx]
  · simp
  ·
    intro c a ha x hx
    rw [smul_dotProduct,smul_dotProduct,ha x hx]

noncomputable def spec {n : ℕ} (U : Submodule (ZMod 2) (Cube n)) (z a : Cube n) : ℤ :=
  @ite ℤ (a ∈ U) (Classical.propDecidable _) (ch a z) 0

theorem sign_flip {b c : ZMod 2} (h : b ≠ c) : sgn b * sgn c = -1 := by
  revert b c
  decide

theorem transform_spec {n : ℕ} (U : Submodule (ZMod 2) (Cube n)) (z x : Cube n) :
    transform (spec U z) x =
      @ite ℤ (∀ a ∈ U, dotProduct a x = dotProduct a z)
        (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U)) 0 := by
  classical
  by_cases good : ∀ a ∈ U, dotProduct a x = dotProduct a z
  · rw [if_pos good]
    have term (a : Cube n) : spec U z a * ch x a = if a ∈ U then 1 else 0 := by
      rw [symm x a]
      by_cases mem : a ∈ U
      · simp only [spec,if_pos mem,ch,good a mem,square]
      · simp [spec,mem]
    change (∑ a, spec U z a * ch x a) = _
    simp_rw [term]
    rw [Finset.sum_boole]
    have cardU : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
      simpa [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := U))
    rw [Fintype.card_subtype] at cardU
    exact_mod_cast cardU
  · rw [if_neg good]
    push_neg at good
    obtain ⟨b,hb,diff⟩ := good
    let f (a : Cube n) := spec U z a * ch x a
    have flip (a : Cube n) : f (a+b) = - f a := by
      have memiff : a+b ∈ U ↔ a ∈ U := by
        constructor
        · intro hab
          simpa using U.sub_mem hab hb
        · exact fun ha => U.add_mem ha hb
      dsimp only [f]
      rw [symm x (a+b),symm x a]
      by_cases ha : a ∈ U
      · simp only [spec,if_pos ha,if_pos (memiff.mpr ha),ch,add_dotProduct,sign_add]
        have neg := sign_flip (Ne.symm diff)
        calc
          _ = (sgn (dotProduct a z) * sgn (dotProduct a x)) *
              (sgn (dotProduct b z) * sgn (dotProduct b x)) := by ring
          _ = _ := by rw [neg]; ring
      · simp [spec,ha,memiff]
    have same := Equiv.sum_comp (Equiv.addRight b) f
    change (∑ a : Cube n, f (a+b)) = ∑ a : Cube n, f a at same
    simp_rw [flip] at same
    rw [Finset.sum_neg_distrib] at same
    change (∑ a : Cube n, f a) = 0
    omega

theorem mixed_bound {n : ℕ} (F : Cube n → ℕ) (a p q : Cube n)
    (hp : F p ≠ 0) (hq : F q ≠ 0) (pp : ch a p = 1) (qq : ch a q = -1) :
    -(∑ x, (F x : ℤ)) < transform (fun x => (F x : ℤ)) a ∧
    transform (fun x => (F x : ℤ)) a < ∑ x, (F x : ℤ) := by
  classical
  change _ < (∑ x, (F x : ℤ) * ch a x) ∧ (∑ x, (F x : ℤ) * ch a x) < _
  constructor
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_lt_sum
    · intro x _
      rcases one_or_neg (dotProduct a x) with h | h <;> change ch a x = _ at h <;> rw [h] <;> simp
    · refine ⟨p,Finset.mem_univ _,?_⟩
      rw [pp,mul_one]
      have : 0 < (F p : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hp
      omega
  · apply Finset.sum_lt_sum
    · intro x _
      rcases one_or_neg (dotProduct a x) with h | h <;> change ch a x = _ at h <;> rw [h] <;> simp
    · refine ⟨q,Finset.mem_univ _,?_⟩
      rw [qq,mul_neg_one]
      have : 0 < (F q : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hq
      omega

theorem spectral {n : ℕ} (F : Cube n → ℕ) (total : (∑ x, F x) = 2^n)
    (z : Cube n) (hz : F z ≠ 0)
    (hd : ∀ a, (2:ℤ)^n ∣ transform (fun x => (F x : ℤ)) a) (a : Cube n) :
    transform (fun x => (F x : ℤ)) a = (2:ℤ)^n * spec (supportSpace F z) z a := by
  classical
  have mass : (∑ x, (F x : ℤ)) = (2:ℤ)^n := by exact_mod_cast total
  by_cases h : a ∈ supportSpace F z
  · have law : ∀ x, F x ≠ 0 → dotProduct a x = dotProduct a z := h
    have term (x : Cube n) : (F x : ℤ) * ch a x = (F x : ℤ) * ch a z := by
      by_cases hx : F x = 0
      · simp [hx]
      · rw [ch,ch,law x hx]
    simp only [transform,spec,if_pos h]
    simp_rw [term]
    rw [← Finset.sum_mul,mass]
  · simp only [spec,if_neg h,mul_zero]
    change ¬ (∀ x, F x ≠ 0 → dotProduct a x = dotProduct a z) at h
    push_neg at h
    obtain ⟨x,hx,hdiff⟩ := h
    have ne : ch a x ≠ ch a z := fun e => hdiff (sign_inj e)
    have both : -(∑ i, (F i : ℤ)) < transform (fun i => (F i : ℤ)) a ∧
        transform (fun i => (F i : ℤ)) a < ∑ i, (F i : ℤ) := by
      rcases one_or_neg (dotProduct a x) with hx' | hx' <;>
        rcases one_or_neg (dotProduct a z) with hz' | hz' <;>
        change ch a x = _ at hx' <;> change ch a z = _ at hz'
      · exact False.elim (ne (hx'.trans hz'.symm))
      · exact mixed_bound F a x z hx hz hx' hz'
      · exact mixed_bound F a z x hz hx hz' hx'
      · exact False.elim (ne (hx'.trans hz'.symm))
    rw [mass] at both
    exact Int.eq_zero_of_abs_lt_dvd (hd a) (abs_lt.mpr both)

theorem classify : ∀ d : ℕ,
  let V := Fin d → ZMod 2
  let dot := fun (a x : V) => ∑ i, a i * x i
  let spin := fun (a x : V) => if dot a x = 0 then (1 : ℤ) else -1
  ∀ F : V → ℕ, (∑ x, F x) = 2^d →
    ((∀ a : V, (2^d : ℤ) ∣ ∑ x : V, (F x : ℤ) * spin a x) ↔
      ∃ (U : Submodule (ZMod 2) V) (z : V),
        ∀ x : V, F x = @ite ℕ (∀ a ∈ U, dot a x = dot a z)
          (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U)) 0) := by
  classical
  intro n V dot spin F total
  change (∀ a, (2:ℤ)^n ∣ transform (fun x => (F x : ℤ)) a) ↔
    ∃ (U : Submodule (ZMod 2) (Cube n)) (z : Cube n), ∀ x,
      F x = @ite ℕ (∀ a ∈ U, dotProduct a x = dotProduct a z) (Classical.propDecidable _) (2^Module.finrank (ZMod 2) U) 0
  constructor
  · intro hd
    obtain ⟨z,hz⟩ : ∃ z, F z ≠ 0 := by
      by_contra! h
      simp [h] at total
      exact (by positivity : 0 < (2:ℕ)^n).ne total
    let U := supportSpace F z
    refine ⟨U,z,?_⟩
    intro x
    have mulW := inv (fun i => (F i : ℤ)) x
    have freq (a : Cube n) : transform (fun i => (F i : ℤ)) a = (2:ℤ)^n * spec U z a :=
      spectral F total z hz hd a
    change (∑ a, transform (fun i => (F i : ℤ)) a * ch x a) = _ at mulW
    simp_rw [freq,mul_assoc] at mulW
    rw [← Finset.mul_sum] at mulW
    change (2:ℤ)^n * transform (spec U z) x = (2:ℤ)^n * (F x : ℤ) at mulW
    have heq : (F x : ℤ) = transform (spec U z) x := by
      exact (mul_left_cancel₀ (by positivity : (2:ℤ)^n ≠ 0) mulW).symm
    rw [transform_spec] at heq
    split_ifs at heq ⊢ <;> exact_mod_cast heq
  · rintro ⟨U,z,h⟩ a
    have feq : (fun x => (F x : ℤ)) = transform (spec U z) := by
      funext x
      rw [transform_spec,h x]
      split_ifs <;> simp
    rw [feq,inv]
    exact dvd_mul_right _ _


def weight {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (x : Cube d) : ℕ :=
  (Finset.univ.filter (fun i => dotProduct (row i) x + off i = 1)).card

def bal {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (a : Cube d) : ℤ :=
  ((Finset.univ.filter (fun i => row i = a ∧ off i = 1)).card : ℤ) -
    ((Finset.univ.filter (fun i => row i = a ∧ off i = 0)).card : ℤ)

theorem bal_zero {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (hr : ∀ i, row i ≠ 0) : bal row off 0 = 0 := by
  simp [bal,hr]

theorem bal_sum {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (a : Cube d) :
    bal row off a = ∑ i, if row i = a then -sgn (off i) else 0 := by
  classical
  unfold bal
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : row i = a
  · simp only [he,true_and,ite_true]
    generalize off i = b
    revert b
    decide
  · simp [he]

theorem signed_bit (t b : ZMod 2) :
    -sgn b * sgn t = 2 * (if t+b=1 then (1:ℤ) else 0) - 1 := by
  revert t b
  decide

theorem weight_formula {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (x : Cube d) :
    transform (bal row off) x = 2 * (weight row off x : ℤ) - m := by
  classical
  unfold transform
  simp_rw [bal_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  have singleton (i : Fin m) : (∑ a : Cube d, (if row i = a then -sgn (off i) else 0) * ch x a) =
      -sgn (off i) * sgn (dotProduct (row i) x) := by
    simp [ite_mul, ch, dotProduct_comm]
  simp_rw [singleton,signed_bit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,Finset.sum_boole]
  simp [weight]

theorem at_zero {d : ℕ} (f : Cube d → ℤ) : transform f 0 = ∑ x, f x := by
  simp [transform,ch,sgn]

theorem zero_of_sign {d : ℕ} (b : Cube d → ℤ) (bz : b 0 = 0)
    (hn : ∀ x, 0 ≤ transform b x) : ∀ a, b a = 0 := by
  classical
  have sumzero := inv b 0
  rw [at_zero,bz,mul_zero] at sumzero
  have zerof : transform b = 0 := by
    funext x
    exact ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp sumzero) x (Finset.mem_univ _)
  intro a
  have ha := inv b a
  rw [zerof] at ha
  simpa [transform] using ha.symm

noncomputable def bump {d : ℕ} (b : Cube d → ℤ) (a : Cube d) : ℤ :=
  b a + if a=0 then 1 else 0

theorem transform_bump {d : ℕ} (b : Cube d → ℤ) (x : Cube d) :
    transform (bump b) x = transform b x + 1 := by
  classical
  simp only [transform,bump,add_mul,Finset.sum_add_distrib]
  congr 1
  simp only [ite_mul,one_mul,zero_mul]
  simp [ch,sgn]

theorem odd_profile {m d g : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (hr : ∀ i, row i ≠ 0) (hm : m = 2*g+1) (hg : ∀ x, g ≤ weight row off x) :
    ∃ (U : Submodule (ZMod 2) (Cube d)) (z : Cube d), 0 < Module.finrank (ZMod 2) U ∧
      (∀ a, bal row off a = @ite ℤ (a ∈ U ∧ a ≠ 0) (Classical.propDecidable _) (ch a z) 0) ∧
      ∀ x, weight row off x = g + @ite ℕ (∀ a ∈ U, dotProduct a x = dotProduct a z)
        (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U-1)) 0 := by
  classical
  let b := bal row off
  let Q := bump b
  let F (x : Cube d) := 2*(weight row off x-g)
  have bz : b 0 = 0 := bal_zero row off hr
  have qz : Q 0 = 1 := by simp [Q,bump,bz]
  have point (x : Cube d) : (F x : ℤ) = transform Q x := by
    change ((2*(weight row off x-g) : ℕ) : ℤ) = transform (bump (bal row off)) x
    rw [transform_bump,weight_formula,Nat.cast_mul,Nat.cast_sub (hg x)]
    norm_num
    omega
  have fspec (a : Cube d) : transform (fun x => (F x : ℤ)) a = (2:ℤ)^d * Q a := by
    have equal : (fun x => (F x : ℤ)) = transform Q := funext point
    rw [equal,inv]
  have mass : (∑ x, F x) = 2^d := by
    have hz := fspec 0
    rw [at_zero,qz,mul_one] at hz
    exact_mod_cast hz
  obtain ⟨U,z,form⟩ := (classify d F mass).mp (fun a => ⟨Q a,fspec a⟩)
  have shape (x : Cube d) : F x =
      @ite ℕ (∀ a ∈ U, dotProduct a x = dotProduct a z) (Classical.propDecidable _)
        (2^Module.finrank (ZMod 2) U) 0 := form x
  have fx : (fun x => (F x : ℤ)) = transform (spec U z) := by
    funext x
    rw [transform_spec,shape]
    split_ifs <;> simp
  have specQ (a : Cube d) : Q a = spec U z a := by
    have lhs := fspec a
    rw [fx,inv] at lhs
    exact (mul_left_cancel₀ (by positivity : (2:ℤ)^d ≠ 0) lhs).symm
  have rankpos : 0 < Module.finrank (ZMod 2) U := by
    by_contra! hz
    have h := shape z
    have rz : Module.finrank (ZMod 2) U = 0 := by omega
    have yes : ∀ a ∈ U, dotProduct a z = dotProduct a z := by simp
    rw [if_pos yes,rz,pow_zero] at h
    dsimp only [F] at h
    omega
  refine ⟨U,z,rankpos,?_,?_⟩
  · intro a
    by_cases ha : a = 0
    · subst a
      simpa using bz
    · have h := specQ a
      simpa [Q,bump,ha,spec,b] using h
  · intro x
    have h := shape x
    have hgx := hg x
    dsimp only [F] at h
    have p : 2^Module.finrank (ZMod 2) U = 2^(Module.finrank (ZMod 2) U-1) * (2:ℕ) := by
      conv_lhs => rw [← Nat.sub_add_cancel rankpos]
      rw [pow_succ]
    rw [p] at h
    by_cases yes : ∀ a ∈ U, dotProduct a x = dotProduct a z
    · rw [if_pos yes] at h ⊢
      have cut : weight row off x - g = 2^(Module.finrank (ZMod 2) U-1) := by
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (h.trans (Nat.mul_comm _ _))
      calc
        _ = (weight row off x - g) + g := (Nat.sub_add_cancel hgx).symm
        _ = _ := by rw [cut,Nat.add_comm]
    · rw [if_neg yes] at h ⊢
      omega

end PEqualNP.Outside.L_lib_639_aux

open PEqualNP.Outside.L_lib_639_aux in
theorem PEqualNP.Outside.L_lib_639 : ∀ (m d : ℕ),
  let V := Fin d → ZMod 2
  let dot := fun (a x : V) => ∑ i, a i * x i
  ∀ (row : Fin m → V) (off : Fin m → ZMod 2), (∀ i, row i ≠ 0) →
    let wt := fun x : V => (Finset.univ.filter (fun i => dot (row i) x + off i = 1)).card
    let balance := fun a : V =>
      (((Finset.univ.filter (fun i => row i = a ∧ off i = 1)).card : ℤ) -
        ((Finset.univ.filter (fun i => row i = a ∧ off i = 0)).card : ℤ))
    ∀ g : ℕ,
      (m = 2*g → ((∀ x, g ≤ wt x) ↔ ∀ a : V, balance a = 0)) ∧
      (m = 2*g+1 → ((∀ x, g ≤ wt x) ↔
        ∃ (U : Submodule (ZMod 2) V) (z : V), 0 < Module.finrank (ZMod 2) U ∧
          (∀ a : V, balance a = @ite ℤ (a ∈ U ∧ a ≠ 0) (Classical.propDecidable _)
            (if dot a z = 0 then 1 else -1) 0) ∧
          ∀ x : V, wt x = g + @ite ℕ (∀ a ∈ U, dot a x = dot a z)
            (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U - 1)) 0)) := by
  classical
  intro m d V dot row off hr wt balance g
  constructor
  · intro hm
    constructor
    · intro hg
      apply zero_of_sign (bal row off) (bal_zero row off hr)
      intro x
      rw [weight_formula]
      have hx : g ≤ weight row off x := hg x
      omega
    · intro hb x
      have hf : bal row off = 0 := funext hb
      have h := weight_formula row off x
      rw [hf] at h
      simp [transform] at h
      change g ≤ weight row off x
      omega
  · intro hm
    constructor
    · exact fun hg => odd_profile row off hr hm hg
    · rintro ⟨U,z,_,_,h⟩ x
      rw [h x]
      omega

