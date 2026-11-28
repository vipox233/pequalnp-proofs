import PEqualNP.Defs

/-! Rank-two block reduction and the bilinear Witt bound on the centred row and column factors. -/

namespace PEqualNP.Outside.L_gct_309.PivotCore

variable {K S W : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S]

structure Pivot (K S W : Type*) [Field K] [AddCommGroup S] [Module K S] where
  p : S →ₗ[K] K
  q : S →ₗ[K] K
  a : S →ₗ[K] K
  b : S →ₗ[K] K
  c : S →ₗ[K] K
  d : S →ₗ[K] K
  u : W → S →ₗ[K] K
  v : W → S →ₗ[K] K
  quad : ∀ s w, p s * u w s + q s * v w s = 0
  cubic : ∀ s w, p s * (a s * u w s + b s * v w s) +
    q s * (c s * u w s + d s * v w s) = 0

namespace Pivot

def det3 (a b u c d v p q z : K) : K :=
  a * (d*z-v*q) - b * (c*z-v*p) + u * (c*q-d*p)

theorem detData (a b u c d v p q z : K)
    (h : det3 a b u c d v p q z = 0)
    (hp : det3 (1+a) b u c (1+d) v p q z = 0)
    (hm : det3 (1-a) (-b) (-u) (-c) (1-d) (-v) (-p) (-q) (-z) = 0) :
    z = 0 ∧ p*u+q*v = 0 ∧
      p*(a*u+b*v)+q*(c*u+d*v) = 0 := by
  simp only [det3] at h hp hm
  have h₂ : (2:K) ≠ 0 := (OfNat.ofNat_ne_zero 2)
  have e : (2:K)*z = 0 := by
    linear_combination hp - hm - 2*h
  have hz : z = 0 := (mul_eq_zero.mp e).resolve_left h₂
  rw [hz] at h hp hm
  have e' : (2:K)*(p*u+q*v) = 0 := by
    linear_combination -hp - hm
  have hq : p*u+q*v = 0 := (mul_eq_zero.mp e').resolve_left h₂
  refine ⟨hz,hq,?_⟩
  linear_combination h + (a+d)*hq

variable (P : Pivot K S W)

theorem polar (x y : S) (w : W) :
    P.p x * P.u w y + P.q x * P.v w y +
      (P.p y * P.u w x + P.q y * P.v w x) = 0 := by
  have hh := P.quad (x+y) w
  simp only [map_add] at hh
  linear_combination hh - P.quad x w - P.quad y w

theorem inLine {p q x y : K} (hn : p ≠ 0 ∨ q ≠ 0) (hh : p*y=q*x) :
    ∃ t : K, x=t*p ∧ y=t*q := by
  by_cases hp : p=0
  · have hq : q≠0 := hn.resolve_left (fun e => e hp)
    have hqx : q*x=0 := by simpa [hp] using hh.symm
    have hx : x=0 := (mul_eq_zero.mp hqx).resolve_left hq
    refine ⟨y/q, by simp [hx,hp], ?_⟩
    exact (div_mul_cancel₀ y hq).symm
  · refine ⟨x/p, (div_mul_cancel₀ x hp).symm, ?_⟩
    have h₀ : (x/p*q-y)*p = 0 := by
      linear_combination q * (div_mul_cancel₀ x hp) - hh
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_right hp)).symm

private theorem hasBoth (F G : S →ₗ[K] K)
    (hf : ∃ x, F x ≠ 0) (hg : ∃ x, G x ≠ 0) :
    ∃ x, F x ≠ 0 ∧ G x ≠ 0 := by
  obtain ⟨x,hx⟩ := hf
  obtain ⟨y,hy⟩ := hg
  by_cases hGx : G x = 0
  · by_cases hFy : F y = 0
    · exact ⟨x+y, by simpa [map_add,hFy] using hx, by simpa [map_add,hGx] using hy⟩
    · exact ⟨y,hFy,hy⟩
  · exact ⟨x,hx,hGx⟩

theorem vanishesOffTwo (F G H : S →ₗ[K] K)
    (hf : ∃ x, F x ≠ 0) (hg : ∃ x, G x ≠ 0)
    (h : ∀ x, F x ≠ 0 → G x ≠ 0 → H x = 0) :
    ∀ x, H x = 0 := by
  obtain ⟨y,hfY,hgY⟩ := hasBoth F G hf hg
  have hy : H y = 0 := h y hfY hgY
  have prod : ∀ x, H x ≠ 0 → F x * G x = 0 := by
    intro x hx
    by_cases hxF : F x = 0
    · simp [hxF]
    by_cases hxG : G x = 0
    · simp [hxG]
    exact (hx (h x hxF hxG)).elim
  intro x
  by_contra hx
  have hx0 := prod x hx
  have hxp := prod (x+y) (by simpa [map_add,hy] using hx)
  have hxm := prod (x-y) (by simpa [map_sub,hy] using hx)
  simp only [map_add,map_sub] at hxp hxm
  have hz : (2:K) * (F y * G y) = 0 := by
    linear_combination hxp + hxm - 2 * hx0
  exact (mul_ne_zero ((OfNat.ofNat_ne_zero 2)) (mul_ne_zero hfY hgY)) hz

def PureImage : Prop := ∀ x, P.p x = 0 ∧ P.q x = 0
def PureKernel : Prop := ∀ x w, P.u w x = 0 ∧ P.v w x = 0

def form (z : S) : S →ₗ[K] K :=
  P.p z • (P.q z • P.a - P.p z • P.b) +
    P.q z • (P.q z • P.c - P.p z • P.d)

theorem form_apply (z x : S) :
    P.form z x = P.p z * (P.a x * P.q z - P.b x * P.p z) +
      P.q z * (P.c x * P.q z - P.d x * P.p z) := by
  simp only [form,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  ring1

def Mixed : Prop := ∃ z, (P.p z ≠ 0 ∨ P.q z ≠ 0) ∧
    (∀ x, P.p z * P.q x = P.q z * P.p x) ∧
    (∀ x w, P.p z * P.u w x + P.q z * P.v w x = 0) ∧
    (∀ x, P.form z x = 0)

private theorem oneDirection (z : S) (hz : P.p z ≠ 0 ∨ P.q z ≠ 0)
    (line : ∀ x, P.p z * P.q x = P.q z * P.p x)
    (hC : ¬ P.PureKernel) : P.Mixed := by
  classical
  have bline : ∀ x, ∃ t : K, P.p x=t*P.p z ∧ P.q x=t*P.q z :=
    fun x => inLine hz (line x)
  have orth : ∀ x w, P.p z * P.u w x + P.q z * P.v w x = 0 := by
    intro x w
    obtain ⟨t,hp,hq⟩ := bline x
    have hh := P.polar z x w
    rw [hp,hq] at hh
    linear_combination hh - t * P.quad z w
  have cline : ∀ x w, ∃ t : K, P.u w x=t*P.q z ∧ P.v w x=t*(-P.p z) := by
    intro x w
    apply inLine
    · rcases hz with hz|hz
      · exact Or.inr (neg_ne_zero.mpr hz)
      · exact Or.inl hz
    · linear_combination orth x w
  have hc : ∃ w, (∃ x, P.u w x ≠ 0) ∨ (∃ x, P.v w x ≠ 0) := by
    classical
    by_contra h
    apply hC
    intro x w
    exact ⟨by by_contra e; exact h ⟨w, Or.inl ⟨x,e⟩⟩,
      by by_contra e; exact h ⟨w, Or.inr ⟨x,e⟩⟩⟩
  obtain ⟨w,hw⟩ := hc
  let F : S →ₗ[K] K := if P.p z = 0 then P.q else P.p
  let G : S →ₗ[K] K := if ∃ x, P.u w x ≠ 0 then P.u w else P.v w
  have hf : ∃ x, F x ≠ 0 := by
    refine ⟨z,?_⟩
    rcases eq_or_ne (P.p z) 0 with h|h
    · simpa [F,h] using hz.resolve_left (fun e => e h)
    · simpa [F,h] using h
  have hg : ∃ x, G x ≠ 0 := by
    by_cases h : ∃ x, P.u w x ≠ 0
    · simpa [G,h] using h
    · simpa [G,h] using hw.resolve_left h
  refine ⟨z,hz,line,orth,vanishesOffTwo F G (P.form z) hf hg ?_⟩
  intro x hFx hGx
  obtain ⟨r,hp,hq⟩ := bline x
  obtain ⟨t,hu,hv⟩ := cline x w
  have hr : r ≠ 0 := by
    intro h
    have e₀ : P.p x = 0 := by simp [hp,h]
    have e₁ : P.q x = 0 := by simp [hq,h]
    apply hFx
    by_cases hF : P.p z = 0 <;> simp [F,hF,e₀,e₁]
  have ht : t ≠ 0 := by
    intro h
    have e₀ : P.u w x = 0 := by simp [hu,h]
    have e₁ : P.v w x = 0 := by simp [hv,h]
    apply hGx
    by_cases hG : ∃ u, P.u w u ≠ 0 <;> simp [G,hG,e₀,e₁]
  have hpv := P.cubic x w
  rw [hp,hq,hu,hv] at hpv
  have hz' : (r*t)*P.form z x = 0 := by
    rw [P.form_apply]
    linear_combination hpv
  exact (mul_eq_zero.mp hz').resolve_left (mul_ne_zero hr ht)

def Faithful : Prop := ∀ x, P.p x = 0 → P.q x = 0 →
    P.a x = 0 → P.b x = 0 → P.c x = 0 → P.d x = 0 →
    (∀ w, P.u w x = 0 ∧ P.v w x = 0) → x = 0

def Small : Prop := ∀ x, P.p x = 0 → P.q x = 0 → P.a x = 0 → x = 0

private theorem twoDirections (x₀ x₁ : S)
    (hp₀ : P.p x₀ = 1) (hq₀ : P.q x₀ = 0)
    (hp₁ : P.p x₁ = 0) (hq₁ : P.q x₁ = 1)
    (hf : P.Faithful) (hC : ¬ P.PureKernel) :
    P.Small := by
  have onKernel : ∀ x, P.p x=0 → P.q x=0 → ∀ w, P.u w x=0 ∧ P.v w x=0 := by
    intro x hp hq w
    constructor
    · simpa [hp,hq,hp₀,hq₀] using P.polar x x₀ w
    · simpa [hp,hq,hp₁,hq₁] using P.polar x x₁ w
  have sy : ∀ w, P.u w x₁ = -(P.v w x₀) := by
    intro w
    have h := P.polar x₀ x₁ w
    simp only [hp₀,hq₀,hp₁,hq₁, one_mul,zero_mul,add_zero,zero_add] at h
    linear_combination h
  have xu : ∀ w, P.u w x₀ = 0 := by
    intro w
    simpa [hp₀,hq₀] using P.quad x₀ w
  have xv : ∀ w, P.v w x₁ = 0 := by
    intro w
    simpa [hp₁,hq₁] using P.quad x₁ w
  have express : ∀ x w, P.u w x = -P.q x * P.v w x₀ ∧ P.v w x = P.p x * P.v w x₀ := by
    intro x w
    have h := P.polar x x₀ w
    have h' := P.polar x x₁ w
    simp only [hp₀,hq₀,xu w, one_mul,zero_mul,add_zero,zero_add] at h
    simp only [hp₁,hq₁,xv w,sy w,one_mul,zero_mul,add_zero,zero_add] at h'
    refine ⟨?_,?_⟩
    · linear_combination h
    · linear_combination h'
  have hn : ∃ w, P.v w x₀ ≠ 0 := by
    classical
    by_contra hh
    apply hC
    intro x w
    have hz : P.v w x₀ = 0 := by
      by_contra hz'
      exact hh ⟨w,hz'⟩
    have h := express x w
    simpa [hz] using h
  obtain ⟨w,hw⟩ := hn
  have reduced : ∀ x, P.p x * (-P.a x * P.q x + P.b x * P.p x) +
      P.q x * (-P.c x * P.q x + P.d x * P.p x) = 0 := by
    intro x
    have h := P.cubic x w
    rw [(express x w).1,(express x w).2] at h
    have hz : (P.p x * (-P.a x * P.q x + P.b x * P.p x) +
      P.q x * (-P.c x * P.q x + P.d x * P.p x)) * P.v w x₀ = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hz).resolve_right hw
  intro x hp hq ha
  have hx₀ := reduced (x₀+x)
  have hx₁ := reduced (x₁+x)
  have h₀ := reduced x₀
  have h₁ := reduced x₁
  simp only [map_add,hp,hq,hp₀,hq₀,hp₁,hq₁, add_zero, mul_one,zero_mul,mul_zero,
    one_mul,zero_add,neg_zero] at hx₀ hx₁ h₀ h₁
  have hb : P.b x = 0 := by linear_combination hx₀ - h₀
  have hc : P.c x = 0 := by linear_combination h₁ - hx₁
  have hxy := reduced (x₀+x₁+x)
  have hy := reduced (x₀+x₁)
  simp only [map_add,hp,hq,hp₀,hq₀,hp₁,hq₁,ha,hb,hc, add_zero,zero_add,
    mul_one,zero_mul,mul_zero,one_mul,neg_zero] at hxy hy
  have hd : P.d x = 0 := by linear_combination hxy - hy
  exact hf x hp hq ha hb hc hd (onKernel x hp hq)

theorem classify (hf : P.Faithful) :
    P.PureImage ∨ P.PureKernel ∨ P.Mixed ∨ P.Small := by
  classical
  by_cases hB : P.PureImage
  · exact Or.inl hB
  by_cases hC : P.PureKernel
  · exact Or.inr (Or.inl hC)
  have hZ : ∃ z, P.p z ≠ 0 ∨ P.q z ≠ 0 := by
    by_contra h
    apply hB
    intro z
    exact ⟨by by_contra h'; exact h ⟨z,Or.inl h'⟩,
      by by_contra h'; exact h ⟨z,Or.inr h'⟩⟩
  obtain ⟨z,hz⟩ := hZ
  by_cases hLine : ∀ x, P.p z * P.q x = P.q z * P.p x
  · exact Or.inr (Or.inr (Or.inl (P.oneDirection z hz hLine hC)))
  obtain ⟨y,hy⟩ := not_forall.mp hLine
  let Δ := P.p z * P.q y - P.q z * P.p y
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr hy
  let x₀ := Δ⁻¹ • (P.q y • z - P.q z • y)
  let x₁ := Δ⁻¹ • (P.p z • y - P.p y • z)
  have hp₀ : P.p x₀ = 1 := by
    simp only [x₀,map_sub,map_smul,smul_eq_mul]
    rw [show P.q y * P.p z - P.q z * P.p y = Δ by unfold Δ; ring1]
    exact inv_mul_cancel₀ hΔ
  have hq₀ : P.q x₀ = 0 := by
    simp only [x₀,map_sub,map_smul,smul_eq_mul]
    ring1
  have hp₁ : P.p x₁ = 0 := by
    simp only [x₁,map_sub,map_smul,smul_eq_mul]
    ring1
  have hq₁ : P.q x₁ = 1 := by
    simp only [x₁,map_sub,map_smul,smul_eq_mul]
    rw [show P.p z * P.q y - P.p y * P.q z = Δ by unfold Δ; ring1]
    exact inv_mul_cancel₀ hΔ
  exact Or.inr (Or.inr (Or.inr (P.twoDirections x₀ x₁ hp₀ hq₀ hp₁ hq₁ hf hC)))

end Pivot
end PEqualNP.Outside.L_gct_309.PivotCore

open Module
open scoped BigOperators

namespace PEqualNP.Outside.L_gct_309.PivotCore

variable {K S D : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S] [AddCommGroup D] [Module K D]

abbrev Target (K : Type*) := Fin 3 → K

def evalSlot (T : S →ₗ[K] D →ₗ[K] Target K) (i : Fin 3) (x : D) : S →ₗ[K] K where
  toFun s := T s x i
  map_add' s t := by simp only [map_add,LinearMap.add_apply,Pi.add_apply]
  map_smul' r s := by simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

@[simp] theorem evalSlot_apply (T : S →ₗ[K] D →ₗ[K] Target K)
    (i : Fin 3) (x : D) (s : S) : evalSlot T i x s = T s x i := rfl

def coord (T : D →ₗ[K] Target K) (i : Fin 3) : D →ₗ[K] K :=
  (LinearMap.proj i).comp T

@[simp] theorem coord_apply (T : D →ₗ[K] Target K) (i : Fin 3) (x : D) :
    coord T i x = T x i := rfl

theorem cutDet (A : D →ₗ[K] Target K) (hA : finrank K (LinearMap.range A) ≤ 2)
    (cols : Fin 3 → D) : (Matrix.of fun (i j : Fin 3) => A (cols j) i).det = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => A (cols j) i
  change M.det = 0
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.range A := by
    rintro _ ⟨x,rfl⟩
    refine ⟨∑ j, x j • cols j, ?_⟩
    ext i
    simp only [map_sum,map_smul,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,M,Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hr : M.rank ≤ 2 := (Submodule.finrank_mono hle).trans hA
  by_contra hd
  have h3 := Matrix.rank_of_det_ne_zero hd
  rw [Fintype.card_fin] at h3
  omega

structure Normalized (K S D : Type*) [Field K] [AddCommGroup S] [Module K S]
    [AddCommGroup D] [Module K D] where
  T : S →ₗ[K] D →ₗ[K] Target K
  faithful : Function.Injective T
  rank : ∀ s, finrank K (LinearMap.range (T s)) ≤ 2
  center : D
  vanishes : ∀ s, T s center = 0
  chosen : S
  x0 : D
  x1 : D
  at0 : T chosen x0 = ![1,0,0]
  at1 : T chosen x1 = ![0,1,0]
  at2 : ∀ x, T chosen x 2 = 0

variable {V : Type*} [AddCommGroup V] [Module K V]

def FixedImage (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ a b : V, LinearIndependent K ![a,b] ∧
    ∀ s, ∃ f g : D →ₗ[K] K, f center = 0 ∧ g center = 0 ∧
      ∀ x, T s x = f x • a + g x • b

def FixedKernel (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ f g : D →ₗ[K] K, f center = 0 ∧ g center = 0 ∧ LinearIndependent K ![f,g] ∧
    ∀ s, ∃ a b : V, ∀ x, T s x = f x • a + g x • b

def FixedLine (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ (a : V) (b : D →ₗ[K] K), a ≠ 0 ∧ b ≠ 0 ∧ b center = 0 ∧
    ∀ s, ∃ (f : D →ₗ[K] K) (y : V), f center = 0 ∧
      ∀ x, T s x = f x • a + b x • y

def ThreeShapes (T : S →ₗ[K] D →ₗ[K] V) (center : D) :=
  FixedImage T center ∨ FixedKernel T center ∨ FixedLine T center

theorem fixedLine_of_restrict (T : S →ₗ[K] D →ₗ[K] V) {center : D}
    (hCenter : ∀ s, T s center = 0)
    (a : V) (b : D →ₗ[K] K) (e : V →ₗ[K] K) (v : D)
    (ha : e a = 1) (hb : b v = 1) (hzero : b center = 0)
    (h : ∀ s x, b x = 0 → ∃ t : K, T s x = t • a) :
    FixedLine T center := by
  have hane : a ≠ 0 := by intro hz; simp [hz] at ha
  have hbne : b ≠ 0 := by intro hz; simp [hz] at hb
  refine ⟨a,b,hane,hbne,hzero,?_⟩
  intro s
  let M : D →ₗ[K] V := T s - b.smulRight (T s v)
  refine ⟨e.comp M, T s v, ?_, ?_⟩
  · simp [M,hCenter s,hzero,LinearMap.smulRight_apply]
  intro x
  let w := x - b x • v
  have hw : b w = 0 := by simp [w,hb,map_sub,map_smul,smul_eq_mul]
  obtain ⟨t,ht⟩ := h s w hw
  have hM : M x = t • a := by
    simpa [M,w,map_sub,map_smul,LinearMap.smulRight_apply] using ht
  change T s x = e (M x) • a + b x • T s v
  rw [hM, map_smul, ha, smul_eq_mul, mul_one, ← hM]
  simp [M,LinearMap.smulRight_apply]

namespace Normalized

variable (N : Normalized K S D)

abbrev Tail := LinearMap.ker (N.T N.chosen)
abbrev r0 := coord (N.T N.chosen) 0
abbrev r1 := coord (N.T N.chosen) 1

def tailPart (x : D) : N.Tail := ⟨x - N.r0 x • N.x0 - N.r1 x • N.x1, by
  rw [LinearMap.mem_ker]
  ext i
  fin_cases i <;>
    simp [r0,r1,map_sub,map_smul,Pi.sub_apply,smul_eq_mul,N.at0,N.at1,N.at2,
      Matrix.vecHead,Matrix.vecTail,Fin.succ_zero_eq_one]⟩

theorem split (x : D) : x = N.r0 x • N.x0 + N.r1 x • N.x1 + (N.tailPart x : D) := by
  change x = _ + _ + (x - _ - _)
  abel

theorem cutStencil (s : S) (w : N.Tail) :
    N.T s (w : D) 2 = 0 ∧
    N.T s N.x0 2 * N.T s (w : D) 0 + N.T s N.x1 2 * N.T s (w : D) 1 = 0 ∧
    N.T s N.x0 2 * (N.T s N.x0 0 * N.T s (w : D) 0 + N.T s N.x1 0 * N.T s (w : D) 1) +
    N.T s N.x1 2 * (N.T s N.x0 1 * N.T s (w : D) 0 + N.T s N.x1 1 * N.T s (w : D) 1) = 0 := by
  let cols : Fin 3 → D := ![N.x0,N.x1,(w : D)]
  let a := N.T s N.x0 0
  let b := N.T s N.x1 0
  let u := N.T s (w : D) 0
  let c := N.T s N.x0 1
  let d := N.T s N.x1 1
  let v := N.T s (w : D) 1
  let p := N.T s N.x0 2
  let q := N.T s N.x1 2
  let z := N.T s (w : D) 2
  have unfoldDet (t : S) :
      (Matrix.of fun (i j : Fin 3) => N.T t (cols j) i).det =
      Pivot.det3 (N.T t N.x0 0) (N.T t N.x1 0) (N.T t (w : D) 0)
        (N.T t N.x0 1) (N.T t N.x1 1) (N.T t (w : D) 1)
        (N.T t N.x0 2) (N.T t N.x1 2) (N.T t (w : D) 2) := by
    rw [Matrix.det_fin_three]
    simp only [cols,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      Pivot.det3]
    ring1
  have h (t : S) := (unfoldDet t).symm.trans (cutDet (N.T t) (N.rank t) cols)
  have hw : N.T N.chosen (w : D) = 0 := w.property
  have hp := h (N.chosen+s)
  have hm := h (N.chosen-s)
  simp only [map_add,LinearMap.add_apply,Pi.add_apply,N.at0,N.at1,hw,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,zero_add] at hp
  simp only [map_sub,LinearMap.sub_apply,Pi.sub_apply,N.at0,N.at1,hw,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,zero_sub] at hm
  exact Pivot.detData a b u c d v p q z (h s) hp hm

def pivot : Pivot K S N.Tail where
  p := evalSlot N.T 2 N.x0
  q := evalSlot N.T 2 N.x1
  a := evalSlot N.T 0 N.x0
  b := evalSlot N.T 0 N.x1
  c := evalSlot N.T 1 N.x0
  d := evalSlot N.T 1 N.x1
  u w := evalSlot N.T 0 w
  v w := evalSlot N.T 1 w
  quad s w := (N.cutStencil s w).2.1
  cubic s w := (N.cutStencil s w).2.2

theorem pivot_faithful : N.pivot.Faithful := by
  intro s hp hq ha hb hc hd ht
  apply N.faithful
  rw [map_zero]
  ext x i
  have h0 : N.T s N.x0 = 0 := by
    ext i
    fin_cases i
    · exact ha
    · exact hc
    · exact hp
  have h1 : N.T s N.x1 = 0 := by
    ext i
    fin_cases i
    · exact hb
    · exact hd
    · exact hq
  have hTail (w : N.Tail) : N.T s w = 0 := by
    ext i
    fin_cases i
    · exact (ht w).1
    · exact (ht w).2
    · exact (N.cutStencil s w).1
  rw [N.split x]
  simp only [map_add,map_smul,h0,h1,hTail,smul_zero,add_zero,LinearMap.zero_apply]

theorem splitValues (s : S) (x : D) :
    N.T s x = N.r0 x • N.T s N.x0 + N.r1 x • N.T s N.x1 + N.T s (N.tailPart x : D) := by
  conv_lhs => rw [N.split x]
  simp only [map_add,map_smul]

theorem r00 : N.r0 N.x0 = 1 := by simp [r0,N.at0]
theorem r01 : N.r0 N.x1 = 0 := by simp [r0,N.at1]
theorem r10 : N.r1 N.x0 = 0 := by simp [r1,N.at0]
theorem r11 : N.r1 N.x1 = 1 := by simp [r1,N.at1]

theorem pImage (hh : N.pivot.PureImage) : FixedImage N.T N.center := by
  let a : Target K := ![1,0,0]
  let b : Target K := ![0,1,0]
  refine ⟨a,b,?_,?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro h; have e := congrFun h 1
      simp [b] at e
    · intro c h; have e := congrFun h 0
      simp [a,b,Pi.smul_apply] at e
  intro s
  refine ⟨coord (N.T s) 0,coord (N.T s) 1, by simp [N.vanishes],by simp [N.vanishes],?_⟩
  intro x
  have hx : N.T s x 2 = 0 := by
    have h₀ : N.T s N.x0 2 = 0 := (hh s).1
    have h₁ : N.T s N.x1 2 = 0 := (hh s).2
    rw [N.splitValues s x]
    simp [h₀,h₁,(N.cutStencil s (N.tailPart x)).1]
  ext i
  fin_cases i <;> simp [a,b,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hx,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem pKernel (hh : N.pivot.PureKernel) : FixedKernel N.T N.center := by
  refine ⟨N.r0,N.r1,by simp [r0,N.vanishes],by simp [r1,N.vanishes],?_,?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro h; have e := DFunLike.congr_fun h N.x1; simp [N.r11] at e
    · intro c h; have e := DFunLike.congr_fun h N.x0
      simp [N.r10,N.r00,LinearMap.smul_apply] at e
  intro s
  refine ⟨N.T s N.x0,N.T s N.x1,?_⟩
  intro x
  rw [N.splitValues s x]
  have ht : N.T s (N.tailPart x : D) = 0 := by
    ext i
    fin_cases i
    · exact (hh s (N.tailPart x)).1
    · exact (hh s (N.tailPart x)).2
    · exact (N.cutStencil s (N.tailPart x)).1
  rw [ht,add_zero]

theorem pMixed (hh : N.pivot.Mixed) : FixedLine N.T N.center := by
  obtain ⟨z,hz,hline,horth,hform⟩ := hh
  let p := N.pivot.p z
  let q := N.pivot.q z
  let a : Target K := ![q,-p,0]
  let b : D →ₗ[K] K := p • N.r0 + q • N.r1
  have hb (x : D) : b x = p*N.r0 x+q*N.r1 x := by
    simp only [b,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  have center : b N.center = 0 := by simp [hb,r0,r1,N.vanishes]
  have hR : ∀ s x, b x = 0 → ∃ t : K, N.T s x = t • a := by
    intro s x hx
    have hne : q ≠ 0 ∨ -p ≠ 0 := by
      rcases hz with h|h
      · exact Or.inr (neg_ne_zero.mpr h)
      · exact Or.inl h
    obtain ⟨v,hv₀,hv₁⟩ := Pivot.inLine hne (show q*N.r1 x=(-p)*N.r0 x by
      rw [hb] at hx
      linear_combination hx)
    have h02 : N.T s x 2 = 0 := by
      rw [N.splitValues s x]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,(N.cutStencil s (N.tailPart x)).1,
        hv₀,hv₁,add_zero]
      have e : p * N.T s N.x1 2 = q * N.T s N.x0 2 := hline s
      linear_combination -v*e
    have ho : p*N.T s x 0+q*N.T s x 1=0 := by
      rw [N.splitValues s x]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hv₀,hv₁]
      have h₁ : p*N.T s (N.tailPart x : D) 0+q*N.T s (N.tailPart x : D) 1=0 :=
        horth s (N.tailPart x)
      have h₂ := hform s
      rw [Pivot.form_apply] at h₂
      change p*(N.T s N.x0 0*q - N.T s N.x1 0*p) +
        q*(N.T s N.x0 1*q - N.T s N.x1 1*p) = 0 at h₂
      linear_combination h₁ + v*h₂
    obtain ⟨t,h₀,h₁⟩ := Pivot.inLine hne (show q*N.T s x 1=(-p)*N.T s x 0 by
      linear_combination ho)
    refine ⟨t,?_⟩
    ext i
    fin_cases i <;> simp [a,h₀,h₁,h02,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  obtain ⟨e,he⟩ : ∃ e : Target K →ₗ[K] K, e a = 1 := by
    rcases hz with h|h
    · refine ⟨(-p)⁻¹ • LinearMap.proj 1,?_⟩
      change (-p)⁻¹ * (-p) = 1
      exact inv_mul_cancel₀ (neg_ne_zero.mpr (show p ≠ 0 from h))
    · refine ⟨q⁻¹ • LinearMap.proj 0,?_⟩
      change q⁻¹ * q = 1
      exact inv_mul_cancel₀ (show q ≠ 0 from h)
  obtain ⟨v,hv⟩ : ∃ v : D, b v = 1 := by
    rcases hz with h|h
    · refine ⟨p⁻¹ • N.x0,?_⟩
      have h0 : b N.x0 = p := by simp [hb,N.r00,N.r10]
      rw [map_smul,h0,smul_eq_mul,inv_mul_cancel₀ h]
    · refine ⟨q⁻¹ • N.x1,?_⟩
      have h1 : b N.x1 = q := by simp [hb,N.r01,N.r11]
      rw [map_smul,h1,smul_eq_mul,inv_mul_cancel₀ h]
  exact fixedLine_of_restrict N.T N.vanishes a b e v he hv center hR

theorem classification (hLarge : 3 < finrank K S) : ThreeShapes N.T N.center := by
  rcases N.pivot.classify N.pivot_faithful with hi|hk|hm|hs
  · exact Or.inl (N.pImage hi)
  · exact Or.inr (Or.inl (N.pKernel hk))
  · exact Or.inr (Or.inr (N.pMixed hm))
  let f := N.pivot.p.prod (N.pivot.q.prod N.pivot.a)
  have h : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun s h => ?_
    exact hs s (congrArg Prod.fst h) (congrArg (fun p => p.2.1) h)
      (congrArg (fun p => p.2.2) h)
  have hf : finrank K S ≤ 3 := by simpa using f.finrank_le_finrank_of_injective h
  omega

end Normalized
end PEqualNP.Outside.L_gct_309.PivotCore

open Module
open scoped BigOperators

namespace PEqualNP.Outside.L_gct_309.PivotCore

variable {K S D V : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S] [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem rankOneLaw (T : D →ₗ[K] V) (h : finrank K (LinearMap.range T) ≤ 1)
    (e : V →ₗ[K] K) (x v : D) : e (T x) • T v = e (T v) • T x := by
  obtain ⟨a,ha⟩ := finrank_le_one_iff.mp h
  obtain ⟨p,hp⟩ := ha ⟨T x,⟨x,rfl⟩⟩
  obtain ⟨q,hq⟩ := ha ⟨T v,⟨v,rfl⟩⟩
  have ep : p • (a : V) = T x := congrArg Subtype.val hp
  have eq : q • (a : V) = T v := congrArg Subtype.val hq
  simp only [← ep,← eq,map_smul,smul_eq_mul,smul_smul]
  congr 1 <;> ring1

theorem rankOneLine (T : S →ₗ[K] D →ₗ[K] V) (hT : Function.Injective T) (center : D)
    (hcenter : ∀ s, T s center = 0) (hsmall : ∀ s, finrank K (LinearMap.range (T s)) ≤ 1)
    (hLarge : 3 < finrank K S) :
    FixedLine T center := by
  classical
  have hex : ∃ (s : S) (v : D), T s v ≠ 0 := by
    by_contra h
    have hz : ∀ s, T s = 0 := by
      intro s
      ext v
      by_contra hv
      exact h ⟨s,v,hv⟩
    letI : Subsingleton S := ⟨fun a b => hT ((hz a).trans (hz b).symm)⟩
    have hz : finrank K S = 0 := Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨m,v,hv⟩ := hex
  let a := T m v
  obtain ⟨e,he⟩ := Module.Projective.exists_dual_eq_one K hv
  change e a = 1 at he
  let b := e.comp (T m)
  have hBV : b v = 1 := he
  have hBZ : b center = 0 := by simp [b,hcenter]
  refine fixedLine_of_restrict T hcenter a b e v he hBV hBZ ?_
  intro s x hx
  have hMx : T m x = 0 := by
    have h := rankOneLaw (T m) (hsmall m) e x v
    change b x • a = e a • T m x at h
    simpa [hx,he] using h.symm
  have h := rankOneLaw (T (m+s)) (hsmall (m+s)) e x v
  have he' : e (T m v) = 1 := he
  simp only [map_add,LinearMap.add_apply,hMx,zero_add,he',add_smul,smul_add,one_smul] at h
  have hr := rankOneLaw (T s) (hsmall s) e x v
  rw [hr] at h
  exact ⟨e (T s x),(add_right_cancel h).symm⟩

def post (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V) :
    S →ₗ[K] D →ₗ[K] Target K where
  toFun s := E.toLinearMap.comp (T s)
  map_add' s t := by ext x i; simp only [map_add,LinearMap.add_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Pi.add_apply]
  map_smul' c s := by ext x i; simp only [map_smul,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Pi.smul_apply,RingHom.id_apply]

@[simp] theorem post_eval (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V)
    (s : S) (x : D) : post E T s x = E (T s x) := rfl

theorem ofPost (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V) (center : D)
    (h : ThreeShapes (post E T) center) : ThreeShapes T center := by
  rcases h with h|h|h
  · obtain ⟨a,b,hi,h⟩ := h
    refine Or.inl ⟨E.symm a,E.symm b,?_,?_⟩
    · have h' := hi.map' E.symm.toLinearMap (LinearMap.ker_eq_bot.mpr E.symm.injective)
      convert h' using 1
      ext i
      fin_cases i <;> rfl
    intro s
    obtain ⟨f,g,hf,hg,h⟩ := h s
    refine ⟨f,g,hf,hg,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)
  · obtain ⟨f,g,hf,hg,hi,h⟩ := h
    refine Or.inr (Or.inl ⟨f,g,hf,hg,hi,?_⟩)
    intro s
    obtain ⟨a,b,h⟩ := h s
    refine ⟨E.symm a,E.symm b,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)
  · obtain ⟨a,b,ha,hb,hb0,h⟩ := h
    refine Or.inr (Or.inr ⟨E.symm a,b,?_,hb,hb0,?_⟩)
    · intro hz
      exact ha (E.symm.injective (hz.trans (map_zero E.symm).symm))
    intro s
    obtain ⟨f,y,hf,h⟩ := h s
    refine ⟨f,E.symm y,hf,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)

theorem classifySpace (T : S →ₗ[K] D →ₗ[K] V) (hT : Function.Injective T)
    (center : D) (hcenter : ∀ s, T s center = 0)
    (hrank : ∀ s, finrank K (LinearMap.range (T s)) ≤ 2)
    (hV : finrank K V = 3) (hS : 3 < finrank K S) : ThreeShapes T center := by
  classical
  by_cases hm : ∃ m, finrank K (LinearMap.range (T m)) = 2
  · obtain ⟨m,hm⟩ := hm
    let R := LinearMap.range (T m)
    have hR : finrank K R = 2 := hm
    obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := R) (n := 2) hR.ge
    let f' : Fin 2 → V := fun i => (f i : V)
    have hf' : LinearIndependent K f' := hf.map' R.subtype R.ker_subtype
    obtain ⟨b,hb⟩ := exists_linearIndependent_snoc_of_lt_finrank hf' (by omega : 2 < finrank K V)
    let B : Basis (Fin 3) K V := basisOfLinearIndependentOfCardEqFinrank hb (by simp [hV])
    have hB (i : Fin 2) : B (Fin.castSucc i) = f' i := by
      simp [B,basisOfLinearIndependentOfCardEqFinrank,Fin.snoc_castSucc]
    have hspan : Submodule.span K (Set.range f') = R := by
      apply Submodule.eq_of_le_of_finrank_eq
      · apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact (f i).property
      · rw [finrank_span_eq_card hf',hR,Fintype.card_fin]
    obtain ⟨v0,hv0⟩ := (f 0).property
    obtain ⟨v1,hv1⟩ := (f 1).property
    have hb0 : T m v0 = B 0 := hv0.trans (hB 0).symm
    have hb1 : T m v1 = B 1 := hv1.trans (hB 1).symm
    let E : V ≃ₗ[K] Target K := B.equivFun
    let U := post E T
    have hU : Function.Injective U := by
      intro x y hxy
      apply hT
      ext z
      apply E.injective
      exact congrArg (fun F : D →ₗ[K] Target K => F z) hxy
    have hUr (s : S) : finrank K (LinearMap.range (U s)) ≤ 2 := by
      change finrank K (LinearMap.range (E.toLinearMap.comp (T s))) ≤ 2
      rw [LinearMap.range_comp,LinearEquiv.finrank_map_eq]
      exact hrank s
    have hU0 : U m v0 = ![1,0,0] := by
      rw [show U m v0 = B.equivFun (T m v0) from rfl,hb0]
      ext i
      fin_cases i <;> exact B.equivFun_self _ _
    have hU1 : U m v1 = ![0,1,0] := by
      rw [show U m v1 = B.equivFun (T m v1) from rfl,hb1]
      ext i
      fin_cases i <;> exact B.equivFun_self _ _
    have hU2 (x : D) : U m x 2 = 0 := by
      have hle : Submodule.span K (Set.range f') ≤ LinearMap.ker (B.coord 2) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change B.coord 2 (f' i) = 0
        rw [← hB i, Basis.coord_apply, Basis.repr_self_apply]
        fin_cases i <;> simp
      have hm' : T m x ∈ Submodule.span K (Set.range f') := by
        rw [hspan]
        exact ⟨x,rfl⟩
      exact hle hm'
    let N : Normalized K S D :=
      ⟨U,hU,hUr,center,by intro s; simp [U,hcenter],m,v0,v1,hU0,hU1,hU2⟩
    exact ofPost E T center (N.classification hS)
  · have hr : ∀ s, finrank K (LinearMap.range (T s)) ≤ 1 := by
      intro s
      have h := hrank s
      have hs : finrank K (LinearMap.range (T s)) ≠ 2 := fun e => hm ⟨s,e⟩
      omega
    exact Or.inr (Or.inr (rankOneLine T hT center hcenter hr hS))

end PEqualNP.Outside.L_gct_309.PivotCore

/- Post-compression finite-dimensional arguments for L-gct-309.
The row and column forms are bilinear, not Hermitian. -/
namespace PEqualNP.Outside.L_gct_309.Form
open scoped BigOperators
open LinearMap Module

abbrev Pairing (E : Type*) [AddCommGroup E] [Module ℂ E] :=
  E →ₗ[ℂ] E →ₗ[ℂ] ℂ

def Symmetric {E : Type*} [AddCommGroup E] [Module ℂ E] (B : Pairing E) : Prop :=
  ∀ x y, B x y = B y x

def Regular {E : Type*} [AddCommGroup E] [Module ℂ E] (B : Pairing E) : Prop :=
  ∀ x, (∀ y, B x y = 0) → x = 0

section General
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

theorem polar_zero (B : Pairing E) (symm : Symmetric B)
    (W : Submodule ℂ E) (hq : ∀ x ∈ W, B x x = 0)
    (x y : E) (hx : x ∈ W) (hy : y ∈ W) : B x y = 0 := by
  have h := hq (x+y) (W.add_mem hx hy)
  simp only [map_add,LinearMap.add_apply,hq x hx,hq y hy,symm y x,zero_add,add_zero] at h
  have e : (2 : ℂ)*B x y = 0 := by simpa only [two_mul] using h
  exact (mul_eq_zero.mp e).resolve_left two_ne_zero

theorem isotropic_bound (B : Pairing E) (symm : Symmetric B)
    (W : Submodule ℂ E) (hq : ∀ x ∈ W, B x x = 0) :
    2 * finrank ℂ W ≤ finrank ℂ E + finrank ℂ B.ker := by
  let f := B.comp W.subtype
  have into : f.range ≤ W.dualAnnihilator := by
    rintro _ ⟨x,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro y hy
    exact polar_zero B symm W hq x.val y x.prop hy
  have ann := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have rel := Submodule.finrank_mono into
  have dim := f.finrank_range_add_finrank_ker
  have eq : f.ker.map W.subtype = W ⊓ B.ker := by
    dsimp only [f]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have le := Submodule.finrank_mono (inf_le_right : W ⊓ B.ker ≤ B.ker)
  rw [←eq,Submodule.finrank_map_subtype_eq] at le
  calc
    2 * finrank ℂ W = finrank ℂ W + finrank ℂ W := by rw [two_mul]
    _ = finrank ℂ W + (finrank ℂ f.range + finrank ℂ f.ker) :=
      congrArg (fun d : Nat => finrank ℂ W + d) dim.symm
    _ ≤ finrank ℂ W + (finrank ℂ W.dualAnnihilator + finrank ℂ B.ker) :=
      Nat.add_le_add_left (Nat.add_le_add rel le) _
    _ = finrank ℂ E + finrank ℂ B.ker :=
      (Nat.add_assoc _ _ _).symm.trans (congrArg (fun d : Nat => d + finrank ℂ B.ker) ann)

theorem regular_ker (B : Pairing E) (nd : Regular B) : B.ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply nd
  intro y
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y

theorem isotropic_bound_nd (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (W : Submodule ℂ E)
    (hq : ∀ x ∈ W, B x x = 0) : 2 * finrank ℂ W ≤ finrank ℂ E := by
  have q := isotropic_bound B symm W hq
  rwa [regular_ker B nd,finrank_bot,add_zero] at q

noncomputable def diag (B : Pairing E) (a b : ℂ) :
    Pairing (E × E) :=
  a • B.compl₁₂ (LinearMap.fst ℂ E E) (LinearMap.fst ℂ E E) +
    b • B.compl₁₂ (LinearMap.snd ℂ E E) (LinearMap.snd ℂ E E)

theorem diag_apply (B : Pairing E) (a b : ℂ) (x y : E × E) :
    diag B a b x y = a * B x.1 y.1 + b * B x.2 y.2 := rfl

theorem diag_symm (B : Pairing E) (hs : Symmetric B) (a b : ℂ) :
    Symmetric (diag B a b) := by
  intro x y
  rw [diag_apply,diag_apply,hs x.1 y.1,hs x.2 y.2]

theorem fst_zero_of_ker (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (ha : a ≠ 0) (z : E × E) (hz : z ∈ (diag B a b).ker) : z.1 = 0 := by
  change diag B a b z = 0 at hz
  apply nd
  intro y
  have h := LinearMap.congr_fun hz (y,0)
  rw [diag_apply] at h
  simpa [ha] using h

theorem snd_zero_of_ker (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (hb : b ≠ 0) (z : E × E) (hz : z ∈ (diag B a b).ker) : z.2 = 0 := by
  change diag B a b z = 0 at hz
  apply nd
  intro y
  have h := LinearMap.congr_fun hz (0,y)
  rw [diag_apply] at h
  simpa [hb] using h

theorem diag_ker_bound (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (ha : a ≠ 0) :
    finrank ℂ (diag B a b).ker ≤ finrank ℂ E := by
  let K := (diag B a b).ker
  let pr : K →ₗ[ℂ] E := (LinearMap.snd ℂ E E).comp K.subtype
  have inj : Function.Injective pr := by
    intro u v e
    apply Subtype.ext
    apply Prod.ext
    · exact (fst_zero_of_ker B nd a b ha u.val u.prop).trans
        (fst_zero_of_ker B nd a b ha v.val v.prop).symm
    · exact e
  exact LinearMap.finrank_le_finrank_of_injective inj

theorem diag_isotropic_bound (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (a b : ℂ) (ha : a ≠ 0)
    (L : Submodule ℂ (E × E))
    (hq : ∀ z ∈ L, a * B z.1 z.1 + b * B z.2 z.2 = 0) :
    2 * finrank ℂ L ≤ 3 * finrank ℂ E := by
  have h := isotropic_bound (diag B a b) (diag_symm B symm a b) L (by
    intro z hz
    rw [diag_apply]
    exact hq z hz)
  have r := diag_ker_bound B nd a b ha
  rw [Module.finrank_prod] at h
  omega

theorem diag_isotropic_bound_regular (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Submodule ℂ (E × E))
    (hq : ∀ z ∈ L, a * B z.1 z.1 + b * B z.2 z.2 = 0) :
    finrank ℂ L ≤ finrank ℂ E := by
  have ker : (diag B a b).ker = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    exact Prod.ext (fst_zero_of_ker B nd a b ha z hz) (snd_zero_of_ker B nd a b hb z hz)
  have h := isotropic_bound (diag B a b) (diag_symm B symm a b) L (by
    intro z hz
    rw [diag_apply]
    exact hq z hz)
  rw [ker,finrank_bot,add_zero,Module.finrank_prod] at h
  omega
end General

noncomputable def dots (n : Nat) : Pairing (Fin n → ℂ) :=
  dotProductBilin ℂ ℂ

theorem dots_eval (n : Nat) (x y : Fin n → ℂ) :
    dots n x y = ∑ i, x i * y i := rfl

theorem dots_symm (n : Nat) : Symmetric (dots n) := by
  intro x y
  change dotProduct x y = dotProduct y x
  exact dotProduct_comm x y

theorem dots_regular (n : Nat) : Regular (dots n) := by
  intro x h
  funext i
  have z := h (Pi.single i (1 : ℂ))
  change dotProduct x (Pi.single i 1) = 0 at z
  rwa [dotProduct_single_one] at z

def ones (n : Nat) : Fin n → ℂ := fun _ => 1

noncomputable def sumLin (n : Nat) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i : Fin n, LinearMap.proj i

theorem sumLin_eval (n : Nat) (x : Fin n → ℂ) : sumLin n x = ∑ i, x i := by
  simp [sumLin]

noncomputable def centered (n : Nat) : Submodule ℂ (Fin n → ℂ) := (sumLin n).ker

theorem centered_mem (n : Nat) (x : Fin n → ℂ) :
    x ∈ centered n ↔ ∑ i, x i = 0 := by
  rw [centered,LinearMap.mem_ker,sumLin_eval]

theorem sum_ones (n : Nat) : sumLin n (ones n) = (n : ℂ) := by
  simp [sumLin_eval,ones]

theorem centered_rank (n : Nat) (h : 0 < n) : finrank ℂ (centered n) = n - 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)
  have onto : Function.Surjective (sumLin n) := by
    intro x
    refine ⟨(x/(n : ℂ)) • ones n,?_⟩
    rw [map_smul,sum_ones,smul_eq_mul]
    exact div_mul_cancel₀ x hn
  have d := (sumLin n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,finrank_self,Module.finrank_pi,Fintype.card_fin] at d
  change 1 + finrank ℂ (centered n) = n at d
  omega

noncomputable def centerDot (n : Nat) : Pairing (centered n) :=
  (dots n).compl₁₂ (centered n).subtype (centered n).subtype

theorem centerDot_symm (n : Nat) : Symmetric (centerDot n) :=
  fun x y => dots_symm n x.val y.val

theorem centerDot_regular (n : Nat) (h : 0 < n) : Regular (centerDot n) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)
  intro x orth
  apply Subtype.ext
  apply dots_regular n
  intro y
  let a := sumLin n y/(n : ℂ)
  let y' := y-a • ones n
  have ok : y' ∈ centered n := by
    change sumLin n (y-a • ones n) = 0
    rw [map_sub,map_smul,sum_ones,smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (sumLin n y) hn).symm
  have base : dots n x.val y' = 0 := orth ⟨y',ok⟩
  have ref : dots n x.val (ones n) = 0 := by
    simpa [dots_eval,ones] using (centered_mem n x.val).mp x.prop
  have e : y = y' + a • ones n := (sub_add_cancel y (a • ones n)).symm
  calc
    dots n x.val y = dots n x.val (y' + a • ones n) := congrArg (dots n x.val) e
    _ = 0 := by rw [map_add,map_smul,base,ref,smul_zero,zero_add]

end PEqualNP.Outside.L_gct_309.Form

namespace PEqualNP.Outside.L_gct_309.Form
open LinearMap Module

abbrev Mat (m n : Nat) := Matrix (Fin m) (Fin n) ℂ
abbrev Vec (n : Nat) := Fin n → ℂ

noncomputable def outer (a : Vec m) (x : Vec n) : Mat m n :=
  Matrix.vecMulVec a x

noncomputable def alongColumn (a : Vec m) : Vec n →ₗ[ℂ] Mat m n :=
  (vecMulVecBilin ℂ ℂ : Vec m →ₗ[ℂ] Vec n →ₗ[ℂ] Mat m n) a

noncomputable def alongRow (b : Vec n) : Vec m →ₗ[ℂ] Mat m n :=
  (vecMulVecBilin ℂ ℂ : Vec m →ₗ[ℂ] Vec n →ₗ[ℂ] Mat m n).flip b

theorem alongColumn_eval (a : Vec m) (x : Vec n) : alongColumn a x = outer a x := rfl
theorem alongRow_eval (b : Vec n) (y : Vec m) : alongRow b y = outer y b := rfl
theorem outer_apply (a : Vec m) (x : Vec n) (i : Fin m) (j : Fin n) :
    outer a x i j = a i * x j := rfl

theorem column_injective (a : Vec m) (ha : a ≠ 0) :
    Function.Injective (alongColumn (n := n) a) := by
  classical
  have useful : ∃ i, a i ≠ 0 := by
    by_contra z
    apply ha
    funext i
    exact Classical.byContradiction (fun fi => z ⟨i,fi⟩)
  obtain ⟨i,hi⟩ := useful
  intro x y h
  funext j
  have e := congrArg (fun A : Mat m n => A i j) h
  change a i * x j = a i * y j at e
  exact mul_left_cancel₀ hi e

noncomputable def fiber (L : Submodule ℂ (Mat m n)) (a : Vec m) :
    Submodule ℂ (Vec n) := L.comap (alongColumn a)

theorem fiber_exact (L : Submodule ℂ (Mat m n)) (a : Vec m) :
    (fiber L a).map (alongColumn a) = L ⊓ (alongColumn a).range := by
  ext A
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,⟨x,rfl⟩⟩
  · rintro ⟨hh,⟨x,he⟩⟩
    exact ⟨x,by change alongColumn a x ∈ L; rw [he]; exact hh,he⟩

theorem fiber_dimension (L : Submodule ℂ (Mat m n)) (a : Vec m) (ha : a ≠ 0) :
    finrank ℂ (fiber L a) = finrank ℂ (L ⊓ (alongColumn a).range : Submodule ℂ (Mat m n)) := by
  rw [← fiber_exact L a]
  exact (Submodule.equivMapOfInjective _ (column_injective a ha) _).finrank_eq

/-- Abstract dimension consequence of a rank-(1,1) compression. -/
theorem dim_compressed {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (L C R : Submodule ℂ E) (ls : L ≤ C ⊔ R)
    (r : finrank ℂ R ≤ 3) (h : 1 ≤ finrank ℂ (C ⊓ R : Submodule ℂ E)) :
    finrank ℂ L ≤ finrank ℂ (L ⊓ C : Submodule ℂ E) + 2 := by
  have t : L ⊔ C ≤ C ⊔ R := sup_le ls le_sup_left
  have f := Submodule.finrank_mono t
  have s := Submodule.finrank_sup_add_finrank_inf_eq L C
  have q := Submodule.finrank_sup_add_finrank_inf_eq C R
  omega

theorem mixed_first {n : Nat} (n5 : 5 ≤ n) (L : Submodule ℂ (Mat 4 n))
    (a : centered 4) (ha : (a : Vec 4) ≠ 0) (b : Vec n)
    (contains : ∀ X ∈ L, ∃ x : Vec n, ∃ y : centered 4,
      X = outer a.val x + outer y.val b) :
    ∃ (u : Vec 4) (K : Submodule ℂ (Vec n)), u ≠ 0 ∧
      2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
      ∀ x ∈ K, (fun i j => u i * x j) ∈ L := by
  let C : Submodule ℂ (Mat 4 n) := (alongColumn a.val).range
  let R : Submodule ℂ (Mat 4 n) := ((alongRow b).comp (centered 4).subtype).range
  let K := fiber L a.val
  have clear : finrank ℂ K = finrank ℂ (L ⊓ C : Submodule ℂ (Mat 4 n)) :=
    fiber_dimension L a.val ha
  refine ⟨a.val,K,ha,?_,?_⟩
  · by_cases bz : b = 0
    · have good : L ≤ C := by
        intro X hx
        obtain ⟨x,y,h⟩ := contains X hx
        refine ⟨x,?_⟩
        rw [alongColumn_eval,h,bz]
        simp [outer]
      have e : L ⊓ C = L := inf_eq_left.mpr good
      rw [e] at clear
      omega
    · have range_dim : finrank ℂ R ≤ 3 := by
        let f : centered 4 →ₗ[ℂ] Mat 4 n := (alongRow b).comp (centered 4).subtype
        calc
          finrank ℂ R ≤ finrank ℂ R + finrank ℂ f.ker := Nat.le_add_right _ _
          _ = finrank ℂ (centered 4) :=
            LinearMap.finrank_range_add_finrank_ker (K := ℂ)
              (V := ↥(centered 4)) (V₂ := Mat 4 n) f
          _ = 3 := centered_rank 4 (by decide)
      have cap : L ≤ C ⊔ R := by
        intro X hx
        obtain ⟨x,y,h⟩ := contains X hx
        rw [h]
        exact Submodule.add_mem_sup (show outer a.val x ∈ C from ⟨x,rfl⟩)
          (show outer y.val b ∈ R from ⟨y,rfl⟩)
      have joint : outer a.val b ∈ C ⊓ R := ⟨⟨b,rfl⟩,⟨a,rfl⟩⟩
      have nz : outer a.val b ≠ 0 := by
        intro eq
        apply bz
        apply column_injective a.val ha
        change outer a.val b = alongColumn a.val 0
        rw [map_zero,eq]
      have line : ℂ ∙ outer a.val b ≤ C ⊓ R :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr joint
      have bound := Submodule.finrank_mono line
      rw [finrank_span_singleton nz] at bound
      have d := dim_compressed L C R cap range_dim bound
      omega
  · intro x hx
    exact hx

end PEqualNP.Outside.L_gct_309.Form

namespace PEqualNP.Outside.L_gct_309.Form
open LinearMap Module
open scoped BigOperators

noncomputable def qMat (X : Mat m n) : ℂ := ∑ i, ∑ j, (X i j)^2

theorem q_two_columns (a b : Vec m) (x y : Vec n) (ort : dots m a b = 0) :
    qMat (outer a x + outer b y) =
      dots m a a * dots n x x + dots m b b * dots n y y := by
  calc
    _ = ∑ i, ((a i*a i)*dots n x x + (b i*b i)*dots n y y +
        (a i*b i)*(2*dots n x y)) := by
      unfold qMat
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ j, ((a i*a i)*(x j*x j) + (b i*b i)*(y j*y j) +
            (a i*b i)*(2*(x j*y j))) := by
          apply Finset.sum_congr rfl
          intro j _
          change (a i*x j + b i*y j)^2 = _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib,dots_eval,← Finset.mul_sum]
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← dots_eval,ort,zero_mul,add_zero]

theorem q_transpose (X : Mat m n) : qMat X.transpose = qMat X := by
  unfold qMat
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

theorem q_two_rows (a b : Vec n) (x y : Vec m) (ort : dots n a b = 0) :
    qMat (outer x a + outer y b) = dots n a a * dots m x x + dots n b b * dots m y y := by
  have flip : (outer x a + outer y b).transpose = outer a x + outer b y := by
    ext i j
    change x j*a i + y j*b i = a i*x j + b i*y j
    rw [mul_comm (x j),mul_comm (y j)]
  rw [← q_transpose (outer x a + outer y b),flip]
  exact q_two_columns a b x y ort

noncomputable def cols (a b : Vec m) : centered n × centered n →ₗ[ℂ] Mat m n :=
  ((alongColumn a).comp (centered n).subtype).comp (LinearMap.fst ℂ _ _) +
    ((alongColumn b).comp (centered n).subtype).comp (LinearMap.snd ℂ _ _)

noncomputable def rows (a b : Vec n) : centered m × centered m →ₗ[ℂ] Mat m n :=
  ((alongRow a).comp (centered m).subtype).comp (LinearMap.fst ℂ _ _) +
    ((alongRow b).comp (centered m).subtype).comp (LinearMap.snd ℂ _ _)

theorem cols_eval (a b : Vec m) (x y : centered n) :
    cols a b (x,y) = outer a x.val + outer b y.val := rfl

theorem rows_eval (a b : Vec n) (x y : centered m) :
    rows a b (x,y) = outer x.val a + outer y.val b := rfl

theorem comap_bound {E V : Type*} [AddCommGroup E] [AddCommGroup V]
    [Module ℂ E] [Module ℂ V] [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] V) (L : Submodule ℂ V)
    (onto : ∀ x ∈ L, ∃ z, f z = x) :
    finrank ℂ L ≤ finrank ℂ (L.comap f) := by
  have e : (L.comap f).map f = L := by
    ext x; constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hx
      obtain ⟨z,hz⟩ := onto x hx
      exact ⟨z,by change f z ∈ L; rw [hz]; exact hx,hz⟩
  have d := Submodule.finrank_map_le f (L.comap f)
  rwa [e] at d

theorem q_cols_comap (L : Submodule ℂ (Mat m n)) (a b : Vec m)
    (ort : dots m a b = 0) (hq : ∀ X ∈ L, qMat X = 0) :
    ∀ z ∈ L.comap (cols a b), dots m a a * centerDot n z.1 z.1 +
      dots m b b * centerDot n z.2 z.2 = 0 := by
  rintro ⟨x,y⟩ hz
  have h := hq _ (show cols a b (x,y) ∈ L from hz)
  rw [cols_eval,q_two_columns a b _ _ ort] at h
  exact h

theorem q_rows_comap (L : Submodule ℂ (Mat m n)) (a b : Vec n)
    (ort : dots n a b = 0) (hq : ∀ X ∈ L, qMat X = 0) :
    ∀ z ∈ L.comap (rows a b), dots n a a * centerDot m z.1 z.1 +
      dots n b b * centerDot m z.2 z.2 = 0 := by
  rintro ⟨x,y⟩ hz
  have h := hq _ (show rows a b (x,y) ∈ L from hz)
  rw [rows_eval,q_two_rows a b _ _ ort] at h
  exact h

theorem regular_columns_impossible {n : Nat} (n0 : 0 < n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L) (a b : Vec 4)
    (ort : dots 4 a b = 0) (ap : dots 4 a a ≠ 0) (bp : dots 4 b b ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered n, X = outer a x.val + outer b y.val)
    (hq : ∀ X ∈ L, qMat X = 0) : False := by
  have big := comap_bound (cols a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have d := diag_isotropic_bound_regular (centerDot n) (centerDot_symm n)
    (centerDot_regular n n0) _ _ ap bp _ (q_cols_comap L a b ort hq)
  rw [centered_rank n n0] at d
  omega

theorem nonisotropic_rows_impossible {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L) (a b : Vec n)
    (ort : dots n a b = 0) (ap : dots n a a ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered 4, X = outer x.val a + outer y.val b)
    (hq : ∀ X ∈ L, qMat X = 0) : False := by
  have big := comap_bound (rows a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have d := diag_isotropic_bound (centerDot 4) (centerDot_symm 4)
    (centerDot_regular 4 (by decide)) _ _ ap _ (q_rows_comap L a b ort hq)
  rw [centered_rank 4 (by decide)] at d
  omega

theorem radical_columns_first {n : Nat} (n0 : 0 < n)
    (L : Submodule ℂ (Mat 4 n)) (a b : Vec 4) (anz : a ≠ 0)
    (ort : dots 4 a b = 0) (null : dots 4 a a = 0) (bp : dots 4 b b ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered n, X = outer a x.val + outer b y.val)
    (hq : ∀ X ∈ L, qMat X = 0) :
    ∃ (u : Vec 4) (K : Submodule ℂ (Vec n)), u ≠ 0 ∧
      2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
      ∀ x ∈ K, (fun i j => u i * x j) ∈ L := by
  let S := L.comap (cols a b)
  let f : S →ₗ[ℂ] centered n := (LinearMap.snd ℂ _ _).comp S.subtype
  let K := fiber L a
  have big : finrank ℂ L ≤ finrank ℂ S := comap_bound (cols a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have fit : ∀ z ∈ f.range, centerDot n z z = 0 := by
    rintro y ⟨z,rfl⟩
    have h := q_cols_comap L a b ort hq z.val z.prop
    rw [null,zero_mul,zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left bp
  have d := isotropic_bound_nd (centerDot n) (centerDot_symm n)
    (centerDot_regular n n0) f.range fit
  rw [centered_rank n n0] at d
  have ker_second (z : f.ker) : z.val.val.2 = 0 := LinearMap.mem_ker.mp z.prop
  let first : f.ker →ₗ[ℂ] Vec n :=
    (centered n).subtype.comp ((LinearMap.fst ℂ _ _).comp (S.subtype.comp f.ker.subtype))
  have hfirst (z : f.ker) : first z ∈ K := by
    have hs : cols a b z.val.val ∈ L := z.val.prop
    have eq : z.val.val = (z.val.val.1,0) := Prod.ext rfl (ker_second z)
    rw [eq,cols_eval] at hs
    change outer a z.val.val.1.val ∈ L
    have hs' : outer a z.val.val.1.val + outer b (0 : Vec n) ∈ L := hs
    simpa [outer] using hs'
  let g : f.ker →ₗ[ℂ] K := first.codRestrict K hfirst
  have gi : Function.Injective g := by
    intro z t ge
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have e := congrArg (fun x : K => x.val) ge
      change z.val.val.1.val = t.val.val.1.val at e
      exact e
    · rw [ker_second z,ker_second t]
  have kcap := LinearMap.finrank_le_finrank_of_injective gi
  have rn := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (V := ↥S) (V₂ := ↥(centered n)) f
  refine ⟨a,K,anz,by omega,?_⟩
  intro x hx
  exact hx

end PEqualNP.Outside.L_gct_309.Form

namespace PEqualNP.Outside.L_gct_309.Form
open scoped BigOperators
open LinearMap Module

/-- A subspace of dimension at most two containing a nonisotropic
direction is generated by it and a single orthogonal direction. -/
theorem orthogonal_span_two {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (B : Pairing E) (A : Submodule ℂ E)
    (sm : finrank ℂ A ≤ 2) (b : E) (hb : b ∈ A) (nb : B b b ≠ 0) :
    ∃ a ∈ A, B b a = 0 ∧
      ∀ x ∈ A, ∃ c d : ℂ, x = c • a + d • b := by
  let b' : A := ⟨b,hb⟩
  let f : A →ₗ[ℂ] ℂ := (B b).domRestrict A
  let D := f.ker
  have t : f b' = B b b := rfl
  have surj : Function.Surjective f := by
    intro y
    refine ⟨(y / B b b) • b',?_⟩
    rw [map_smul,t,smul_eq_mul]
    exact div_mul_cancel₀ y nb
  have dim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,finrank_self] at dim
  have small : finrank ℂ D ≤ 1 := by change finrank ℂ f.ker ≤ 1; omega
  obtain ⟨a',aSpan⟩ := finrank_le_one_iff.mp small
  let a : E := a'.val.val
  have porth : B b a = 0 := LinearMap.mem_ker.mp a'.prop
  refine ⟨a,a'.val.prop,porth,?_⟩
  intro x hx
  let x' : A := ⟨x,hx⟩
  let d := f x' / B b b
  have kh : x' - d • b' ∈ D := by
    change f (x' - d • b') = 0
    rw [map_sub,map_smul,t,smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (f x') nb).symm
  obtain ⟨c,cv⟩ := aSpan ⟨x' - d • b',kh⟩
  have cve : c • a'.val = x' - d • b' := congrArg Subtype.val cv
  refine ⟨c,d,?_⟩
  have xy : c • a'.val + d • b' = x' := by rw [cve,sub_add_cancel]
  exact (congrArg Subtype.val xy).symm

end PEqualNP.Outside.L_gct_309.Form

namespace PEqualNP.Outside.L_gct_309.Form
open scoped BigOperators
open LinearMap Module

def First {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ (a : Vec 4) (K : Submodule ℂ (Vec n)), a ≠ 0 ∧
    2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
    (∀ x ∈ K, (fun i j => a i * x j) ∈ L)

def Second {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ U : Submodule ℂ (Vec n), finrank ℂ U = 2 ∧
    (∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^2) = 0) ∧
    (∀ X ∈ L, ∀ i, X i ∈ U)

def ColCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ a b : centered 4, LinearIndependent ℂ ![a,b] ∧
    ∀ X ∈ L, ∃ x y : centered n, X = outer a.val x.val + outer b.val y.val

def RowCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ a b : centered n, LinearIndependent ℂ ![a,b] ∧
    ∀ X ∈ L, ∃ x y : centered 4, X = outer x.val a.val + outer y.val b.val

def MixedCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ (a : centered 4) (b : centered n), a.val ≠ 0 ∧
    ∀ X ∈ L, ∃ x : centered n, ∃ y : centered 4, X = outer a.val x.val + outer y.val b.val

theorem spanTwo_finrank {E : Type*} [AddCommGroup E] [Module ℂ E] {a b : E}
    (lin : LinearIndependent ℂ ![a,b]) :
    finrank ℂ (Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E))) = 2 := by
  rw [finrank_span_eq_card lin,Fintype.card_fin]

theorem spanTwo_left {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    a ∈ Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E)) :=
  Submodule.subset_span ⟨0,rfl⟩

theorem spanTwo_right {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    b ∈ Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E)) :=
  Submodule.subset_span ⟨1,rfl⟩

theorem change_columns {m n : Nat} (a b p q : centered m)
    (c d e f : ℂ) (ha : a = c • p + d • q) (hb : b = e • p + f • q)
    (x y : centered n) :
    outer a.val x.val + outer b.val y.val =
      outer p.val (c • x + e • y : centered n).val +
      outer q.val (d • x + f • y : centered n).val := by
  apply Matrix.ext
  intro i j
  have ai := congrArg (fun z : centered m => z.val i) ha
  have bi := congrArg (fun z : centered m => z.val i) hb
  change a.val i = c*p.val i + d*q.val i at ai
  change b.val i = e*p.val i + f*q.val i at bi
  change a.val i*x.val j + b.val i*y.val j =
    p.val i*(c*x.val j + e*y.val j) + q.val i*(d*x.val j + f*y.val j)
  rw [ai,bi]
  ring

theorem change_rows {m n : Nat} (a b p q : centered n)
    (c d e f : ℂ) (ha : a = c • p + d • q) (hb : b = e • p + f • q)
    (x y : centered m) :
    outer x.val a.val + outer y.val b.val =
      outer (c • x + e • y : centered m).val p.val +
      outer (d • x + f • y : centered m).val q.val := by
  apply Matrix.ext
  intro i j
  have aj := congrArg (fun z : centered n => z.val j) ha
  have bj := congrArg (fun z : centered n => z.val j) hb
  change a.val j = c*p.val j + d*q.val j at aj
  change b.val j = e*p.val j + f*q.val j at bj
  change x.val i*a.val j + y.val i*b.val j =
    (c*x.val i + e*y.val i)*p.val j + (d*x.val i + f*y.val i)*q.val j
  rw [aj,bj]
  ring

theorem generators_independent_direction {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (A : Submodule ℂ E) (dim : finrank ℂ A = 2)
    (p q : E) (qq : q ≠ 0) (sp : ∀ x ∈ A, ∃ c d : ℂ, x = c • p + d • q) :
    p ≠ 0 := by
  intro p0
  have small : A ≤ ℂ ∙ q := by
    intro x hx
    obtain ⟨_c,d,ex⟩ := sp x hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨d,by simpa [p0] using ex.symm⟩
  have nu := Submodule.finrank_mono small
  rw [dim,finrank_span_singleton qq] at nu
  omega

theorem column_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, qMat X = 0) (covered : ColCompression L) :
    First L := by
  obtain ⟨a,b,li,coords⟩ := covered
  let A := Submodule.span ℂ (Set.range (![a,b] : Fin 2 → centered 4))
  have dim : finrank ℂ A = 2 := spanTwo_finrank li
  have qExists : ∃ q ∈ A, centerDot 4 q q ≠ 0 := by
    classical
    by_contra no
    have zero : ∀ q ∈ A, centerDot 4 q q = 0 := by
      intro q hn
      exact Classical.byContradiction (fun hz => no ⟨q,hn,hz⟩)
    have cap := isotropic_bound_nd (centerDot 4) (centerDot_symm 4)
      (centerDot_regular 4 (by decide)) A zero
    rw [dim,centered_rank 4 (by decide)] at cap
    omega
  obtain ⟨q,qA,qN⟩ := qExists
  obtain ⟨p,_,ort,sp⟩ := orthogonal_span_two (centerDot 4) A (by omega) q qA qN
  obtain ⟨c,d,ha⟩ := sp a (spanTwo_left a b)
  obtain ⟨e,f,hb⟩ := sp b (spanTwo_right a b)
  have qnz : q ≠ 0 := by intro bz; apply qN; simp [bz]
  have pnz := generators_independent_direction A dim p q qnz sp
  have pv : p.val ≠ 0 := fun z => pnz (Subtype.ext z)
  have ort' : dots 4 p.val q.val = 0 := (dots_symm 4 p.val q.val).trans ort
  have newCoords (X : Mat 4 n) (inL : X ∈ L) :
      ∃ x y : centered n, X = outer p.val x.val + outer q.val y.val := by
    obtain ⟨x,y,h⟩ := coords X inL
    exact ⟨c • x + e • y,d • x + f • y,h.trans (change_columns a b p q c d e f ha hb x y)⟩
  by_cases hz : dots 4 p.val p.val = 0
  · exact radical_columns_first (by omega) L p.val q.val pv ort' hz qN newCoords hq
  · exact False.elim (regular_columns_impossible (by omega) L large p.val q.val ort' hz qN newCoords hq)

theorem row_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, qMat X = 0) (covered : RowCompression L) :
    Second L := by
  classical
  obtain ⟨a,b,li,coords⟩ := covered
  let A := Submodule.span ℂ (Set.range (![a,b] : Fin 2 → centered n))
  have dim : finrank ℂ A = 2 := spanTwo_finrank li
  let U := A.map (centered n).subtype
  by_cases qExists : ∃ q ∈ A, centerDot n q q ≠ 0
  · obtain ⟨q,qA,qN⟩ := qExists
    obtain ⟨p,_,ort,sp⟩ := orthogonal_span_two (centerDot n) A (by omega) q qA qN
    obtain ⟨c,d,ha⟩ := sp a (spanTwo_left a b)
    obtain ⟨e,f,hb⟩ := sp b (spanTwo_right a b)
    have newCoords (X : Mat 4 n) (inL : X ∈ L) :
        ∃ x y : centered 4, X = outer x.val q.val + outer y.val p.val := by
      obtain ⟨x,y,h⟩ := coords X inL
      refine ⟨d • x + f • y,c • x + e • y,?_⟩
      exact h.trans ((change_rows a b p q c d e f ha hb x y).trans (add_comm _ _))
    exact False.elim (nonisotropic_rows_impossible n5 L large q.val p.val ort qN newCoords hq)
  · have zero : ∀ q ∈ A, centerDot n q q = 0 := by
      intro q hn
      exact Classical.byContradiction (fun hz => qExists ⟨q,hn,hz⟩)
    have size : finrank ℂ U = 2 := by
      simpa only [U,Submodule.finrank_map_subtype_eq] using dim
    refine ⟨U,size,?_,?_⟩
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨(centered_mem n x.val).mp x.prop,?_⟩
      have d := zero x hx
      change dots n x.val x.val = 0 at d
      change (∑ j, (x.val j)^2) = 0
      simpa only [dots_eval,pow_two] using d
    · intro X inL i
      obtain ⟨x,y,showX⟩ := coords X inL
      let z : centered n := x.val i • a + y.val i • b
      have zA : z ∈ A := A.add_mem (A.smul_mem _ (spanTwo_left a b)) (A.smul_mem _ (spanTwo_right a b))
      refine ⟨z,zA,?_⟩
      funext j
      rw [showX]
      rfl

theorem mixed_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (covered : MixedCompression L) : First L := by
  obtain ⟨a,b,az,coords⟩ := covered
  apply mixed_first n5 L a az b.val
  intro X inL
  obtain ⟨x,y,h⟩ := coords X inL
  exact ⟨x.val,y,h⟩

theorem postcompression {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, (∑ i, ∑ j, (X i j)^2) = 0)
    (shape : ColCompression L ∨ RowCompression L ∨ MixedCompression L) :
    First L ∨ Second L := by
  rcases shape with cols|rows|mixed
  · exact Or.inl (column_finish n5 L large hq cols)
  · exact Or.inr (row_finish n5 L large hq rows)
  · exact Or.inl (mixed_finish n5 L mixed)

end PEqualNP.Outside.L_gct_309.Form

open Module
open scoped BigOperators

namespace PEqualNP.Outside.L_gct_309.Bridge
open PEqualNP.Outside.L_gct_309.PivotCore
open PEqualNP.Outside.L_gct_309.Form


abbrev Domain (n : Nat) := Fin n → ℂ

noncomputable def act {n : Nat} (L : Submodule ℂ (Mat 4 n))
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) :
    L →ₗ[ℂ] Domain n →ₗ[ℂ] centered 4 where
  toFun X := LinearMap.codRestrict (centered 4) X.val.mulVecLin (by
    intro v
    rw [centered_mem]
    simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hcols X.val X.prop,zero_mul]
    simp)
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (X.val+Y.val).mulVecLin v = X.val.mulVecLin v+Y.val.mulVecLin v
    rw [Matrix.mulVecLin_add,LinearMap.add_apply]
  map_smul' r X := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (r • X.val).mulVecLin v = r • X.val.mulVecLin v
    exact Matrix.smul_mulVec r X.val v

theorem act_coe {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    {hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0} (X : L) (v : Domain n) :
    (act L hcols X v).val = X.val.mulVecLin v := rfl

theorem act_single {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    {hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0} (X : L) (i : Fin 4) (j : Fin n) :
    (act L hcols X (Pi.single j 1)).val i = X.val i j := by
  rw [act_coe,Matrix.mulVecLin_apply,Matrix.mulVec_single_one]
  rfl

theorem act_inj {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) : Function.Injective (act L hcols) := by
  intro X Y h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  simpa only [act_single] using
    congrArg (fun F : Domain n →ₗ[ℂ] centered 4 => (F (Pi.single j 1)).val i) h

theorem act_center {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hrows : ∀ X ∈ L, ∀ i, (∑ j, X i j) = 0)
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) (X : L) :
    act L hcols X (ones n) = 0 := by
  apply Subtype.ext
  funext i
  simp [act_coe,ones,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,hrows X.val X.prop i]

theorem act_rank {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) (X : L) :
    Module.finrank ℂ (LinearMap.range (act L hcols X)) = X.val.rank := by
  change _ = finrank ℂ (LinearMap.range X.val.mulVecLin)
  have h : (centered 4).subtype.comp (act L hcols X) = X.val.mulVecLin := rfl
  rw [← h,LinearMap.range_comp,Submodule.finrank_map_subtype_eq]

noncomputable def asProfile {n : Nat} (f : Domain n →ₗ[ℂ] ℂ) (hf : f (ones n) = 0) : centered n := by
  let e := dotProductEquiv ℂ (Fin n)
  refine ⟨e.symm f,?_⟩
  rw [centered_mem]
  have h : e (e.symm f) (ones n) = 0 := by rw [e.apply_symm_apply,hf]
  change dotProduct (e.symm f) (ones n) = 0 at h
  simpa [dotProduct,ones] using h

theorem asProfile_single {n : Nat} (f : Domain n →ₗ[ℂ] ℂ) (hf : f (ones n) = 0)
    (j : Fin n) :
    (asProfile f hf).val j = f (Pi.single j 1) := by
  have h := LinearEquiv.apply_symm_apply (dotProductEquiv ℂ (Fin n)) f
  have hx := LinearMap.congr_fun h (Pi.single j 1)
  change dotProduct (asProfile f hf).val (Pi.single j 1) = _ at hx
  rwa [dotProduct_single_one] at hx

theorem independentProfiles {n : Nat} {f g : Domain n →ₗ[ℂ] ℂ}
    (hf : f (ones n) = 0) (hg : g (ones n) = 0)
    (h : LinearIndependent ℂ ![f,g]) :
    LinearIndependent ℂ ![asProfile f hf,asProfile g hg] := by
  let e := (dotProductEquiv ℂ (Fin n)).symm
  have h' := h.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  apply LinearIndependent.of_comp (centered n).subtype
  convert h' using 1
  funext i
  fin_cases i <;> rfl

theorem shapes {n : Nat} (L : Submodule ℂ (Mat 4 n))
    (hc : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0)
    (h : ThreeShapes (act L hc) (ones n)) :
    ColCompression L ∨ RowCompression L ∨ MixedCompression L := by
  rcases h with h|h|h
  · obtain ⟨a,b,hab,h⟩ := h
    refine Or.inl ⟨a,b,hab,?_⟩
    intro X hX
    obtain ⟨f,g,hf,hg,h⟩ := h ⟨X,hX⟩
    refine ⟨asProfile f hf,asProfile g hg,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e
  · obtain ⟨f,g,hf,hg,hi,h⟩ := h
    refine Or.inr (Or.inl ⟨asProfile f hf,asProfile g hg,independentProfiles hf hg hi,?_⟩)
    intro X hX
    obtain ⟨a,b,h⟩ := h ⟨X,hX⟩
    refine ⟨a,b,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e
  · obtain ⟨a,b,ha,_,hb,h⟩ := h
    refine Or.inr (Or.inr ⟨a,asProfile b hb,?_,?_⟩)
    · intro hz
      exact ha (Subtype.ext hz)
    intro X hX
    obtain ⟨f,y,hf,h⟩ := h ⟨X,hX⟩
    refine ⟨asProfile f hf,y,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e

theorem bridge {n : Nat} (n5 : 5 ≤ n) (L : Submodule ℂ (Mat 4 n))
    (large : n ≤ finrank ℂ L)
    (hrows : ∀ X ∈ L, ∀ i, (∑ j, X i j) = 0)
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0)
    (hquad : ∀ X ∈ L, (∑ i, ∑ j, (X i j)^2) = 0)
    (hr : ∀ X ∈ L, X.rank ≤ 2) : First L ∨ Second L := by
  apply postcompression n5 L large hquad
  apply shapes L hcols
  apply classifySpace (act L hcols) (act_inj hcols) (ones n) (act_center hrows hcols)
  · intro X
    rw [act_rank hcols X]
    exact hr X.val X.prop
  · simpa using centered_rank 4 (by decide)
  · omega

end PEqualNP.Outside.L_gct_309.Bridge

theorem PEqualNP.Outside.L_gct_309 : ∀ (n : ℕ), 5 ≤ n → ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ),
  n ≤ Module.finrank ℂ L →
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ i, ∑ j, (X i j)^2) = 0 ∧ X.rank ≤ 2) →
  (∃ (a : Fin 4 → ℂ) (K : Submodule ℂ (Fin n → ℂ)), a ≠ 0 ∧
    2 * Module.finrank ℂ L + 1 ≤ 2 * Module.finrank ℂ K + n ∧
    (∀ x ∈ K, (fun i j => a i * x j) ∈ L)) ∨
  (∃ U : Submodule ℂ (Fin n → ℂ), Module.finrank ℂ U = 2 ∧
    (∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^2) = 0) ∧
    (∀ X ∈ L, ∀ i, X i ∈ U)) := by
  intro n n5 L large hypotheses
  exact PEqualNP.Outside.L_gct_309.Bridge.bridge n5 L large
    (fun X hX => (hypotheses X hX).1)
    (fun X hX => (hypotheses X hX).2.1)
    (fun X hX => (hypotheses X hX).2.2.1)
    (fun X hX => (hypotheses X hX).2.2.2)
