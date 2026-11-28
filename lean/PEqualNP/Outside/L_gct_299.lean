import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_299
noncomputable section
open Finset

private lemma injective_vec4_iff {α : Type*} (a b c d : α) :
    Function.Injective ![a, b, c, d] ↔
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 1) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 2) (a₂ := 3) e) (by decide)
  · rintro ⟨hab, hac, had, hbc, hbd, hcd⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private lemma sum_emb_fin4_eq_ind {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ) :
    ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) * F a b c d := by
  let e1 : { f : Fin 4 → α // Function.Injective f } ≃ (Fin 4 ↪ α) :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (Fin 4 → α) ≃ α × α × α × α :=
    { toFun := fun f => (f 0, f 1, f 2, f 3)
      invFun := fun ⟨a, b, c, d⟩ => ![a, b, c, d]
      left_inv := fun f => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  have h1 : ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) := by
    exact (Fintype.sum_equiv e1 _ _ (fun _ => rfl)).symm
  have h2 : ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) =
      ∑ f : Fin 4 → α, if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun f _ => f.1) ?_ ?_ ?_ ?_
    · intro f _; simp [f.2]
    · intro f₁ _ f₂ _ h; exact Subtype.ext h
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact ⟨⟨f, hf⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have h3 : ∑ f : Fin 4 → α, (if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0) =
      ∑ x : α × α × α × α,
        if Function.Injective ![x.1, x.2.1, x.2.2.1, x.2.2.2] then
          F x.1 x.2.1 x.2.2.1 x.2.2.2
        else 0 := by
    exact Fintype.sum_equiv e2 _ _ (fun f => by
      have hf : ![f 0, f 1, f 2, f 3] = f := e2.left_inv f
      simp [e2, hf])
  rw [h1, h2, h3]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [injective_vec4_iff]
  split_ifs <;> simp

variable {q : ℕ}
private abbrev V (q : ℕ) := Fin q → ℂ
private def S (a : V q) := ∑ j, a j
private def S₂ (a b : V q) := ∑ i, a i * ∑ j ∈ univ.erase i, b j
private def S₃ (a b c : V q) :=
  ∑ i, a i * ∑ j ∈ univ.erase i, b j * ∑ k ∈ (univ.erase i).erase j, c k
private def S₄ (a b c d : V q) :=
  ∑ i, a i * ∑ j ∈ univ.erase i, b j * ∑ k ∈ (univ.erase i).erase j,
    c k * ∑ l ∈ ((univ.erase i).erase j).erase k, d l

private lemma emb_prod (a b c d : V q) :
    ∑ f : Fin 4 ↪ Fin q, a (f 0) * b (f 1) * c (f 2) * d (f 3) = S₄ a b c d := by
  rw [sum_emb_fin4_eq_ind (fun i j k l => a i * b j * c k * d l)]
  simp only [S₄, ← filter_ne', sum_filter, mul_sum, mul_ite, mul_zero, filter_filter]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]
    refine sum_congr rfl fun k _ => ?_
    by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp_all
    grind

private lemma s₂_eq (a b : V q) : S₂ a b = S a * S b - S (a*b) := by
  simp [S₂, S, sum_erase_eq_sub (mem_univ _), mul_sub, sum_sub_distrib, ← sum_mul]

private lemma s₃_eq (a b c : V q) :
    S₃ a b c = S₂ a b * S c - S₂ (a*c) b - S₂ a (b*c) := by
  unfold S₃ S₂
  simp only [sum_mul, mul_sum, Pi.mul_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  refine sum_congr rfl fun j hj => ?_
  simp only [← mul_sum]
  rw [sum_erase_eq_sub hj, sum_erase_eq_sub (mem_univ i)]
  unfold S
  ring

private lemma s₄_eq (a b c d : V q) :
    S₄ a b c d = S₃ a b c * S d - S₃ (a*d) b c - S₃ a (b*d) c - S₃ a b (c*d) := by
  unfold S₄ S₃
  simp only [sum_mul, mul_sum, Pi.mul_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  refine sum_congr rfl fun j hj => ?_
  refine sum_congr rfl fun k hk => ?_
  simp only [← mul_sum]
  rw [sum_erase_eq_sub hk, sum_erase_eq_sub hj, sum_erase_eq_sub (mem_univ i)]
  unfold S
  ring

private lemma S_add (a b : V q) : S (a+b) = S a + S b := sum_add_distrib
private lemma S_sub (a b : V q) : S (a-b) = S a - S b := sum_sub_distrib _ _
private lemma S_one : S (1 : V q) = (q : ℂ) := by simp [S]
private def perm (x w : V q) : ℂ :=
  ∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + (![x, -x, w, -w] : Fin 4 → V q) i (f i))

private lemma perm_eq (x w : V q) (hx : S x = 0) (hw : S w = 0)
    (hww : S (w*w) = 0) :
    perm x w = (Fintype.card (Fin 4 ↪ Fin q) : ℂ) +
      (q-2 : ℂ)*(q-3 : ℂ)*S (x*x) + 2*(S (x*w))^2 - 6*S ((x*x)*(w*w)) := by
  have h (a b : V q) : perm a b = S₄ (1+a) (1-a) (1+b) (1-b) := by
    unfold perm
    rw [← emb_prod]
    apply sum_congr rfl
    intro f _
    simp [Fin.prod_univ_succ, sub_eq_add_neg, mul_assoc]
  have hcard : (Fintype.card (Fin 4 ↪ Fin q) : ℂ) = S₄ (1 : V q) 1 1 1 := by
    rw [← emb_prod]
    simp
  rw [h, hcard]
  simp only [s₄_eq, s₃_eq, s₂_eq, mul_add, add_mul, sub_mul, mul_sub,
    one_mul, mul_one, S_add, S_sub, S_one, hx, hw, hww]
  simp only [mul_assoc, mul_left_comm, mul_comm] at *
  simp only [zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub]
  ring

private def pad {h : ℕ} (y : V h) (n : ℕ) : V n := fun j => (List.ofFn y).getD j.val 0

private lemma pad_same {h : ℕ} (y : V h) : pad y h = y := by
  ext j
  unfold pad
  rw [List.getD_eq_getElem _ _ (show j.val < (List.ofFn y).length by simp)]
  simp

private lemma pad_left {h m n : ℕ} (y : V h) (j : Fin m) :
    pad y (m+n) (Fin.castAdd n j) = pad y m j := rfl

private lemma pad_right {h m n : ℕ} (hle : h ≤ m) (y : V h) (j : Fin n) :
    pad y (m+n) (Fin.natAdd m j) = 0 := by
  apply List.getD_eq_default
  simp
  omega

private lemma pad_sum {h : ℕ} (y : V h) (hq : h ≤ q) :
    S (pad y q) = S y ∧ S (pad y q * pad y q) = S (y*y) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hq
  simp [S, Fin.sum_univ_add, pad_left, pad_right le_rfl, pad_same]

private def Good (v x : V q) : Prop :=
  S x = 0 ∧ S (x*x) = 0 ∧ S (x*(v*v)) = 0 ∧
    S (x*v)^2 = 3*S ((x*x)*(v*v))

private lemma three_base (y : V 3) (hn : ∀ i, y i ≠ 0) (hy : S y = 0)
    (hy₂ : S (y*y) = 0) :
    ∃ K : Submodule ℂ (V 3), 2*Module.finrank ℂ K+1=3 ∧ ∀ x ∈ K, Good y x := by
  let c := y 0*y 1*y 2
  have h₁ : y 0+y 1+y 2=0 := by simpa [S, Fin.sum_univ_three] using hy
  have h₂ : y 0*y 0+y 1*y 1+y 2*y 2=0 := by simpa [S, Fin.sum_univ_three] using hy₂
  have hp : y 0*y 1+y 0*y 2+y 1*y 2=0 := by
    linear_combination ((y 0+y 1+y 2)*h₁-h₂)/2
  have hc (i : Fin 3) : y i^3=c := by
    fin_cases i <;> dsimp [c]
    · linear_combination (y 0)^2*h₁-y 0*hp
    · linear_combination (y 1)^2*h₁-y 1*hp
    · linear_combination (y 2)^2*h₁-y 2*hp
  let r := y*y
  have hr : r ≠ 0 := by
    intro he
    exact (mul_ne_zero (hn 0) (hn 0)) (congrFun he 0)
  refine ⟨Submodule.span ℂ {r}, by rw [finrank_span_singleton hr], ?_⟩
  intro x hx
  obtain ⟨z,rfl⟩ := Submodule.mem_span_singleton.mp hx
  have p₁ (i : Fin 3) : (z • r) i = z*(y i*y i) := rfl
  have p₂ (i : Fin 3) : ((z • r)*(z • r)) i = (z^2*c)*y i := by
    simp only [Pi.mul_apply, p₁, ← hc i]; ring
  have p₃ (i : Fin 3) : ((z • r)*(y*y)) i = (z*c)*y i := by
    simp only [Pi.mul_apply, p₁, ← hc i]; ring
  have p₄ (i : Fin 3) : ((z • r)*y) i = z*c := by
    simp only [Pi.mul_apply, p₁, ← hc i]; ring
  have p₅ (i : Fin 3) : ((z • r*(z • r))*(y*y)) i = (z*c)^2 := by
    simp only [Pi.mul_apply, p₁, ← hc i]; ring
  unfold S at hy hy₂
  simp only [Good, S, p₂, p₃, p₄, p₅, p₁, ← mul_sum, hy, ← Pi.mul_apply,
    hy₂, mul_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, true_and]
  ring

private def grow {K : Submodule ℂ (V q)} (a b : ℂ) : (K × ℂ) →ₗ[ℂ] V (q+2) where
  toFun p := Fin.append (fun i => (p.1 : V q) i+p.2) ![p.2*a,p.2*b]
  map_add' p r := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]; ring
    · fin_cases j <;> simp [Fin.append_right] <;> ring
  map_smul' z p := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]; ring
    · fin_cases j <;> simp [Fin.append_right] <;> ring

private lemma three_step {y : V 3} (hq : 3 ≤ q) (hy : S y = 0) (hy₂ : S (y*y) = 0)
    (ih : ∃ K : Submodule ℂ (V q), 2*Module.finrank ℂ K+1=q ∧
      ∀ x ∈ K, Good (pad y q) x) :
    ∃ K : Submodule ℂ (V (q+2)), 2*Module.finrank ℂ K+1=q+2 ∧
      ∀ x ∈ K, Good (pad y (q+2)) x := by
  obtain ⟨K, hdim, hK⟩ := ih
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (-((q:ℂ)^2+2*q)) zero_lt_two
  let a := (-(q:ℂ)+d)/2
  let b := (-(q:ℂ)-d)/2
  have hab : a+b = -(q:ℂ) := by dsimp [a,b]; ring
  have hab₂ : a^2+b^2 = -(q:ℂ) := by dsimp [a,b]; linear_combination hd/2
  have hn : (q:ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  let g := grow (K:=K) a b
  have inj : Function.Injective g := by
    apply (LinearMap.ker_eq_bot.mp _)
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x,z⟩ he
    have htail (j : Fin 2) := congrFun he (Fin.natAdd q j)
    have hza : z*a=0 := by simpa [g,grow] using htail 0
    have hzb : z*b=0 := by simpa [g,grow] using htail 1
    have hz : z=0 := by
      by_contra hnz
      rw [(mul_eq_zero.mp hza).resolve_left hnz, (mul_eq_zero.mp hzb).resolve_left hnz] at hab
      exact hn (by simpa using hab.symm)
    subst z
    apply Prod.ext
    · ext j
      simpa [g, grow] using congrFun he (Fin.castAdd 2 j)
    · rfl
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj inj, Module.finrank_prod, Module.finrank_self]
    omega
  rintro _ ⟨⟨x,z⟩,rfl⟩
  let v := pad y q
  obtain ⟨hx,hxx,hxvv,hm⟩ := hK x x.property
  obtain ⟨hv,hvv⟩ := pad_sum y hq
  change S v = _ at hv
  change S (v*v) = _ at hvv
  rw [hy] at hv
  rw [hy₂] at hvv
  change S ((x:V q)*_) = _ at hxx
  dsimp only [S,Pi.mul_apply] at hx hxx hxvv hm hv hvv
  change (∑ i, (x:V q) i*(v i*v i))=0 at hxvv
  change (∑ i, (x:V q) i*v i)^2=3*∑ i, ((x:V q) i*(x:V q) i)*(v i*v i) at hm
  have base (i : Fin q) : g (x,z) (Fin.castAdd 2 i)=(x:V q) i+z := by simp [g, grow]
  have tail (i : Fin 2) : g (x,z) (Fin.natAdd q i)=(![z*a,z*b] : Fin 2 → ℂ) i :=
    by simp [g, grow]
  simp only [Good, S, Pi.mul_apply, Fin.sum_univ_add, base, tail, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, pad_left, pad_right hq, show pad y q=v from rfl, add_mul,
    mul_add, sum_add_distrib, ← sum_mul, ← mul_sum, hx, hxx, hxvv, hv, hvv,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, zero_mul, add_zero, zero_add]
  constructor
  · linear_combination z*hab
  constructor
  · linear_combination z^2*hab₂
  constructor
  · simp
  · simp only [mul_assoc, mul_left_comm, mul_comm] at hxvv hm ⊢
    simp only [← mul_sum, hxvv, mul_zero, add_zero]
    exact hm
private def Top (v : V q) := ∃ K : Submodule ℂ (V q), 2*Module.finrank ℂ K+1=q ∧
  ∀ x ∈ K, S x=0 ∧ ∀ t : ℂ, perm x (t • v) = (Fintype.card (Fin 4 ↪ Fin q) : ℂ)

private lemma perm_scaled (x v : V q) (hx : S x=0) (hv : S v=0) (hvv : S (v*v)=0) (t : ℂ) :
    perm x (t • v) = (Fintype.card (Fin 4 ↪ Fin q) : ℂ) +
      ((q:ℂ)-2)*(q-3 : ℂ)*S (x*x) + t^2*(2*S (x*v)^2-6*S ((x*x)*(v*v))) := by
  have hs (a : V q) (z : ℂ) : S (z • a) = z*S a := by simp [S, ← mul_sum]
  have p : (t • v)*(t • v) = (t*t) • (v*v) := by ext i; simp; ring
  rw [perm_eq _ _ hx (by rw [hs,hv,mul_zero]) (by rw [p,hs,hvv,mul_zero]),p]
  simp only [mul_smul_comm, hs]
  ring

private lemma three_top (y : V 3) (hn : ∀ i, y i ≠ 0) (hy : S y = 0) (hy₂ : S (y*y) = 0)
    (hq : 3 ≤ q) (ho : Odd q) : Top (pad y q) := by
  suffices hh : ∀ k : ℕ, ∃ K : Submodule ℂ (V (3+2*k)), 2*Module.finrank ℂ K+1=3+2*k ∧
      ∀ x ∈ K, Good (pad y (3+2*k)) x by
    obtain ⟨j,hj⟩ := ho
    obtain ⟨k,rfl⟩ : ∃ k, q=3+2*k := ⟨j-1, by omega⟩
    obtain ⟨K,hK,hx⟩ := hh k
    obtain ⟨hv,hvv⟩ := pad_sum y hq
    refine ⟨K,hK,fun x hxK => ?_⟩
    obtain ⟨h₁,h₂,_,h₄⟩ := hx x hxK
    refine ⟨h₁,fun t => ?_⟩
    rw [perm_scaled x _ h₁ (hv.trans hy) (hvv.trans hy₂), h₂, h₄]
    ring
  intro k
  induction k with
  | zero => simpa [pad_same] using three_base y hn hy hy₂
  | succ k ih => exact three_step (Nat.le_add_right 3 (2*k)) hy hy₂ ih

private lemma top_forms {v : V q} (hq : 3 < q) (hv : S v=0) (hvv : S (v*v)=0)
    (ht : Top v) :
    ∃ K : Submodule ℂ (V q), 2*Module.finrank ℂ K+1=q ∧
      ∀ x ∈ K, S x=0 ∧ S (x*x)=0 ∧ S (x*v)^2=3*S ((x*x)*(v*v)) := by
  obtain ⟨K,hd,hK⟩ := ht
  refine ⟨K,hd,fun x hx => ?_⟩
  obtain ⟨h₁,hp⟩ := hK x hx
  have h₀ := hp 0
  have h₂ := hp 1
  rw [perm_scaled _ _ h₁ hv hvv] at h₀ h₂
  have hn (a : ℕ) (ha : a < q) : (q:ℂ)-(a:ℂ)≠0 := sub_ne_zero.mpr (by exact_mod_cast ha.ne')
  have c : ((q:ℂ)-2)*((q:ℂ)-3)≠0 := mul_ne_zero (hn 2 (by omega)) (hn 3 hq)
  have hs : S (x*x)=0 := (mul_eq_zero.mp (show ((q:ℂ)-2)*((q:ℂ)-3)*S (x*x)=0 by
    linear_combination h₀)).resolve_left c
  refine ⟨h₁,hs,?_⟩
  rw [hs] at h₂
  linear_combination h₂/2

private abbrev Mat (h : ℕ) := Matrix (Fin h) (Fin h) ℂ
private def metric (h : ℕ) (t : ℂ) : Mat h :=
  1 + Matrix.replicateCol Unit (fun _ : Fin h => t) * Matrix.replicateRow Unit (fun _ : Fin h => (1:ℂ))

private lemma metric_eval {h : ℕ} (t : ℂ) (x z : V h) :
    (metric h t).toBilin' x z = S (x*z)+t*S x*S z := by
  rw [Matrix.toBilin'_apply', metric, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
  simp [dotProduct, Matrix.mulVec, Matrix.mul_apply, S, ← mul_sum, ← sum_mul]
  ring

private lemma metric_det (h : ℕ) (t : ℂ) : (metric h t).det = 1+t*h := by
  rw [metric, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, mul_comm]

private def active {h : ℕ} (y : V h) : Mat h :=
  Matrix.diagonal y * metric h (-(1/3)) * Matrix.diagonal y

private lemma active_eval {h : ℕ} (y x z : V h) :
    (active y).toBilin' x z = S ((x*y)*(z*y))-(1/3)*S (x*y)*S (z*y) := by
  have e : (active y).toBilin' x z = (metric h (-(1/3))).toBilin' (x*y) (z*y) := by
    simp only [active, Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    congr 1
    · ext i; simp [Matrix.vecMul_diagonal]
    · congr 1
      ext i; simp [Matrix.mulVec_diagonal,mul_comm]
  rw [e, metric_eval]; ring

private lemma active_det {h : ℕ} (hh : 3 < h) (y : V h) (hy : ∀ i, y i ≠ 0) :
    (active y).det ≠ 0 := by
  simp only [active,Matrix.det_mul,Matrix.det_diagonal,metric_det]
  have nn : (∏ i,y i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy i)
  apply mul_ne_zero (mul_ne_zero nn _) nn
  intro he
  have eq : (h:ℂ) = 3 := by linear_combination -3*he
  exact (by omega : h ≠ 3) (by exact_mod_cast eq)

private lemma two_dim_le {h : ℕ} {L : Submodule ℂ (V h)} {B : Mat h}
    (det : B.det≠0) (iso : ∀ x ∈ L, ∀ z ∈ L, B.toBilin' x z=0) :
    2*Module.finrank ℂ L ≤ h := by
  have le : L ≤ B.toBilin'.orthogonal L := fun x hx z hz => iso z hz x hx
  have hd := Submodule.finrank_mono le
  rw [LinearMap.BilinForm.finrank_orthogonal (Matrix.Nondegenerate.of_det_ne_zero det).toBilin',
     Module.finrank_fin_fun] at hd
  have hh := Submodule.finrank_le L
  rw [Module.finrank_fin_fun] at hh
  change Module.finrank ℂ L ≤ h-Module.finrank ℂ L at hd
  change Module.finrank ℂ L ≤ h at hh
  omega

private lemma polar {n : ℕ} (L : Submodule ℂ (V n)) (B : Mat n)
    (symm : ∀ x z, B.toBilin' x z=B.toBilin' z x) (hh : ∀ x ∈ L,B.toBilin' x x=0) :
    ∀ x ∈ L, ∀ z ∈ L, B.toBilin' x z=0 := by
  intro x hx z hz
  have eq := hh _ (L.add_mem hx hz)
  simp only [map_add, LinearMap.add_apply, hh x hx, hh z hz, symm z x] at eq
  linear_combination eq/2

private lemma compress {h m : ℕ} (hh : 3 < h) (hm : 0 < m) (y : V h) (hn : ∀ i,y i ≠ 0)
    (K : Submodule ℂ (V (h+m))) (dim : 2*Module.finrank ℂ K+1=h+m)
    (hK : ∀ x ∈ K, S x=0 ∧ S (x*x)=0 ∧
      S (x*pad y (h+m))^2=3*S ((x*x)*(pad y (h+m)*pad y (h+m)))) :
    ∃ U : Submodule ℂ (V h), 2*Module.finrank ℂ U=h ∧
      (∀ x ∈ U, ∀ z ∈ U, (active y).toBilin' x z=0) ∧
      (∀ x ∈ U, ∀ z ∈ U, (metric h (m:ℂ)⁻¹).toBilin' x z=0) := by
  classical
  let l : K →ₗ[ℂ] V h := (LinearMap.funLeft ℂ ℂ (Fin.castAdd m)).comp K.subtype
  let r : K →ₗ[ℂ] V m := (LinearMap.funLeft ℂ ℂ (Fin.natAdd h)).comp K.subtype
  let f := r.comp (LinearMap.ker l).subtype
  let U := LinearMap.range l
  let T := LinearMap.range f
  have f_inj : Function.Injective f := by
    intro a b eq
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have aa : l a.val=0 := a.property
      have bb : l b.val=0 := b.property
      exact (congrFun aa j).trans (congrFun bb j).symm
    · exact congrFun eq _
  have rank := LinearMap.finrank_range_add_finrank_ker l
  have trank : Module.finrank ℂ T = Module.finrank ℂ (LinearMap.ker l) :=
    LinearMap.finrank_range_of_inj f_inj
  have rank_sum : Module.finrank ℂ U+Module.finrank ℂ T=Module.finrank ℂ K := by
    rw [trank]; exact rank
  have split_sum (p : K) : S (l p)+S (r p)=0 := by
    simpa [S,l,r,LinearMap.funLeft,Fin.sum_univ_add] using (hK p p.property).1
  have dot (p z : K) : S ((l p)*(l z))+S ((r p)*(r z))=0 := by
    have sq (x : K) : S ((l x)*(l x))+S ((r x)*(r x))=0 := by
      simpa [S,l,r,LinearMap.funLeft,Fin.sum_univ_add] using (hK x x.property).2.1
    have eq := sq (p+z)
    simp only [map_add,add_mul,mul_add] at eq
    have sa (u v : V h) : S (u+v) = S u+S v := sum_add_distrib
    have sb (u v : V m) : S (u+v) = S u+S v := sum_add_distrib
    simp only [sa,sb] at eq
    rw [mul_comm (l z) (l p),mul_comm (r z) (r p)] at eq
    linear_combination (eq-sq p-sq z)/2
  have isoU : ∀ x ∈ U, ∀ z ∈ U, (active y).toBilin' x z=0 := by
    apply polar
    · intro x z; rw [active_eval,active_eval,mul_comm (x*y) (z*y)]; ring
    · rintro _ ⟨p,rfl⟩
      have eq := (hK p p.property).2.2
      simp only [S,Fin.sum_univ_add,Pi.mul_apply,pad_left,pad_right (le_refl h),pad_same,
        mul_zero,sum_const_zero,add_zero] at eq
      rw [active_eval]
      change (∑ i, ((p:V _) (Fin.castAdd m i)*y i)*((p:V _) (Fin.castAdd m i)*y i))-
        1/3*(∑ i,(p:V _) (Fin.castAdd m i)*y i)*(∑ i,(p:V _) (Fin.castAdd m i)*y i)=0
      simp only [mul_assoc,mul_left_comm,mul_comm] at eq ⊢
      linear_combination -eq/3
  have du := two_dim_le (active_det hh y hn) isoU
  let B := (metric m 0).toBilin'
  have bval (u v : V m) : B u v=S (u*v) := by simp [B, metric_eval]
  have orth (p : K) : r p ∈ B.orthogonal T := by
    rintro _ ⟨z,rfl⟩
    have eq := dot z.val p
    rw [show l z.val=0 from z.property,zero_mul] at eq
    simpa [bval,f,S] using eq
  have torth : T ≤ B.orthogonal T := by rintro _ ⟨z,rfl⟩; exact orth z.val
  have zeroT : ∀ x ∈ T, S x=0 := by
    rintro _ ⟨z,rfl⟩
    have eq := split_sum z.val
    rw [show l z.val=0 from z.property] at eq
    simpa [f,S] using eq
  have orth1 : (1 : V m) ∈ B.orthogonal T := by
    intro x hx
    simpa [bval] using zeroT x hx
  have n1 : (1 : V m) ∉ T := by
    intro he
    simpa [S,Nat.ne_of_gt hm] using zeroT _ he
  have le : T ⊔ Submodule.span ℂ {1} ≤ B.orthogonal T :=
    sup_le torth (Submodule.span_le.mpr (by simpa using orth1))
  have bnd := Submodule.finrank_mono le
  have fr := Submodule.finrank_le T
  rw [Module.finrank_fin_fun] at fr
  have fd : Module.finrank ℂ (B.orthogonal T) = m-Module.finrank ℂ T := by
    rw [LinearMap.BilinForm.finrank_orthogonal,Module.finrank_fin_fun]
    exact (Matrix.Nondegenerate.of_det_ne_zero (show (metric m 0).det ≠ 0 by simp [metric_det])).toBilin'
  rw [fd, Submodule.finrank_sup_span_singleton n1] at bnd
  have eq : T ⊔ Submodule.span ℂ {1} = B.orthogonal T := by
    apply Submodule.eq_of_le_of_finrank_le le
    rw [fd,Submodule.finrank_sup_span_singleton n1]
    omega
  refine ⟨U,by omega,isoU,?_⟩
  apply polar
  · intro x z; rw [metric_eval,metric_eval,mul_comm x z]; ring
  · rintro _ ⟨p,rfl⟩
    have mem := orth p
    rw [← eq,Submodule.mem_sup] at mem
    obtain ⟨w,hw,_,hz,hp⟩ := mem
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    have w2 := torth hw w hw
    rw [bval] at w2
    have s := split_sum p
    have d := dot p p
    rw [← hp] at s d
    have sw := zeroT w hw
    simp [S, Finset.sum_add_distrib] at s
    change (∑ i, w i)=0 at sw
    rw [sw] at s
    have tail : S ((w+c • (1:V m))*(w+c • (1:V m)))=(m:ℂ)*c^2 := by
      simp only [S, Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one,add_mul,
        mul_add,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,sw,
        show (∑ i,w i*w i)=0 from w2, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    rw [tail] at d
    rw [metric_eval]
    have hm' : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
    have hs : S (l p)= -(m:ℂ)*c := by change (∑ i,l p i)=_; linear_combination s
    rw [hs]
    field_simp
    linear_combination d

open Polynomial
open scoped Polynomial

private lemma four_squares (P Q : ℂ[X]) (t : Fin 4 → ℂ) (ht : Function.Injective t)
    (p : Fin 4 → ℂ[X]) (hp : ∀ i, p i ^ 2 = P+C (t i)*Q)
    (hm : ∀ i, (p i ^ 2).Monic) (hd : ∀ i, (p i).natDegree=(p 0).natDegree)
    (hQ : Q ≠ 0) : False := by
  classical
  have nz (i) : p i ≠ 0 := fun h => (hm i).ne_zero (by simp [h])
  let a (i j k : Fin 4) := (t j-t k)/(t j-t i)
  let b (i j k : Fin 4) := (t k-t i)/(t j-t i)
  have mix (i j k : Fin 4) (hij : i ≠ j) :
      p k^2=C (a i j k)*p i^2+C (b i j k)*p j^2 := by
    have ne : t j-t i≠0 := sub_ne_zero.mpr (ht.ne hij.symm)
    have add : a i j k+b i j k=1 := by dsimp [a,b]; field_simp; ring
    have wt : a i j k*t i+b i j k*t j=t k := by dsimp [a,b]; field_simp; ring
    simp only [hp]
    linear_combination (norm := (simp only [map_add, map_mul, map_one] at *; ring1))
      -P*congrArg (C : ℂ →+* ℂ[X]) add-Q*congrArg (C : ℂ →+* ℂ[X]) wt
  let g := GCDMonoid.gcd (p 0) (p 1)
  have ng : g≠0 := gcd_ne_zero_of_right (nz 1)
  have dg (i) : g ∣ p i := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp
    rw [mix 0 1 i (by decide)]
    exact dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (GCDMonoid.gcd_dvd_left ..) 2) _)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (GCDMonoid.gcd_dvd_right ..) 2) _)
  let r (i : Fin 4) := p i/g
  have gr (i) : g*r i=p i := EuclideanDomain.mul_div_cancel' ng (dg i)
  have nr (i) : r i≠0 := fun h => nz i (by rw [← gr i,h,mul_zero])
  have dr (i) : (r i).natDegree=(r 0).natDegree := by
    have h := hd i
    rw [← gr i, ← gr 0, natDegree_mul ng (nr i), natDegree_mul ng (nr 0)] at h
    omega
  have red (i j k : Fin 4) (hij : i ≠ j) :
      r k^2=C (a i j k)*r i^2+C (b i j k)*r j^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ng)
    have h := mix i j k hij
    simp only [← gr, mul_pow] at h
    linear_combination h
  have base : IsCoprime (r 0) (r 1) := isCoprime_div_gcd_div_gcd (nz 1)
  have cop : Pairwise (fun i j => IsCoprime (r i) (r j)) := by
    intro i j hij
    apply (gcd_isUnit_iff _ _).mp
    apply (base.pow (m:=2) (n:=2)).isUnit_of_dvd'
    all_goals
      rw [red i j _ hij]
      exact dvd_add (dvd_mul_of_dvd_right ((GCDMonoid.gcd_dvd_left ..).trans (dvd_pow_self _ two_ne_zero)) _)
        (dvd_mul_of_dvd_right ((GCDMonoid.gcd_dvd_right ..).trans (dvd_pow_self _ two_ne_zero)) _)
  let W := wronskian (r 0^2) (r 1^2)
  have w0 : W ≠ 0 := by
    intro h
    have hder := base.pow.wronskian_eq_zero_iff.mp h
    have hdeg := derivative_eq_zero.mp hder.1
    rw [natDegree_pow] at hdeg
    have dc : (r 0).natDegree=0 := by omega
    have u : IsUnit (r 0) := by
      rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (nr 0),dc]
      rfl
    have dd : p 0^2 ∣ p 1^2 := by
      rw [← gr 0, ← gr 1, mul_pow,mul_pow]
      exact mul_dvd_mul_left _ (u.pow 2).dvd
    have he := eq_of_monic_of_dvd_of_natDegree_le (hm 0) (hm 1) dd (by simp [natDegree_pow, hd 1])
    rw [hp,hp,add_right_inj] at he
    exact ht.ne (by decide : (0:Fin 4)≠1) (C_injective (mul_right_cancel₀ hQ he.symm))
  have divides (i : Fin 4) : r i ∣ W := by
    obtain ⟨j,hj⟩ := exists_ne i
    have h0 := red i j 0 hj.symm
    have h1 := red i j 1 hj.symm
    have bil (u v s t : ℂ) (A B : ℂ[X]) :
        wronskian (C u*A+C v*B) (C s*A+C t*B) =
          (C u*C t-C v*C s)*wronskian A B := by
      simp [wronskian, derivative_add, derivative_mul]; ring
    change r i ∣ wronskian (r 0^2) (r 1^2)
    rw [h0,h1,bil]
    apply dvd_mul_of_dvd_right
    rw [wronskian, derivative_pow]
    exact dvd_sub ((dvd_pow_self _ two_ne_zero).mul_right _) (by
      use 2 * derivative (r i) * r j^2
      simp only [derivative_pow]; norm_num; simp only [map_ofNat]; ring)
  have upper := natDegree_wronskian_lt_add w0
  have lower := natDegree_le_of_dvd (Fintype.prod_dvd_of_coprime cop divides) w0
  rw [natDegree_prod _ _ (fun i _ => nr i)] at lower
  simp only [dr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at lower
  simp only [natDegree_pow,dr] at upper
  dsimp [W] at lower
  omega

open Matrix Module

private lemma square_spectrum {h : ℕ} (B G : Mat h)
    (db : B.det ≠ 0) (sB : ∀ x z, B.toBilin' x z=B.toBilin' z x)
    (sG : ∀ x z, G.toBilin' x z=G.toBilin' z x)
    (U : Submodule ℂ (V h)) (dim : 2*finrank ℂ U=h)
    (ub : ∀ x ∈ U, ∀ z ∈ U, B.toBilin' x z=0)
    (ug : ∀ x ∈ U, ∀ z ∈ U, G.toBilin' x z=0) :
    ∃ p : Polynomial ℂ, p^2=(B⁻¹*G).charpoly := by
  classical
  obtain ⟨W,hw⟩ := exists_isCompl U
  let d := finrank ℂ U
  have dw : finrank ℂ W=d := by
    have eq := Submodule.finrank_add_eq_of_isCompl hw
    rw [Module.finrank_fin_fun] at eq
    dsimp [d]; omega
  let bU := Module.finBasis ℂ U
  let bW := Module.finBasisOfFinrankEq ℂ W dw
  let b := (bU.prod bW).map (U.prodEquivOfIsCompl W hw)
  let c := b.reindex (Equiv.sumComm (Fin d) (Fin d))
  have bin (i : Fin d) : b (Sum.inl i) ∈ U := by
    simp [b,Module.Basis.prod_apply]
  let coord (H : LinearMap.BilinForm ℂ (V h)) := LinearMap.toMatrix b c.dualBasis H
  let cross (H : LinearMap.BilinForm ℂ (V h)) : Mat d :=
    Matrix.of fun i j => H (b (Sum.inl j)) (b (Sum.inr i))
  have coords (H : LinearMap.BilinForm ℂ (V h)) (i j) :
      coord H i j = H (b j) (b (Sum.swap i)) := by
    simp [coord,c,LinearMap.toMatrix_apply,Module.Basis.reindex_apply]
  have gram (H : LinearMap.BilinForm ℂ (V h))
      (sym : ∀ x z,H x z=H z x) (van : ∀ x ∈ U,∀ z ∈ U,H x z=0) :
      (coord H).det=(cross H).det^2 := by
    let E : Mat d := Matrix.of fun i j => H (b (Sum.inr j)) (b (Sum.inr i))
    have mat : coord H=Matrix.fromBlocks (cross H) E 0 (cross H).transpose := by
      ext i j
      rw [coords]
      cases i with
      | inl i => cases j <;> rfl
      | inr i =>
        cases j with
        | inl j => exact van _ (bin j) _ (bin i)
        | inr j => exact sym _ _
    rw [mat,Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose,pow_two]
  let T := (B⁻¹*G).toLin'
  let M := LinearMap.toMatrix b b T
  have comp : LinearMap.comp B.toBilin' T = G.toBilin' := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    change B.toBilin' (T x) z = G.toBilin' x z
    rw [sB,sG]
    simp only [T, Matrix.toBilin'_apply', Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr db),Matrix.one_mul]
  have cm : coord B.toBilin' * M=coord G.toBilin' := by
    exact (LinearMap.toMatrix_comp b b c.dualBasis B.toBilin' T).symm.trans (congrArg coord comp)
  have nonsing : IsUnit (coord B.toBilin').det := by
    let e := B.toBilin'.toDual (Matrix.Nondegenerate.of_det_ne_zero db).toBilin'
    have rr := LinearMap.toMatrix_comp c.dualBasis b c.dualBasis e.toLinearMap e.symm.toLinearMap
    have eid : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by ext x; simp
    rw [eid,LinearMap.toMatrix_id] at rr
    exact isUnit_iff_ne_zero.mpr (fun z => by
      have ee := congrArg Matrix.det rr
      rw [Matrix.det_one,Matrix.det_mul] at ee
      change (1:ℂ)=(coord B.toBilin').det*_ at ee
      simp [z] at ee)
  let D := cross B.toBilin'
  let F := cross G.toBilin'
  have dd : D.det≠0 := by
    have ne := nonsing.ne_zero
    rw [gram _ sB ub] at ne
    exact fun eq => ne (by change D.det^2=0; rw [eq]; norm_num)
  refine ⟨(D⁻¹*F).charpoly, Polynomial.funext (fun z => ?_)⟩
  have ev : (B⁻¹*G).charpoly = M.charpoly := by
    rw [show M = LinearMap.toMatrix b b T from rfl, LinearMap.charpoly_toMatrix]
    exact (Matrix.charpoly_toLin' _).symm
  rw [ev, Polynomial.eval_pow,Matrix.eval_charpoly,Matrix.eval_charpoly]
  let H := z • B.toBilin' - G.toBilin'
  have sym (x w) : H x w=H w x := by simp [H,sB x w,sG x w]
  have van : ∀ x ∈ U,∀ w ∈ U,H x w=0 := by
    intro x hx w hw'
    simp [H,ub x hx w hw',ug x hx w hw']
  have scalar_mul' {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
      A*Matrix.scalar n z=z • A := by
    change A * Matrix.diagonal (fun _ => z) = _
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have prod : coord B.toBilin' * (Matrix.scalar _ z - M) = coord H := by
    rw [mul_sub, scalar_mul',cm]
    simp [coord,H]
  have smaller : D*(Matrix.scalar _ z-D⁻¹*F)=cross H := by
    rw [mul_sub,scalar_mul',← Matrix.mul_assoc,Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr dd),Matrix.one_mul]
    ext i j
    simp [cross,H,D,F]
  have eq := congrArg Matrix.det prod
  rw [Matrix.det_mul,gram _ sB ub,gram H sym van,← smaller, Matrix.det_mul,mul_pow] at eq
  exact (mul_left_cancel₀ (pow_ne_zero 2 dd) eq).symm

private lemma det_pencil {n : ℕ} (A : Mat n) (u : Matrix (Fin n) Unit ℂ)
    (v : Matrix Unit (Fin n) ℂ) (t : ℂ) :
    (A-u*(t • v)).det=A.det+t*((A-u*v).det-A.det) := by
  let M (s : ℂ) := Matrix.fromBlocks A u (s • v) (1 : Matrix Unit Unit ℂ)
  let i : Fin n ⊕ Unit := .inr ()
  let w : (Fin n ⊕ Unit) → ℂ := Sum.elim (v ()) (fun _ => 0)
  have up (s : ℂ) : M s = (M 0).updateRow i (M 0 i+s • w) := by
    ext a b
    cases a with
    | inl k => cases b <;> simp [M,Matrix.updateRow,Function.update, i]
    | inr k => cases k; cases b <;> simp [M,Matrix.updateRow,Function.update,i,w]
  have aff (s : ℂ) : (M s).det=(M 0).det+s*((M 0).updateRow i w).det := by
    rw [up s, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  have e := aff 1
  have f := aff t
  simp [M] at e f
  rw [Matrix.mul_smul]
  linear_combination f-t*e

private def poly {h : ℕ} (B : Mat h) (s : ℂ) := (B⁻¹*metric h s).charpoly

private lemma poly_aff {h : ℕ} (B : Mat h) (s : ℂ) :
    poly B s=poly B 0+C s*(poly B 1-poly B 0) := by
  let u := Matrix.replicateCol Unit (fun _ : Fin h => (1:ℂ))
  let v := Matrix.replicateRow Unit (fun _ : Fin h => (1:ℂ))
  have eg (t : ℂ) : metric h t=1+u*(t • v) := by
    unfold metric
    apply congrArg (fun K : Mat h => 1+K)
    ext i j
    simp [u,v,Matrix.mul_apply]
  apply Polynomial.funext
  intro z
  simp only [poly,Polynomial.eval_add, Polynomial.eval_mul,Polynomial.eval_C, Polynomial.eval_sub,
    Matrix.eval_charpoly, eg, zero_smul, one_smul, Matrix.mul_zero,add_zero,
    Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,← sub_sub]
  exact det_pencil _ _ _ _

private lemma poly_nonconst {h : ℕ} (hh : 0 < h) (B : Mat h) (db : B.det≠0) :
    poly B 1-poly B 0≠0 := by
  intro eq
  have e := congrArg (Polynomial.eval 0) (sub_eq_zero.mp eq)
  simp only [poly, Matrix.eval_charpoly, map_zero,zero_sub,Matrix.det_neg,Matrix.det_mul,
    Matrix.det_nonsing_inv, metric,Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct] at e
  simp only [Fintype.card_fin,mul_zero,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,add_zero,Ring.inverse_eq_inv] at e
  have ne : (-1:ℂ)^h*B.det⁻¹≠0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero db)
  have he : (-1:ℂ)^h*B.det⁻¹*(h:ℂ)=0 := by linear_combination e
  exact (mul_ne_zero ne (by exact_mod_cast hh.ne')) he

private lemma compressed_top {h q : ℕ} (hh : 3 < h) (y : V h) (hn : ∀ i, y i ≠ 0)
    (hy : S y=0) (hy₂ : S (y*y)=0) (hq : h < q) (ht : Top (pad y q)) :
    ∃ U : Submodule ℂ (V h), 2*Module.finrank ℂ U=h ∧
      (∀ x ∈ U, ∀ z ∈ U, (active y).toBilin' x z=0) ∧
      (∀ x ∈ U, ∀ z ∈ U, (metric h ((q-h:ℕ):ℂ)⁻¹).toBilin' x z=0) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hq.le
  obtain ⟨hv,hvv⟩ := pad_sum y hq.le
  obtain ⟨K,dim,hK⟩ := top_forms (by omega) (hv.trans hy) (hvv.trans hy₂) ht
  simpa using compress hh (by omega : 0 < m) y hn K dim hK

private lemma widths {h : ℕ} (hh : 3 < h) (y : V h) (hn : ∀ i,y i ≠ 0)
    (hy : S y=0) (hy₂ : S (y*y)=0) (W : Finset ℕ)
    (hw : ∀ q ∈ W, h < q ∧ Odd q ∧ Top (pad y q)) : W.card ≤ 3 := by
  classical
  by_contra! too_many
  obtain ⟨A,sub,card⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ W.card)
  let k := A.orderEmbOfFin card
  have good (i : Fin 4) := hw (k i) (sub (A.orderEmbOfFin_mem card i))
  let t (i : Fin 4) := (((k i-h : ℕ) : ℂ))⁻¹
  have inj : Function.Injective t := by
    intro i j eq
    apply k.injective
    have he : k i-h=k j-h := by
      apply Nat.cast_injective (R:=ℂ)
      exact inv_injective eq
    have hi := (good i).1
    have hj := (good j).1
    omega
  let B := active y
  have nz : B.det ≠ 0 := active_det hh y hn
  have sq (i : Fin 4) : ∃ p : Polynomial ℂ, p^2=poly B (t i) := by
    obtain ⟨U,ud,ub,ug⟩ := compressed_top hh y hn hy hy₂ (good i).1 (good i).2.2
    apply square_spectrum B (metric h (t i)) nz _ _ U ud ub ug
    · intro x z; rw [show B = active y from rfl,active_eval,active_eval,mul_comm (x*y) (z*y)]; ring
    · intro x z; rw [metric_eval,metric_eval,mul_comm x z]; ring
  choose p hp using sq
  have deg (i) : 2*(p i).natDegree=h := by
    simpa only [poly,Polynomial.natDegree_pow,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin] using
      congrArg Polynomial.natDegree (hp i)
  exact four_squares (poly B 0) (poly B 1-poly B 0) t inj p
    (fun i => (hp i).trans (poly_aff B _)) (fun i => by rw [hp i]; exact Matrix.charpoly_monic _)
    (fun i => by have := deg i; have := deg 0; omega) (poly_nonconst (by omega) B nz)
end
end PEqualNP.Outside.L_gct_299

open PEqualNP.Outside.L_gct_299 in
theorem PEqualNP.Outside.L_gct_299 : (∀ (h : ℕ) (y : Fin h → ℂ), 3 ≤ h → (∀ i, y i ≠ 0) →
  (∑ i, y i) = 0 → (∑ i, (y i)^2) = 0 →
  let top := fun q : ℕ =>
    let v := fun j : Fin q => (List.ofFn y).getD j.val 0
    ∃ K : Submodule ℂ (Fin q → ℂ), 2 * Module.finrank ℂ K + 1 = q ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ,
        let rows : Fin 4 → Fin q → ℂ := ![x, -x, t • v, -(t • v)]
        (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
          (Fintype.card (Fin 4 ↪ Fin q) : ℂ)
  (h = 3 → ∀ q : ℕ, h < q → Odd q → top q) ∧
  (3 < h → Odd h → ∀ q : ℕ, h < q → Odd q → ¬ top q) ∧
  (3 < h → ∀ W : Finset ℕ, (∀ q ∈ W, h < q ∧ Odd q ∧ top q) → W.card ≤ 3)) := by
  intro h y _ hn hy hy₂
  change (h = 3 → ∀ q, h < q → Odd q → Top (pad y q)) ∧
    (3 < h → Odd h → ∀ q, h < q → Odd q → ¬ Top (pad y q)) ∧
    (3 < h → ∀ W : Finset ℕ, (∀ q ∈ W, h < q ∧ Odd q ∧ Top (pad y q)) → W.card ≤ 3)
  have hs : S (y*y)=0 := by simpa [S,pow_two] using hy₂
  constructor
  · rintro rfl q hq odd
    exact three_top y hn hy hs hq.le odd
  constructor
  · rintro hh ⟨d,hd⟩ q hq _ ht
    obtain ⟨U,du,_,_⟩ := compressed_top hh y hn hy hs hq ht
    omega
  · intro hh W hw
    exact widths hh y hn hy hs W hw
