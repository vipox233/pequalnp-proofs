import PEqualNP.Defs
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Pi

namespace PEqualNP.Outside.L_meta_32485_aux

namespace PrivateTask346AffineCubic

abbrev F := ZMod 2

def delta {V : Type*} [Add V] (f : V → F) (v x : V) : F := f (x+v)-f x
def DegreeThree {V : Type*} [Add V] (f : V → F) : Prop :=
  ∀ (v : Fin 4 → V) (x : V), (List.ofFn v).foldl delta f x = 0

variable {V U : Type*} [AddCommGroup V] [Module F V] [AddCommGroup U] [Module F U]

lemma delta_pullback (L : V →ₗ[F] U) (c : U) (f : U → F) (v : V) :
    delta (fun x => f (L x+c)) v = fun x => delta f (L v) (L x+c) := by
  funext x
  unfold delta
  change f (L (x+v)+c)-f (L x+c) = f ((L x+c)+L v)-f (L x+c)
  rw [map_add]
  have he : (L x+L v)+c = (L x+c)+L v := by abel
  rw [he]

lemma fold_pullback (L : V →ₗ[F] U) (c : U) (vs : List V) (f : U → F) :
    vs.foldl delta (fun x => f (L x+c)) =
      fun x => (vs.map L).foldl delta f (L x+c) := by
  induction vs generalizing f with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [delta_pullback]
    exact ih (delta f (L v))

theorem cubic_pullback (L : V →ₗ[F] U) (c : U) (f : U → F) (hf : DegreeThree f) :
    DegreeThree (fun x => f (L x+c)) := by
  intro v x
  have he := congrFun (fold_pullback L c (List.ofFn v) f) x
  rw [List.map_ofFn] at he
  exact he.trans (hf (fun i => L (v i)) (L x+c))

theorem cubic_lift (L : V →ₗ[F] U) (R : U →ₗ[F] V)
    (hLR : ∀ z : U, L (R z) = z) (c : V) (q : U → F) (hq : DegreeThree q) :
    ∃ p : V → F, DegreeThree p ∧ ∀ z : U, p (R z+c) = q z := by
  refine ⟨fun x => q (L x + (-L c)),cubic_pullback L (-L c) q hq,?_⟩
  intro z
  simp only [map_add,hLR,add_neg_cancel_right]

theorem question_lift (L : V →ₗ[F] U) (R : U →ₗ[F] V)
    (hLR : ∀ z : U, L (R z) = z) (c : V) (a : U →ₗ[F] F) :
    ∃ b : V →ₗ[F] F, ∀ z : U, b (R z+c) = a z + a (L c) := by
  refine ⟨a.comp L,?_⟩
  intro z
  simp [LinearMap.comp_apply,hLR]

end PrivateTask346AffineCubic

namespace PrivateTask346CubePrice

abbrev F := ZMod 2
abbrev W := Fin 4 → F
abbrev Cube := Bool × Bool × Bool × Bool

def bit (a : Bool) : F := a.toNat
def point (a b c d : Bool) : W := ![bit a,bit b,bit c,bit d]
def vec (z : Cube) : W := point z.1 z.2.1 z.2.2.1 z.2.2.2
def dirs : Fin 4 → W := ![point true false false false,
  point false true false false,point false false true false,point false false false true]
def diff (f : W → F) (v x : W) : F := f (x+v)-f x
def Cubic (f : W → F) : Prop := ∀ (v : Fin 4 → W) (x : W), (List.ofFn v).foldl diff f x = 0
def quartic (z : W) : F := z 0 * z 1 * z 2 * z 3

lemma bit_xor (a b : Bool) : bit (xor a b) = bit a + bit b := by
  cases a <;> cases b <;> decide +kernel

lemma point_add (a b c d a' b' c' d' : Bool) :
    point a b c d + point a' b' c' d' =
      point (xor a a') (xor b b') (xor c c') (xor d d') := by
  funext i
  fin_cases i <;> simp [point,bit_xor]

lemma cubic_sum (f : W → F) (hf : Cubic f) :
    ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f (point a b c d) = 0 := by
  have hh := hf dirs 0
  norm_num [dirs,List.ofFn_succ,diff,point_add] at hh
  simp only [Fintype.sum_bool]
  have hzero : point false false false false = (0 : W) := by
    funext i
    fin_cases i <;> rfl
  rw [hzero]
  linear_combination (norm := ring_nf) hh
  simp only [show (2 : F) = 0 by decide +kernel,mul_zero,add_zero,sub_self]

lemma quartic_sum :
    ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, quartic (point a b c d) = 1 := by
  norm_num [Fintype.sum_bool,quartic,point,bit]

theorem cubic_disagreement (p q : W → F) (hp : Cubic p) (hq : Cubic q) :
    ∃ a b c d : Bool, quartic (point a b c d) + q (point a b c d) ≠ p (point a b c d) := by
  by_contra hn
  push Not at hn
  have hs : (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, (quartic (point a b c d) + q (point a b c d))) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, p (point a b c d) := by
    simp_rw [hn]
  simp only [Finset.sum_add_distrib] at hs
  rw [quartic_sum,cubic_sum q hq,cubic_sum p hp] at hs
  norm_num at hs

theorem cubic_agreement_le_fifteen (p q : W → F) (hp : Cubic p) (hq : Cubic q) :
    ((Finset.univ : Finset Cube).filter fun z => quartic (vec z) + q (vec z) = p (vec z)).card ≤ 15 := by
  classical
  obtain ⟨a,b,c,d,hd⟩ := cubic_disagreement p q hp hq
  have sub : ((Finset.univ : Finset Cube).filter fun z => quartic (vec z) + q (vec z) = p (vec z)) ⊆
      (Finset.univ : Finset Cube).erase (a,b,c,d) := by
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro he
    subst z
    exact hd (Finset.mem_filter.mp hz).2
  have bound := Finset.card_le_card sub
  simpa using bound

end PrivateTask346CubePrice

namespace PrivateTask346OneFace
open PrivateTask346CubePrice

def hitSet {m : ℕ} (C : Fin m → F) (q p : Fin m → W → F) : Finset Cube :=
  Finset.univ.filter fun z => ∀ j, C j * quartic (vec z) + q j (vec z) = p j (vec z)

lemma field_cases : ∀ a : F, a = 0 ∨ a = 1 := by decide +kernel

lemma cubic_add (p q : W → F) (hp : Cubic p) (hq : Cubic q) :
    Cubic (fun z => p z + q z) := by
  intro v x
  have a := hp v x
  have b := hq v x
  norm_num [List.ofFn_succ,diff] at a b ⊢
  linear_combination a+b

lemma cubic_const_mul (q : W → F) (hq : Cubic q) (a : F) :
    Cubic (fun z => a * q z) := by
  intro v x
  have h := hq v x
  norm_num [List.ofFn_succ,diff] at h ⊢
  linear_combination a*h

lemma cubic_triple : Cubic (fun z : W => z 1 * z 2 * z 3) := by
  intro v x
  norm_num [List.ofFn_succ,diff,Pi.add_apply]
  ring

lemma zero_quartic_count :
    ((Finset.univ : Finset Cube).filter fun z => quartic (vec z) = 0).card = 15 := by
  decide +kernel

theorem vector_zero_query_price {m : ℕ} (C : Fin m → F) (q : Fin m → W → F)
    (hq : ∀ j, Cubic (q j)) :
    (∀ p : Fin m → W → F, (∀ j, Cubic (p j)) →
      (hitSet C q p).card ≤ if ∀ j, C j = 0 then 16 else 15) ∧
    (∃ p : Fin m → W → F, (∀ j, Cubic (p j)) ∧
      (hitSet C q p).card = if ∀ j, C j = 0 then 16 else 15) := by
  classical
  by_cases hc : ∀ j, C j = 0
  · rw [if_pos hc]
    constructor
    · intro p hp
      have h := Finset.card_le_card (Finset.filter_subset (fun z => ∀ j, C j * quartic (vec z) + q j (vec z) = p j (vec z)) Finset.univ)
      simpa [hitSet] using h
    · refine ⟨q,hq,?_⟩
      have he : hitSet C q q = Finset.univ := by
        ext z
        simp [hitSet,hc]
      rw [he]
      simp
  · rw [if_neg hc]
    obtain ⟨j,hj⟩ : ∃ j, C j ≠ 0 := by simpa only [not_forall] using hc
    have hone : C j = 1 := (field_cases (C j)).resolve_left hj
    constructor
    · intro p hp
      have sub : hitSet C q p ⊆ ((Finset.univ : Finset Cube).filter fun z =>
          quartic (vec z) + q j (vec z) = p j (vec z)) := by
        intro z hz
        have h := (Finset.mem_filter.mp hz).2 j
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [hone] using h⟩
      exact (Finset.card_le_card sub).trans (cubic_agreement_le_fifteen (p j) (q j) (hp j) (hq j))
    · refine ⟨q,hq,?_⟩
      have he : hitSet C q q = ((Finset.univ : Finset Cube).filter fun z => quartic (vec z) = 0) := by
        ext z
        simp only [hitSet,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hz
          have h := hz j
          rw [hone,one_mul] at h
          exact add_right_cancel (h.trans (zero_add _).symm)
        · intro hz i
          rw [hz,mul_zero,zero_add]
      rw [he,zero_quartic_count]

def coordinateAsk : W →ₗ[F] F where
  toFun := fun z => z 0
  map_add' := by intro a b; rfl
  map_smul' := by intro a b; rfl

theorem one_question_attains_all {m : ℕ} (C : Fin m → F) (q : Fin m → W → F)
    (hq : ∀ j, Cubic (q j)) :
    ∃ p : F → Fin m → W → F, (∀ b j, Cubic (p b j)) ∧
      ∀ z : W, ∀ j : Fin m, C j * quartic z + q j z = p (coordinateAsk z) j z := by
  let p := fun (b : F) (j : Fin m) (z : W) => q j z + (C j * b) * (z 1 * z 2 * z 3)
  refine ⟨p,fun b j => cubic_add _ _ (hq j) (cubic_const_mul _ cubic_triple _),?_⟩
  intro z j
  change C j * quartic z + q j z = q j z + (C j * z 0) * (z 1 * z 2 * z 3)
  unfold quartic
  ring

end PrivateTask346OneFace

namespace PrivateTask346CubicClosure
open PrivateTask346AffineCubic

variable {V : Type*} [AddCommGroup V] [Module F V]

lemma cubic_zero : DegreeThree (fun _ : V => (0 : F)) := by
  intro v x
  simp [List.ofFn_succ,delta]

lemma cubic_add (p q : V → F) (hp : DegreeThree p) (hq : DegreeThree q) :
    DegreeThree (fun z => p z + q z) := by
  intro v x
  have a := hp v x
  have b := hq v x
  norm_num [List.ofFn_succ,delta] at a b ⊢
  linear_combination a+b

lemma cubic_const_mul (q : V → F) (hq : DegreeThree q) (a : F) :
    DegreeThree (fun z => a * q z) := by
  intro v x
  have h := hq v x
  norm_num [List.ofFn_succ,delta] at h ⊢
  linear_combination a*h

lemma cubic_finset_sum {ι : Type*} (S : Finset ι) (f : ι → V → F)
    (hf : ∀ i ∈ S, DegreeThree (f i)) : DegreeThree (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (cubic_zero (V := V))
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact cubic_add _ _ (hf i (by simp))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

abbrev Block := Fin 4 → F
abbrev Blocks (s : ℕ) := Fin s → Block

def blockProj {s : ℕ} (i : Fin s) : Blocks s →ₗ[F] Block where
  toFun := fun z => z i
  map_add' := by intro a b; rfl
  map_smul' := by intro a b; rfl

def coordinate {s : ℕ} (i : Fin s) : Blocks s →ₗ[F] F where
  toFun := fun z => z i 0
  map_add' := by intro a b; rfl
  map_smul' := by intro a b; rfl

theorem cubic_block_triple {s : ℕ} (i : Fin s) :
    DegreeThree (fun z : Blocks s => z i 1 * z i 2 * z i 3) := by
  have ht : DegreeThree (fun z : Block => z 1 * z 2 * z 3) :=
    PrivateTask346OneFace.cubic_triple
  have h := cubic_pullback (blockProj i) 0 _ ht
  simpa [blockProj] using h

end PrivateTask346CubicClosure

namespace PrivateTask346QuarticTranslate
open PrivateTask346CubePrice PrivateTask346OneFace

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem quartic_translation_cubic (c : W) : Cubic (fun z : W => quartic (z+c)-quartic z) := by
  intro v x
  norm_num [List.ofFn_succ,diff,quartic,Pi.add_apply]
  ring

lemma cubic_translate (q : W → F) (hq : Cubic q) (c : W) : Cubic (fun z => q (z+c)) := by
  have hq' : PrivateTask346AffineCubic.DegreeThree q := hq
  have hp := PrivateTask346AffineCubic.cubic_pullback (LinearMap.id : W →ₗ[F] W) c q hq'
  exact hp

theorem vector_translation_remainder {m : ℕ} (C : Fin m → F) (q : Fin m → W → F)
    (hq : ∀ j, Cubic (q j)) (c : W) :
    ∃ r : Fin m → W → F, (∀ j, Cubic (r j)) ∧ ∀ z : W, ∀ j : Fin m,
      C j * quartic (z+c) + q j (z+c) = C j * quartic z + r j z := by
  let r := fun (j : Fin m) (z : W) => C j * (quartic (z+c)-quartic z) + q j (z+c)
  refine ⟨r,?_,?_⟩
  · intro j
    exact cubic_add _ _ (cubic_const_mul _ (quartic_translation_cubic c) _)
      (cubic_translate (q j) (hq j) c)
  · intro z j
    change C j * quartic (z+c) + q j (z+c) =
      C j * quartic z + (C j * (quartic (z+c)-quartic z) + q j (z+c))
    ring

end PrivateTask346QuarticTranslate

namespace PrivateTask346AffineProducts
open PrivateTask346AffineCubic PrivateTask346CubicClosure

variable {V : Type*} [AddCommGroup V] [Module F V]

def tuple (L : Fin 4 → V →ₗ[F] F) : V →ₗ[F] (Fin 4 → F) where
  toFun := fun x i => L i x
  map_add' := by intro x y; ext i; exact map_add (L i) x y
  map_smul' := by intro c x; ext i; exact map_smul (L i) c x

def prod4 (L : Fin 4 → V →ₗ[F] F) (x : V) : F := L 0 x * L 1 x * L 2 x * L 3 x

theorem cubic_affine_triple (L : Fin 3 → V →ₗ[F] F) (c : Fin 3 → F) :
    DegreeThree (fun x => (L 0 x + c 0) * (L 1 x + c 1) * (L 2 x + c 2)) := by
  let L4 : Fin 4 → V →ₗ[F] F := ![0, L 0, L 1, L 2]
  let c4 : Fin 4 → F := ![0, c 0, c 1, c 2]
  have h := cubic_pullback (tuple L4) c4
    (fun z : Fin 4 → F => z 1 * z 2 * z 3) PrivateTask346OneFace.cubic_triple
  simpa [tuple, L4, c4] using h

theorem cubic_affine_pair (L M : V →ₗ[F] F) (c d : F) :
    DegreeThree (fun x => (L x + c) * (M x + d)) := by
  have h := cubic_affine_triple ![L, M, 0] ![c, d, 1]
  simpa using h

theorem cubic_affine (L : V →ₗ[F] F) (c : F) : DegreeThree (fun x => L x + c) := by
  have h := cubic_affine_pair L 0 c 1
  simpa using h

theorem cubic_quartic_shift (L : Fin 4 → V →ₗ[F] F) (c : Fin 4 → F) :
    DegreeThree (fun x =>
      (L 0 x+c 0)*(L 1 x+c 1)*(L 2 x+c 2)*(L 3 x+c 3)-prod4 L x) := by
  have h := cubic_pullback (tuple L) 0 _
    (PrivateTask346QuarticTranslate.quartic_translation_cubic c)
  simpa [tuple, prod4, PrivateTask346CubePrice.quartic] using h

lemma square (x : F) : x*x=x := by
  obtain h | h := PrivateTask346OneFace.field_cases x <;> simp [h]

theorem cubic_repeated_quartic (L M N : V →ₗ[F] F) :
    DegreeThree (fun x => L x * L x * M x * N x) := by
  have h := cubic_affine_triple ![L, M, N] 0
  simpa [square] using h

end PrivateTask346AffineProducts

namespace PrivateTask346QuadraticLayers
open PrivateTask346AffineCubic PrivateTask346CubicClosure PrivateTask346AffineProducts

variable {V : Type*} [AddCommGroup V] [Module F V]

def quadratic (A B : Fin 3 → V →ₗ[F] F) (x : V) : F := ∑ i, A i x * B i x

theorem cubic_quadratic_affine (A B : Fin 3 → V →ₗ[F] F) (L : V →ₗ[F] F) (c : F) :
    DegreeThree (fun x => quadratic A B x * (L x+c)) := by
  have h := cubic_finset_sum Finset.univ
    (fun i x => (A i x * B i x) * (L x+c)) (by
      intro i hi
      have ht := cubic_affine_triple ![A i, B i, L] ![0, 0, c]
      simpa using ht)
  simpa [quadratic, Finset.sum_mul] using h

theorem cubic_quadratic (A B : Fin 3 → V →ₗ[F] F) : DegreeThree (quadratic A B) := by
  have h := cubic_quadratic_affine A B 0 1
  simpa using h

theorem product_remainder_cubic (A B C D : Fin 3 → V →ₗ[F] F)
    (L M : V →ₗ[F] F) (c d : F) :
    DegreeThree (fun x => (quadratic A B x + (L x+c)) *
      (quadratic C D x + (M x+d)) - quadratic A B x * quadratic C D x) := by
  have h1 := cubic_quadratic_affine A B M d
  have h2 := cubic_quadratic_affine C D L c
  have h3 := cubic_affine_pair L M c d
  have he : (fun x => (quadratic A B x + (L x+c)) *
      (quadratic C D x + (M x+d)) - quadratic A B x * quadratic C D x) =
      (fun x => quadratic A B x * (M x+d) +
        quadratic C D x * (L x+c) + (L x+c)*(M x+d)) := by
    funext x
    ring
  rw [he]
  exact cubic_add _ _ (cubic_add _ _ h1 h2) h3

theorem two_layer_remainder_cubic (A B C D E G : Fin 3 → V →ₗ[F] F)
    (L M N P : V →ₗ[F] F) (c d e f : F) :
    DegreeThree (fun x =>
      (quadratic A B x + (L x+c)) +
      (1 + (quadratic C D x + (M x+d))) * (quadratic E G x + (N x+e)) +
      (P x+f) - quadratic C D x * quadratic E G x) := by
  have hp := product_remainder_cubic C D E G M N (d+1) e
  have hq := cubic_add _ _ (cubic_quadratic A B) (cubic_affine L c)
  have hr := cubic_affine P f
  have he : (fun x =>
      (quadratic A B x + (L x+c)) +
      (1 + (quadratic C D x + (M x+d))) * (quadratic E G x + (N x+e)) +
      (P x+f) - quadratic C D x * quadratic E G x) =
      (fun x => (quadratic A B x + (L x+c)) +
        ((quadratic C D x + (M x+(d+1))) * (quadratic E G x + (N x+e)) -
          quadratic C D x * quadratic E G x) + (P x+f)) := by
    funext x
    ring
  rw [he]
  exact cubic_add _ _ (cubic_add _ _ hq hp) hr

theorem first_layer_identity (L M N P : V →ₗ[F] F) (c d e f : F) (x : V) :
    (L x+c) + (1+(M x+d))*(N x+e) + (P x+f) =
      M x*N x +
        ((L + ((1+d) • N) + (e • M) + P) x + (c+(1+d)*e+f)) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

end PrivateTask346QuadraticLayers

namespace PrivateTask346RawDegree
open PrivateTask346AffineCubic PrivateTask346QuadraticLayers

abbrev W (k : ℕ) := Fin k → F

def ix {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n%k, Nat.mod_lt _ hk⟩

def rot {k : ℕ} (hk : 0 < k) (a : ℕ) : W k →ₗ[F] W k where
  toFun := fun x i => x (ix hk (i.val+k-a%k))
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def mix {k : ℕ} (hk : 0 < k) (a : ℕ) : W k →ₗ[F] W k where
  toFun := fun x i => x i+x (ix hk (i.val+a))+x (ix hk (i.val+k-a%k))
  map_add' := by intro x y; ext i; simp only [Pi.add_apply]; ring
  map_smul' := by intro c x; ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def step {k : ℕ} (hk : 0 < k) (x : W k) (i : Fin k) : F :=
  x i+(1+x (ix hk (i.val+1)))*x (ix hk (i.val+2))

def scalarAt {k : ℕ} (L : W k →ₗ[F] W k) (i : Fin k) : W k →ₗ[F] F where
  toFun := fun x => L x i
  map_add' := by intro x y; exact congrFun (map_add L x y) i
  map_smul' := by intro c x; exact congrFun (map_smul L c x) i

def firstLinear {k : ℕ} (hk : 0 < k) (a r : ℕ) : W k →ₗ[F] W k :=
  (mix hk a).comp (rot hk r)

def inner {k : ℕ} (hk : 0 < k) (a r : ℕ) (E : W k →ₗ[F] W k)
    (u c : W k) (w : W k) : W k := step hk (mix hk a (rot hk r w+u))+E w+c

def remLinear {k : ℕ} (hk : 0 < k) (a r : ℕ) (E : W k →ₗ[F] W k)
    (u : W k) (i : Fin k) : W k →ₗ[F] F :=
  scalarAt (firstLinear hk a r) i +
    ((1+mix hk a u (ix hk (i.val+1))) • scalarAt (firstLinear hk a r) (ix hk (i.val+2))) +
    ((mix hk a u (ix hk (i.val+2))) • scalarAt (firstLinear hk a r) (ix hk (i.val+1))) + scalarAt E i

def remConstant {k : ℕ} (hk : 0 < k) (a : ℕ) (u c : W k) (i : Fin k) : F :=
  mix hk a u i+(1+mix hk a u (ix hk (i.val+1)))*mix hk a u (ix hk (i.val+2))+c i

theorem inner_identity {k : ℕ} (hk : 0 < k) (a r : ℕ) (E : W k →ₗ[F] W k)
    (u c w : W k) (i : Fin k) :
    inner hk a r E u c w i =
      scalarAt (firstLinear hk a r) (ix hk (i.val+1)) w *
        scalarAt (firstLinear hk a r) (ix hk (i.val+2)) w +
      (remLinear hk a r E u i w + remConstant hk a u c i) := by
  have hi := first_layer_identity
    (scalarAt (firstLinear hk a r) i)
    (scalarAt (firstLinear hk a r) (ix hk (i.val+1)))
    (scalarAt (firstLinear hk a r) (ix hk (i.val+2))) (scalarAt E i)
    (mix hk a u i) (mix hk a u (ix hk (i.val+1)))
    (mix hk a u (ix hk (i.val+2))) (c i) w
  simpa only [inner, step, map_add, Pi.add_apply, firstLinear, LinearMap.comp_apply,
    scalarAt, LinearMap.coe_mk, AddHom.coe_mk, remLinear, remConstant, add_assoc] using hi

def selected {k : ℕ} (hk : 0 < k) (a : ℕ) (i : Fin k) : Fin 3 → Fin k :=
  ![i, ix hk (i.val+a), ix hk (i.val+k-a%k)]

theorem mix_sum {k : ℕ} (hk : 0 < k) (a : ℕ) (w : W k) (i : Fin k) :
    mix hk a w i = ∑ t : Fin 3, w (selected hk a i t) := by
  simp [mix, selected, Fin.sum_univ_succ, add_assoc]

def quadA {k : ℕ} (hk : 0 < k) (a r : ℕ) (i : Fin k) (t : Fin 3) : W k →ₗ[F] F :=
  scalarAt (firstLinear hk a r) (ix hk ((selected hk a i t).val+1))

def quadB {k : ℕ} (hk : 0 < k) (a r : ℕ) (i : Fin k) (t : Fin 3) : W k →ₗ[F] F :=
  scalarAt (firstLinear hk a r) (ix hk ((selected hk a i t).val+2))

def mixedLinear {k : ℕ} (hk : 0 < k) (a r : ℕ) (E : W k →ₗ[F] W k)
    (u : W k) (i : Fin k) : W k →ₗ[F] F := ∑ t, remLinear hk a r E u (selected hk a i t)

def mixedConstant {k : ℕ} (hk : 0 < k) (a : ℕ) (u c : W k) (i : Fin k) : F :=
  ∑ t, remConstant hk a u c (selected hk a i t)

theorem mixed_inner {k : ℕ} (hk : 0 < k) (a r : ℕ) (E : W k →ₗ[F] W k)
    (u c w : W k) (i : Fin k) :
    mix hk a (inner hk a r E u c w) i =
      quadratic (quadA hk a r i) (quadB hk a r i) w +
        (mixedLinear hk a r E u i w + mixedConstant hk a u c i) := by
  rw [mix_sum]
  simp_rw [inner_identity]
  simp only [quadratic, quadA, quadB, mixedLinear, mixedConstant,
    LinearMap.sum_apply, Finset.sum_add_distrib]

def outer {k : ℕ} (hk : 0 < k) (a r : ℕ) (E G : W k →ₗ[F] W k)
    (u c d : W k) (w : W k) : W k := step hk (mix hk a (inner hk a r E u c w))+G w+d

def rawQuartic {k : ℕ} (hk : 0 < k) (a r : ℕ) (i : Fin k) (w : W k) : F :=
  quadratic (quadA hk a r (ix hk (i.val+1))) (quadB hk a r (ix hk (i.val+1))) w *
    quadratic (quadA hk a r (ix hk (i.val+2))) (quadB hk a r (ix hk (i.val+2))) w

theorem raw_remainder_cubic {k : ℕ} (hk : 0 < k) (a r : ℕ) (E G : W k →ₗ[F] W k)
    (u c d : W k) (i : Fin k) :
    DegreeThree (fun w => outer hk a r E G u c d w i - rawQuartic hk a r i w) := by
  have h := two_layer_remainder_cubic
    (quadA hk a r i) (quadB hk a r i)
    (quadA hk a r (ix hk (i.val+1))) (quadB hk a r (ix hk (i.val+1)))
    (quadA hk a r (ix hk (i.val+2))) (quadB hk a r (ix hk (i.val+2)))
    (mixedLinear hk a r E u i)
    (mixedLinear hk a r E u (ix hk (i.val+1)))
    (mixedLinear hk a r E u (ix hk (i.val+2))) (scalarAt G i)
    (mixedConstant hk a u c i) (mixedConstant hk a u c (ix hk (i.val+1)))
    (mixedConstant hk a u c (ix hk (i.val+2))) (d i)
  convert h using 1
  funext w
  simp only [outer, Pi.add_apply, step, mixed_inner, rawQuartic, scalarAt,
    LinearMap.coe_mk, AddHom.coe_mk]
  ring

end PrivateTask346RawDegree

namespace PrivateTask346RowQuartic
open PrivateTask346AffineCubic PrivateTask346CubicClosure PrivateTask346AffineProducts

def rawTop (x : Fin 7 → F) : F := ((x 1 + x 2 + x 0)*(x 2 + x 3 + x 1) + (x 2 + x 3 + x 1)*(x 3 + x 4 + x 2) + (x 3 + x 4 + x 2)*(x 4 + x 5 + x 3))*((x 2 + x 3 + x 1)*(x 3 + x 4 + x 2) + (x 3 + x 4 + x 2)*(x 4 + x 5 + x 3) + (x 4 + x 5 + x 3)*(x 5 + x 6 + x 4))
def highPart (x : Fin 7 → F) : F := (x 0*x 1*x 2*x 3 + x 0*x 1*x 2*x 4 + x 0*x 1*x 2*x 5 + x 0*x 1*x 3*x 4 + x 0*x 1*x 3*x 6 + x 0*x 1*x 4*x 5 + x 0*x 1*x 4*x 6 + x 0*x 1*x 5*x 6 + x 0*x 2*x 3*x 5 + x 0*x 2*x 3*x 6 + x 0*x 2*x 4*x 5 + x 0*x 2*x 4*x 6 + x 0*x 2*x 5*x 6 + x 0*x 3*x 4*x 5 + x 0*x 3*x 4*x 6 + x 0*x 3*x 5*x 6 + x 1*x 2*x 3*x 6 + x 1*x 2*x 4*x 6 + x 1*x 2*x 5*x 6 + x 1*x 3*x 4*x 6 + x 1*x 4*x 5*x 6 + x 2*x 3*x 5*x 6 + x 2*x 4*x 5*x 6 + x 3*x 4*x 5*x 6)
def lowPart (x : Fin 7 → F) : F := (x 0*x 2 + x 1*x 3 + x 1*x 4 + x 1*x 5 + x 2*x 4 + x 2*x 5 + x 3*x 5 + x 4*x 6 + x 0*x 1*x 2 + x 0*x 1*x 4 + x 0*x 1*x 5 + x 0*x 2*x 3 + x 0*x 3*x 5 + x 0*x 3*x 6 + x 1*x 2*x 3 + x 1*x 3*x 5 + x 1*x 3*x 6 + x 1*x 5*x 6 + x 2*x 3*x 4 + x 2*x 5*x 6 + x 3*x 4*x 5 + x 3*x 4*x 6 + x 4*x 5*x 6)

lemma pow2 (x : F) : x^2=x := by rw [pow_two, square]
lemma pow3 (x : F) : x^3=x := by rw [pow_succ, pow2, square]
lemma pow4 (x : F) : x^4=x := by rw [pow_succ, pow3, square]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem scalar_identity (x : Fin 7 → F) : rawTop x = highPart x + lowPart x := by
  have : CharP F 2 := inferInstance
  unfold rawTop highPart lowPart
  ring_nf
  simp only [pow2, pow3, pow4]
  ring_nf
  reduce_mod_char! <;> ring

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem low_cubic (L : Fin 7 → V →ₗ[F] F) :
    DegreeThree (fun x => lowPart (fun i => L i x)) := by
  have h0 := cubic_affine_triple ![L 0, L 2, 0] ![0, 0, 1]
  have p0 : DegreeThree (fun x => L 0 x *L 2 x) := by
    simpa using h0
  have h1 := cubic_affine_triple ![L 1, L 3, 0] ![0, 0, 1]
  have p1 : DegreeThree (fun x => L 1 x *L 3 x) := by
    simpa using h1
  have h2 := cubic_affine_triple ![L 1, L 4, 0] ![0, 0, 1]
  have p2 : DegreeThree (fun x => L 1 x *L 4 x) := by
    simpa using h2
  have h3 := cubic_affine_triple ![L 1, L 5, 0] ![0, 0, 1]
  have p3 : DegreeThree (fun x => L 1 x *L 5 x) := by
    simpa using h3
  have h4 := cubic_affine_triple ![L 2, L 4, 0] ![0, 0, 1]
  have p4 : DegreeThree (fun x => L 2 x *L 4 x) := by
    simpa using h4
  have h5 := cubic_affine_triple ![L 2, L 5, 0] ![0, 0, 1]
  have p5 : DegreeThree (fun x => L 2 x *L 5 x) := by
    simpa using h5
  have h6 := cubic_affine_triple ![L 3, L 5, 0] ![0, 0, 1]
  have p6 : DegreeThree (fun x => L 3 x *L 5 x) := by
    simpa using h6
  have h7 := cubic_affine_triple ![L 4, L 6, 0] ![0, 0, 1]
  have p7 : DegreeThree (fun x => L 4 x *L 6 x) := by
    simpa using h7
  have h8 := cubic_affine_triple ![L 0, L 1, L 2] ![0, 0, 0]
  have p8 : DegreeThree (fun x => L 0 x *L 1 x *L 2 x) := by
    simpa using h8
  have h9 := cubic_affine_triple ![L 0, L 1, L 4] ![0, 0, 0]
  have p9 : DegreeThree (fun x => L 0 x *L 1 x *L 4 x) := by
    simpa using h9
  have h10 := cubic_affine_triple ![L 0, L 1, L 5] ![0, 0, 0]
  have p10 : DegreeThree (fun x => L 0 x *L 1 x *L 5 x) := by
    simpa using h10
  have h11 := cubic_affine_triple ![L 0, L 2, L 3] ![0, 0, 0]
  have p11 : DegreeThree (fun x => L 0 x *L 2 x *L 3 x) := by
    simpa using h11
  have h12 := cubic_affine_triple ![L 0, L 3, L 5] ![0, 0, 0]
  have p12 : DegreeThree (fun x => L 0 x *L 3 x *L 5 x) := by
    simpa using h12
  have h13 := cubic_affine_triple ![L 0, L 3, L 6] ![0, 0, 0]
  have p13 : DegreeThree (fun x => L 0 x *L 3 x *L 6 x) := by
    simpa using h13
  have h14 := cubic_affine_triple ![L 1, L 2, L 3] ![0, 0, 0]
  have p14 : DegreeThree (fun x => L 1 x *L 2 x *L 3 x) := by
    simpa using h14
  have h15 := cubic_affine_triple ![L 1, L 3, L 5] ![0, 0, 0]
  have p15 : DegreeThree (fun x => L 1 x *L 3 x *L 5 x) := by
    simpa using h15
  have h16 := cubic_affine_triple ![L 1, L 3, L 6] ![0, 0, 0]
  have p16 : DegreeThree (fun x => L 1 x *L 3 x *L 6 x) := by
    simpa using h16
  have h17 := cubic_affine_triple ![L 1, L 5, L 6] ![0, 0, 0]
  have p17 : DegreeThree (fun x => L 1 x *L 5 x *L 6 x) := by
    simpa using h17
  have h18 := cubic_affine_triple ![L 2, L 3, L 4] ![0, 0, 0]
  have p18 : DegreeThree (fun x => L 2 x *L 3 x *L 4 x) := by
    simpa using h18
  have h19 := cubic_affine_triple ![L 2, L 5, L 6] ![0, 0, 0]
  have p19 : DegreeThree (fun x => L 2 x *L 5 x *L 6 x) := by
    simpa using h19
  have h20 := cubic_affine_triple ![L 3, L 4, L 5] ![0, 0, 0]
  have p20 : DegreeThree (fun x => L 3 x *L 4 x *L 5 x) := by
    simpa using h20
  have h21 := cubic_affine_triple ![L 3, L 4, L 6] ![0, 0, 0]
  have p21 : DegreeThree (fun x => L 3 x *L 4 x *L 6 x) := by
    simpa using h21
  have h22 := cubic_affine_triple ![L 4, L 5, L 6] ![0, 0, 0]
  have p22 : DegreeThree (fun x => L 4 x *L 5 x *L 6 x) := by
    simpa using h22
  exact (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ p0 p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) p20) p21) p22)

theorem quartic_remainder_cubic (L : Fin 7 → V →ₗ[F] F) :
    DegreeThree (fun x => rawTop (fun i => L i x) - highPart (fun i => L i x)) := by
  have he : (fun x => rawTop (fun i => L i x) - highPart (fun i => L i x)) =
      (fun x => lowPart (fun i => L i x)) := by
    funext x
    rw [scalar_identity]
    ring
  rw [he]
  exact low_cubic L

end PrivateTask346RowQuartic

namespace PrivateTask346ColumnQuartic
open PrivateTask346AffineCubic PrivateTask346CubicClosure PrivateTask346AffineProducts

def rawTop (x : Fin 11 → F) : F := ((x 2 + x 4 + x 0)*(x 3 + x 5 + x 1) + (x 4 + x 6 + x 2)*(x 5 + x 7 + x 3) + (x 6 + x 8 + x 4)*(x 7 + x 9 + x 5))*((x 3 + x 5 + x 1)*(x 4 + x 6 + x 2) + (x 5 + x 7 + x 3)*(x 6 + x 8 + x 4) + (x 7 + x 9 + x 5)*(x 8 + x 10 + x 6))
def highPart (x : Fin 11 → F) : F := (x 0*x 1*x 3*x 4 + x 0*x 1*x 3*x 6 + x 0*x 1*x 3*x 8 + x 0*x 1*x 4*x 5 + x 0*x 1*x 4*x 7 + x 0*x 1*x 5*x 10 + x 0*x 1*x 6*x 9 + x 0*x 1*x 7*x 10 + x 0*x 1*x 8*x 9 + x 0*x 1*x 9*x 10 + x 0*x 3*x 4*x 7 + x 0*x 3*x 5*x 6 + x 0*x 3*x 5*x 8 + x 0*x 3*x 5*x 10 + x 0*x 3*x 6*x 9 + x 0*x 3*x 7*x 10 + x 0*x 3*x 8*x 9 + x 0*x 3*x 9*x 10 + x 0*x 4*x 5*x 7 + x 0*x 5*x 6*x 9 + x 0*x 5*x 7*x 10 + x 0*x 5*x 8*x 9 + x 0*x 5*x 9*x 10 + x 1*x 2*x 3*x 4 + x 1*x 2*x 3*x 6 + x 1*x 2*x 3*x 8 + x 1*x 2*x 4*x 9 + x 1*x 2*x 5*x 6 + x 1*x 2*x 5*x 8 + x 1*x 2*x 5*x 10 + x 1*x 2*x 6*x 7 + x 1*x 2*x 7*x 8 + x 1*x 2*x 7*x 10 + x 1*x 2*x 9*x 10 + x 1*x 3*x 4*x 6 + x 1*x 3*x 4*x 8 + x 1*x 4*x 5*x 8 + x 1*x 4*x 5*x 10 + x 1*x 4*x 6*x 9 + x 1*x 4*x 7*x 8 + x 1*x 4*x 7*x 10 + x 1*x 4*x 9*x 10 + x 1*x 5*x 6*x 8 + x 1*x 6*x 7*x 8 + x 1*x 6*x 8*x 9 + x 2*x 3*x 4*x 5 + x 2*x 3*x 4*x 9 + x 2*x 3*x 5*x 6 + x 2*x 3*x 5*x 8 + x 2*x 3*x 6*x 9 + x 2*x 3*x 8*x 9 + x 2*x 4*x 5*x 9 + x 2*x 5*x 6*x 7 + x 2*x 5*x 6*x 9 + x 2*x 5*x 7*x 8 + x 2*x 5*x 7*x 10 + x 2*x 5*x 8*x 9 + x 2*x 6*x 7*x 9 + x 2*x 7*x 8*x 9 + x 2*x 7*x 9*x 10 + x 3*x 4*x 5*x 8 + x 3*x 4*x 6*x 7 + x 3*x 4*x 8*x 9 + x 3*x 5*x 6*x 10 + x 3*x 6*x 7*x 10 + x 3*x 6*x 9*x 10 + x 4*x 5*x 7*x 8 + x 4*x 5*x 7*x 10 + x 4*x 5*x 8*x 9 + x 4*x 6*x 7*x 9 + x 4*x 7*x 8*x 9 + x 4*x 7*x 9*x 10 + x 5*x 6*x 7*x 8 + x 5*x 6*x 9*x 10 + x 6*x 7*x 8*x 9 + x 6*x 7*x 9*x 10)
def lowPart (x : Fin 11 → F) : F := (x 1*x 2 + x 1*x 4 + x 6*x 9 + x 8*x 9 + x 0*x 1*x 2 + x 0*x 1*x 4 + x 0*x 1*x 6 + x 0*x 2*x 3 + x 0*x 2*x 5 + x 0*x 3*x 8 + x 0*x 5*x 6 + x 0*x 5*x 10 + x 1*x 2*x 3 + x 1*x 2*x 5 + x 1*x 2*x 6 + x 1*x 2*x 7 + x 1*x 3*x 6 + x 1*x 4*x 5 + x 1*x 4*x 6 + x 1*x 4*x 7 + x 1*x 4*x 9 + x 1*x 6*x 9 + x 2*x 3*x 6 + x 2*x 3*x 7 + x 2*x 4*x 5 + x 2*x 4*x 7 + x 2*x 5*x 7 + x 2*x 5*x 8 + x 2*x 7*x 10 + x 3*x 5*x 6 + x 3*x 5*x 8 + x 3*x 6*x 8 + x 3*x 6*x 9 + x 3*x 7*x 8 + x 3*x 8*x 9 + x 4*x 5*x 6 + x 4*x 5*x 7 + x 4*x 5*x 10 + x 4*x 6*x 9 + x 4*x 7*x 8 + x 4*x 7*x 9 + x 4*x 8*x 9 + x 4*x 9*x 10 + x 5*x 6*x 8 + x 5*x 6*x 9 + x 5*x 8*x 9 + x 5*x 8*x 10 + x 6*x 9*x 10 + x 7*x 8*x 9 + x 7*x 8*x 10 + x 8*x 9*x 10)

lemma pow2 (x : F) : x^2=x := by rw [pow_two, square]
lemma pow3 (x : F) : x^3=x := by rw [pow_succ, pow2, square]
lemma pow4 (x : F) : x^4=x := by rw [pow_succ, pow3, square]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem scalar_identity (x : Fin 11 → F) : rawTop x = highPart x + lowPart x := by
  have : CharP F 2 := inferInstance
  unfold rawTop highPart lowPart
  ring_nf
  simp only [pow2, pow3, pow4]
  ring_nf
  reduce_mod_char! <;> ring

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem low_cubic (L : Fin 11 → V →ₗ[F] F) :
    DegreeThree (fun x => lowPart (fun i => L i x)) := by
  have h0 := cubic_affine_triple ![L 1, L 2, 0] ![0, 0, 1]
  have p0 : DegreeThree (fun x => L 1 x *L 2 x) := by
    simpa using h0
  have h1 := cubic_affine_triple ![L 1, L 4, 0] ![0, 0, 1]
  have p1 : DegreeThree (fun x => L 1 x *L 4 x) := by
    simpa using h1
  have h2 := cubic_affine_triple ![L 6, L 9, 0] ![0, 0, 1]
  have p2 : DegreeThree (fun x => L 6 x *L 9 x) := by
    simpa using h2
  have h3 := cubic_affine_triple ![L 8, L 9, 0] ![0, 0, 1]
  have p3 : DegreeThree (fun x => L 8 x *L 9 x) := by
    simpa using h3
  have h4 := cubic_affine_triple ![L 0, L 1, L 2] ![0, 0, 0]
  have p4 : DegreeThree (fun x => L 0 x *L 1 x *L 2 x) := by
    simpa using h4
  have h5 := cubic_affine_triple ![L 0, L 1, L 4] ![0, 0, 0]
  have p5 : DegreeThree (fun x => L 0 x *L 1 x *L 4 x) := by
    simpa using h5
  have h6 := cubic_affine_triple ![L 0, L 1, L 6] ![0, 0, 0]
  have p6 : DegreeThree (fun x => L 0 x *L 1 x *L 6 x) := by
    simpa using h6
  have h7 := cubic_affine_triple ![L 0, L 2, L 3] ![0, 0, 0]
  have p7 : DegreeThree (fun x => L 0 x *L 2 x *L 3 x) := by
    simpa using h7
  have h8 := cubic_affine_triple ![L 0, L 2, L 5] ![0, 0, 0]
  have p8 : DegreeThree (fun x => L 0 x *L 2 x *L 5 x) := by
    simpa using h8
  have h9 := cubic_affine_triple ![L 0, L 3, L 8] ![0, 0, 0]
  have p9 : DegreeThree (fun x => L 0 x *L 3 x *L 8 x) := by
    simpa using h9
  have h10 := cubic_affine_triple ![L 0, L 5, L 6] ![0, 0, 0]
  have p10 : DegreeThree (fun x => L 0 x *L 5 x *L 6 x) := by
    simpa using h10
  have h11 := cubic_affine_triple ![L 0, L 5, L 10] ![0, 0, 0]
  have p11 : DegreeThree (fun x => L 0 x *L 5 x *L 10 x) := by
    simpa using h11
  have h12 := cubic_affine_triple ![L 1, L 2, L 3] ![0, 0, 0]
  have p12 : DegreeThree (fun x => L 1 x *L 2 x *L 3 x) := by
    simpa using h12
  have h13 := cubic_affine_triple ![L 1, L 2, L 5] ![0, 0, 0]
  have p13 : DegreeThree (fun x => L 1 x *L 2 x *L 5 x) := by
    simpa using h13
  have h14 := cubic_affine_triple ![L 1, L 2, L 6] ![0, 0, 0]
  have p14 : DegreeThree (fun x => L 1 x *L 2 x *L 6 x) := by
    simpa using h14
  have h15 := cubic_affine_triple ![L 1, L 2, L 7] ![0, 0, 0]
  have p15 : DegreeThree (fun x => L 1 x *L 2 x *L 7 x) := by
    simpa using h15
  have h16 := cubic_affine_triple ![L 1, L 3, L 6] ![0, 0, 0]
  have p16 : DegreeThree (fun x => L 1 x *L 3 x *L 6 x) := by
    simpa using h16
  have h17 := cubic_affine_triple ![L 1, L 4, L 5] ![0, 0, 0]
  have p17 : DegreeThree (fun x => L 1 x *L 4 x *L 5 x) := by
    simpa using h17
  have h18 := cubic_affine_triple ![L 1, L 4, L 6] ![0, 0, 0]
  have p18 : DegreeThree (fun x => L 1 x *L 4 x *L 6 x) := by
    simpa using h18
  have h19 := cubic_affine_triple ![L 1, L 4, L 7] ![0, 0, 0]
  have p19 : DegreeThree (fun x => L 1 x *L 4 x *L 7 x) := by
    simpa using h19
  have h20 := cubic_affine_triple ![L 1, L 4, L 9] ![0, 0, 0]
  have p20 : DegreeThree (fun x => L 1 x *L 4 x *L 9 x) := by
    simpa using h20
  have h21 := cubic_affine_triple ![L 1, L 6, L 9] ![0, 0, 0]
  have p21 : DegreeThree (fun x => L 1 x *L 6 x *L 9 x) := by
    simpa using h21
  have h22 := cubic_affine_triple ![L 2, L 3, L 6] ![0, 0, 0]
  have p22 : DegreeThree (fun x => L 2 x *L 3 x *L 6 x) := by
    simpa using h22
  have h23 := cubic_affine_triple ![L 2, L 3, L 7] ![0, 0, 0]
  have p23 : DegreeThree (fun x => L 2 x *L 3 x *L 7 x) := by
    simpa using h23
  have h24 := cubic_affine_triple ![L 2, L 4, L 5] ![0, 0, 0]
  have p24 : DegreeThree (fun x => L 2 x *L 4 x *L 5 x) := by
    simpa using h24
  have h25 := cubic_affine_triple ![L 2, L 4, L 7] ![0, 0, 0]
  have p25 : DegreeThree (fun x => L 2 x *L 4 x *L 7 x) := by
    simpa using h25
  have h26 := cubic_affine_triple ![L 2, L 5, L 7] ![0, 0, 0]
  have p26 : DegreeThree (fun x => L 2 x *L 5 x *L 7 x) := by
    simpa using h26
  have h27 := cubic_affine_triple ![L 2, L 5, L 8] ![0, 0, 0]
  have p27 : DegreeThree (fun x => L 2 x *L 5 x *L 8 x) := by
    simpa using h27
  have h28 := cubic_affine_triple ![L 2, L 7, L 10] ![0, 0, 0]
  have p28 : DegreeThree (fun x => L 2 x *L 7 x *L 10 x) := by
    simpa using h28
  have h29 := cubic_affine_triple ![L 3, L 5, L 6] ![0, 0, 0]
  have p29 : DegreeThree (fun x => L 3 x *L 5 x *L 6 x) := by
    simpa using h29
  have h30 := cubic_affine_triple ![L 3, L 5, L 8] ![0, 0, 0]
  have p30 : DegreeThree (fun x => L 3 x *L 5 x *L 8 x) := by
    simpa using h30
  have h31 := cubic_affine_triple ![L 3, L 6, L 8] ![0, 0, 0]
  have p31 : DegreeThree (fun x => L 3 x *L 6 x *L 8 x) := by
    simpa using h31
  have h32 := cubic_affine_triple ![L 3, L 6, L 9] ![0, 0, 0]
  have p32 : DegreeThree (fun x => L 3 x *L 6 x *L 9 x) := by
    simpa using h32
  have h33 := cubic_affine_triple ![L 3, L 7, L 8] ![0, 0, 0]
  have p33 : DegreeThree (fun x => L 3 x *L 7 x *L 8 x) := by
    simpa using h33
  have h34 := cubic_affine_triple ![L 3, L 8, L 9] ![0, 0, 0]
  have p34 : DegreeThree (fun x => L 3 x *L 8 x *L 9 x) := by
    simpa using h34
  have h35 := cubic_affine_triple ![L 4, L 5, L 6] ![0, 0, 0]
  have p35 : DegreeThree (fun x => L 4 x *L 5 x *L 6 x) := by
    simpa using h35
  have h36 := cubic_affine_triple ![L 4, L 5, L 7] ![0, 0, 0]
  have p36 : DegreeThree (fun x => L 4 x *L 5 x *L 7 x) := by
    simpa using h36
  have h37 := cubic_affine_triple ![L 4, L 5, L 10] ![0, 0, 0]
  have p37 : DegreeThree (fun x => L 4 x *L 5 x *L 10 x) := by
    simpa using h37
  have h38 := cubic_affine_triple ![L 4, L 6, L 9] ![0, 0, 0]
  have p38 : DegreeThree (fun x => L 4 x *L 6 x *L 9 x) := by
    simpa using h38
  have h39 := cubic_affine_triple ![L 4, L 7, L 8] ![0, 0, 0]
  have p39 : DegreeThree (fun x => L 4 x *L 7 x *L 8 x) := by
    simpa using h39
  have h40 := cubic_affine_triple ![L 4, L 7, L 9] ![0, 0, 0]
  have p40 : DegreeThree (fun x => L 4 x *L 7 x *L 9 x) := by
    simpa using h40
  have h41 := cubic_affine_triple ![L 4, L 8, L 9] ![0, 0, 0]
  have p41 : DegreeThree (fun x => L 4 x *L 8 x *L 9 x) := by
    simpa using h41
  have h42 := cubic_affine_triple ![L 4, L 9, L 10] ![0, 0, 0]
  have p42 : DegreeThree (fun x => L 4 x *L 9 x *L 10 x) := by
    simpa using h42
  have h43 := cubic_affine_triple ![L 5, L 6, L 8] ![0, 0, 0]
  have p43 : DegreeThree (fun x => L 5 x *L 6 x *L 8 x) := by
    simpa using h43
  have h44 := cubic_affine_triple ![L 5, L 6, L 9] ![0, 0, 0]
  have p44 : DegreeThree (fun x => L 5 x *L 6 x *L 9 x) := by
    simpa using h44
  have h45 := cubic_affine_triple ![L 5, L 8, L 9] ![0, 0, 0]
  have p45 : DegreeThree (fun x => L 5 x *L 8 x *L 9 x) := by
    simpa using h45
  have h46 := cubic_affine_triple ![L 5, L 8, L 10] ![0, 0, 0]
  have p46 : DegreeThree (fun x => L 5 x *L 8 x *L 10 x) := by
    simpa using h46
  have h47 := cubic_affine_triple ![L 6, L 9, L 10] ![0, 0, 0]
  have p47 : DegreeThree (fun x => L 6 x *L 9 x *L 10 x) := by
    simpa using h47
  have h48 := cubic_affine_triple ![L 7, L 8, L 9] ![0, 0, 0]
  have p48 : DegreeThree (fun x => L 7 x *L 8 x *L 9 x) := by
    simpa using h48
  have h49 := cubic_affine_triple ![L 7, L 8, L 10] ![0, 0, 0]
  have p49 : DegreeThree (fun x => L 7 x *L 8 x *L 10 x) := by
    simpa using h49
  have h50 := cubic_affine_triple ![L 8, L 9, L 10] ![0, 0, 0]
  have p50 : DegreeThree (fun x => L 8 x *L 9 x *L 10 x) := by
    simpa using h50
  exact (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ (cubic_add _ _ p0 p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) p20) p21) p22) p23) p24) p25) p26) p27) p28) p29) p30) p31) p32) p33) p34) p35) p36) p37) p38) p39) p40) p41) p42) p43) p44) p45) p46) p47) p48) p49) p50)

theorem quartic_remainder_cubic (L : Fin 11 → V →ₗ[F] F) :
    DegreeThree (fun x => rawTop (fun i => L i x) - highPart (fun i => L i x)) := by
  have he : (fun x => rawTop (fun i => L i x) - highPart (fun i => L i x)) =
      (fun x => lowPart (fun i => L i x)) := by
    funext x
    rw [scalar_identity]
    ring
  rw [he]
  exact low_cubic L

end PrivateTask346ColumnQuartic

namespace PrivateTask346RawWindows
open PrivateTask346AffineCubic PrivateTask346RawDegree PrivateTask346QuadraticLayers
open scoped Fin.NatCast

variable {k : ℕ} [NeZero k]

lemma ix_plus (hk : 0 < k) (i : Fin k) (a : ℕ) :
    ix hk (i.val+a) = i + (a : Fin k) := by
  apply Fin.ext
  simp [ix, Fin.val_add, Fin.val_natCast, Nat.add_mod]

lemma ix_back (hk : 0 < k) (i : Fin k) (a : ℕ) :
    ix hk (i.val+k-a%k) = i - (a : Fin k) := by
  apply Fin.ext
  change (i.val+k-a%k)%k = ((k-a%k)+i.val)%k
  congr 1
  have hm := Nat.mod_lt a hk
  omega

lemma first_apply (hk : 0 < k) (a r : ℕ) (w : W k) (i : Fin k) :
    firstLinear hk a r w i =
      w (i-(r : Fin k)) + w (i+(a : Fin k)-(r : Fin k)) +
        w (i-(a : Fin k)-(r : Fin k)) := by
  simp only [firstLinear, LinearMap.comp_apply, mix, rot, LinearMap.coe_mk, AddHom.coe_mk,
    ix_plus, ix_back]

lemma nat_smul (n : ℕ) : (n : Fin k) = n • (1 : Fin k) := (nsmul_one n).symm
lemma fin2 : (2 : Fin k) = 2 • (1 : Fin k) := nat_smul 2
lemma fin3 : (3 : Fin k) = 3 • (1 : Fin k) := nat_smul 3
lemma fin4 : (4 : Fin k) = 4 • (1 : Fin k) := nat_smul 4
lemma fin5 : (5 : Fin k) = 5 • (1 : Fin k) := nat_smul 5
lemma fin6 : (6 : Fin k) = 6 • (1 : Fin k) := nat_smul 6
lemma fin7 : (7 : Fin k) = 7 • (1 : Fin k) := nat_smul 7
lemma fin8 : (8 : Fin k) = 8 • (1 : Fin k) := nat_smul 8
lemma fin9 : (9 : Fin k) = 9 • (1 : Fin k) := nat_smul 9
lemma fin10 : (10 : Fin k) = 10 • (1 : Fin k) := nat_smul 10

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem row_window (hk : 0 < k) (w : W k) (i : Fin k) :
    rawQuartic hk 1 1 i w =
      PrivateTask346RowQuartic.rawTop (fun t : Fin 7 => w (i-1+(t.val : Fin k))) := by
  norm_num [rawQuartic, quadratic, quadA, quadB, scalarAt, selected, Fin.sum_univ_succ,
    ix_plus, ix_back, first_apply, PrivateTask346RowQuartic.rawTop]
  simp only [fin2, fin3, fin4, fin5, fin6]
  abel_nf
  simp only [← add_zsmul]
  norm_num
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem column_window (hk : 0 < k) (w : W k) (i : Fin k) :
    rawQuartic hk 2 3 i w =
      PrivateTask346ColumnQuartic.rawTop (fun t : Fin 11 => w (i-5+(t.val : Fin k))) := by
  norm_num [rawQuartic, quadratic, quadA, quadB, scalarAt, selected, Fin.sum_univ_succ,
    ix_plus, ix_back, first_apply, PrivateTask346ColumnQuartic.rawTop]
  simp only [fin2, fin3, fin4, fin5, fin6, fin7, fin8, fin9, fin10]
  abel_nf
  simp only [← add_zsmul]
  norm_num
  ring

end PrivateTask346RawWindows

namespace PrivateTask346SeparatedLocations

lemma mod_three (k n : ℕ) (hk : 0 < k) (hn : n < 3*k) :
    n = n%k ∨ n = n%k+k ∨ n = n%k+2*k := by
  have hq : n/k < 3 := (Nat.div_lt_iff_lt_mul hk).mpr (by omega)
  have he := Nat.mod_add_div n k
  interval_cases h : n/k <;> simp_all <;> omega

set_option maxHeartbeats 1200000 in
lemma cross_disjoint (k p q a b : ℕ) (hk : 21 ≤ k) (hp : p < k) (hq : q < k)
    (ha : a ≤ 10) (hb : b ≤ 10)
    (hd : 21 ≤ (q+k-p)%k) (hr : 21 ≤ (p+k-q)%k) :
    (p+k-5+a)%k ≠ (q+k-5+b)%k := by
  intro he
  have h1 := mod_three k (p+k-5+a) (by omega) (by omega)
  have h2 := mod_three k (q+k-5+b) (by omega) (by omega)
  have h3 := mod_three k (q+k-p) (by omega) (by omega)
  have h4 := mod_three k (p+k-q) (by omega) (by omega)
  have hm1 : (p+k-5+a)%k < k := Nat.mod_lt _ (by omega)
  have hm2 : (q+k-5+b)%k < k := Nat.mod_lt _ (by omega)
  have hm3 : (q+k-p)%k < k := Nat.mod_lt _ (by omega)
  have hm4 : (p+k-q)%k < k := Nat.mod_lt _ (by omega)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;> omega

lemma same_offset (k p a b : ℕ) (hk : 21 ≤ k) (hp : p < k) (ha : a ≤ 10) (hb : b ≤ 10)
    (he : (p+k-5+a)%k = (p+k-5+b)%k) : a = b := by
  have h1 := mod_three k (p+k-5+a) (by omega) (by omega)
  have h2 := mod_three k (p+k-5+b) (by omega) (by omega)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> omega

def offset (a : Fin 4) : ℕ := if a.val = 0 then 0 else if a.val = 1 then 1 else if a.val = 2 then 9 else 10
lemma offset_le : ∀ a : Fin 4, offset a ≤ 10 := by decide +kernel
lemma offset_injective : Function.Injective offset := by decide +kernel

def loc {k s : ℕ} (hk : 0 < k) (pick : Fin s → Fin k) (i : Fin s) (a : Fin 4) : Fin k :=
  ⟨((pick i).val+k-5+offset a)%k,Nat.mod_lt _ hk⟩

theorem loc_injective {k s : ℕ} (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k) :
    Function.Injective (fun p : Fin s × Fin 4 => loc hk pick p.1 p.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  have hv := congrArg Fin.val he
  change ((pick i).val+k-5+offset a)%k = ((pick j).val+k-5+offset b)%k at hv
  by_cases hij : i = j
  · subst j
    have ho := same_offset k (pick i).val (offset a) (offset b) h21 (pick i).isLt (offset_le a) (offset_le b) hv
    have hab := offset_injective ho
    subst b
    rfl
  · exact (cross_disjoint k (pick i).val (pick j).val (offset a) (offset b) h21
      (pick i).isLt (pick j).isLt (offset_le a) (offset_le b)
      (sep i j hij) (sep j i (Ne.symm hij)) hv).elim

end PrivateTask346SeparatedLocations

namespace PrivateTask346FaceSpace
open PrivateTask346CubicClosure (Blocks)
open PrivateTask346AffineCubic (DegreeThree)

abbrev F := ZMod 2
abbrev Raw (k : ℕ) := Fin k → F

def insertFn {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (z : Blocks s) (j : Fin k) : F :=
  ∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z i a else 0

def insertLinear {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) : Blocks s →ₗ[F] Raw k where
  toFun := insertFn ell
  map_add' := by
    intro z z'
    funext j
    change (∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z i a+z' i a else 0) =
      (∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z i a else 0) +
      (∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z' i a else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  map_smul' := by
    intro r z
    funext j
    change (∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then r*z i a else 0) =
      r * (∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z i a else 0)
    simp only [Finset.mul_sum,mul_ite,mul_zero]

def sampleLinear {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) : Raw k →ₗ[F] Blocks s where
  toFun := fun w i a => w (ell (i,a))
  map_add' := by intro z z'; rfl
  map_smul' := by intro r z; rfl

theorem sample_insert {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (z : Blocks s) : sampleLinear ell (insertLinear ell z) = z := by
  funext i a
  change (∑ i' : Fin s, ∑ a' : Fin 4, if ell (i',a') = ell (i,a) then z i' a' else 0) = z i a
  have hh (i' : Fin s) (a' : Fin 4) : ell (i',a') = ell (i,a) ↔ i'=i ∧ a'=a := by
    constructor
    · intro h
      exact Prod.mk.inj (he h)
    · rintro ⟨rfl,rfl⟩
      rfl
  simp_rw [hh]
  simp [ite_and]

def face {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (base : Raw k) (z : Blocks s) : Raw k :=
  fun j => base j + ∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z i a else 0

lemma face_eq {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (base : Raw k) (z : Blocks s) :
    face ell base z = insertLinear ell z + base := by
  funext j
  change base j + insertFn ell z j = insertFn ell z j + base j
  exact add_comm _ _

theorem cubic_lift_face {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (base : Raw k) (q : Blocks s → F) (hq : DegreeThree q) :
    ∃ p : Raw k → F, DegreeThree p ∧ ∀ z : Blocks s, p (face ell base z) = q z := by
  obtain ⟨p,hp,hpface⟩ := PrivateTask346AffineCubic.cubic_lift (sampleLinear ell) (insertLinear ell)
    (sample_insert ell he) base q hq
  exact ⟨p,hp,fun z => by rw [face_eq]; exact hpface z⟩

theorem question_lift_face {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (base : Raw k) (a : Blocks s →ₗ[F] F) :
    ∃ b : Raw k →ₗ[F] F, ∀ z : Blocks s, b (face ell base z) = a z + a (sampleLinear ell base) := by
  obtain ⟨b,hb⟩ := PrivateTask346AffineCubic.question_lift (sampleLinear ell) (insertLinear ell)
    (sample_insert ell he) base a
  exact ⟨b,fun z => by rw [face_eq]; exact hb z⟩

abbrev NormalBase {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) := {w : Raw k // sampleLinear ell w = 0}

def faceEquiv {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell) :
    Raw k ≃ NormalBase ell × Blocks s where
  toFun w := (⟨w-insertLinear ell (sampleLinear ell w),by simp only [map_sub,sample_insert ell he,sub_self]⟩,
    sampleLinear ell w)
  invFun p := insertLinear ell p.2+p.1.1
  left_inv := by intro w; change insertLinear ell (sampleLinear ell w)+(w-insertLinear ell (sampleLinear ell w))=w; abel
  right_inv := by
    rintro ⟨⟨b,hb⟩,z⟩
    apply Prod.ext
    · apply Subtype.ext
      change (insertLinear ell z+b)-insertLinear ell (sampleLinear ell (insertLinear ell z+b))=b
      simp only [map_add,sample_insert ell he,hb,add_zero]
      abel
    · change sampleLinear ell (insertLinear ell z+b)=z
      simp only [map_add,sample_insert ell he,hb,add_zero]

lemma raw_card (k : ℕ) : Nat.card (Raw k) = 2^k := by
  rw [Nat.card_eq_fintype_card]
  simp [Raw,Fintype.card_fun]

lemma blocks_card (s : ℕ) : Nat.card (Blocks s) = 16^s := by
  rw [Nat.card_eq_fintype_card]
  simp [Blocks,PrivateTask346CubicClosure.Block,Fintype.card_fun]

theorem split_card {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell) :
    Nat.card (NormalBase ell) * 16^s = 2^k := by
  have h := Nat.card_congr (faceEquiv ell he)
  rw [Nat.card_prod,raw_card,blocks_card] at h
  exact h.symm

theorem coordinates_fit {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell) : 4*s ≤ k := by
  have h := Fintype.card_le_of_injective ell he
  simpa [Nat.mul_comm] using h

end PrivateTask346FaceSpace

namespace PrivateTask346LocalWindows
open PrivateTask346SeparatedLocations

set_option maxHeartbeats 2400000 in
theorem cross_far (k p q a b : ℕ) (hk : 21 ≤ k) (hp : p < k) (hq : q < k)
    (ha : a ≤ 10) (hb : b ≤ 10)
    (hd : 21 ≤ (q+k-p)%k) (hr : 21 ≤ (p+k-q)%k) :
    11 ≤ (((q+k-5+b)%k)+k-((p+k-5+a)%k))%k := by
  have h1 := mod_three k (p+k-5+a) (by omega) (by omega)
  have h2 := mod_three k (q+k-5+b) (by omega) (by omega)
  have h3 := mod_three k (q+k-p) (by omega) (by omega)
  have h4 := mod_three k (p+k-q) (by omega) (by omega)
  have hm1 : (p+k-5+a)%k < k := Nat.mod_lt _ (by omega)
  have hm2 : (q+k-5+b)%k < k := Nat.mod_lt _ (by omega)
  have hm3 : (q+k-p)%k < k := Nat.mod_lt _ (by omega)
  have hm4 : (p+k-q)%k < k := Nat.mod_lt _ (by omega)
  have h5 := mod_three k (((q+k-5+b)%k)+k-((p+k-5+a)%k)) (by omega) (by omega)
  have hm5 : (((q+k-5+b)%k)+k-((p+k-5+a)%k))%k < k := Nat.mod_lt _ (by omega)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;>
    rcases h5 with h5 | h5 | h5 <;> omega

set_option maxHeartbeats 1200000 in
theorem window_close (k j a b : ℕ) (hk : 21 ≤ k) (hj : j < k)
    (ha : a ≤ 10) (hb : b ≤ 10) :
    (((j+k-5+b)%k)+k-((j+k-5+a)%k))%k ≤ 10 ∨
      (((j+k-5+a)%k)+k-((j+k-5+b)%k))%k ≤ 10 := by
  have h1 := mod_three k (j+k-5+a) (by omega) (by omega)
  have h2 := mod_three k (j+k-5+b) (by omega) (by omega)
  have hm1 : (j+k-5+a)%k < k := Nat.mod_lt _ (by omega)
  have hm2 : (j+k-5+b)%k < k := Nat.mod_lt _ (by omega)
  have h3 := mod_three k (((j+k-5+b)%k)+k-((j+k-5+a)%k)) (by omega) (by omega)
  have h4 := mod_three k (((j+k-5+a)%k)+k-((j+k-5+b)%k)) (by omega) (by omega)
  have hm3 : (((j+k-5+b)%k)+k-((j+k-5+a)%k))%k < k := Nat.mod_lt _ (by omega)
  have hm4 : (((j+k-5+a)%k)+k-((j+k-5+b)%k))%k < k := Nat.mod_lt _ (by omega)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;> omega

set_option maxHeartbeats 1200000 in
theorem window_extremes (k p j a b : ℕ) (hk : 21 ≤ k) (hp : p < k) (hj : j < k)
    (ha : a ≤ 10) (hb : b ≤ 10)
    (he : (p+k-5)%k = (j+k-5+a)%k)
    (hf : (p+k-5+10)%k = (j+k-5+b)%k) : p = j ∧ a = 0 ∧ b = 10 := by
  have h1 := mod_three k (p+k-5) (by omega) (by omega)
  have h2 := mod_three k (p+k-5+10) (by omega) (by omega)
  have h3 := mod_three k (j+k-5+a) (by omega) (by omega)
  have h4 := mod_three k (j+k-5+b) (by omega) (by omega)
  have hm1 : (p+k-5)%k < k := Nat.mod_lt _ (by omega)
  have hm2 : (p+k-5+10)%k < k := Nat.mod_lt _ (by omega)
  have hm3 : (j+k-5+a)%k < k := Nat.mod_lt _ (by omega)
  have hm4 : (j+k-5+b)%k < k := Nat.mod_lt _ (by omega)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;> omega

theorem same_window_same_block {k s : ℕ} (hk : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (i j : Fin s) (a b : Fin 4) (center : Fin k) (u v : ℕ) (hu : u ≤ 10) (hv : v ≤ 10)
    (he : ((pick i).val+k-5+offset a)%k = (center.val+k-5+u)%k)
    (hf : ((pick j).val+k-5+offset b)%k = (center.val+k-5+v)%k) : i = j := by
  by_contra hne
  have h1 := cross_far k (pick i).val (pick j).val (offset a) (offset b) hk
    (pick i).isLt (pick j).isLt (offset_le a) (offset_le b) (sep i j hne) (sep j i (Ne.symm hne))
  have h2 := cross_far k (pick j).val (pick i).val (offset b) (offset a) hk
    (pick j).isLt (pick i).isLt (offset_le b) (offset_le a) (sep j i (Ne.symm hne)) (sep i j hne)
  rw [he, hf] at h1 h2
  have hc := window_close k center.val u v hk center.isLt hu hv
  omega

theorem quartet_window {k s : ℕ} (hk : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (center : Fin k) (T : Fin 4 → ℕ) (hT : ∀ a, T a ≤ 10) (hTi : Function.Injective T)
    (block : Fin 4 → Fin s) (slot : Fin 4 → Fin 4)
    (he : ∀ a, ((pick (block a)).val+k-5+offset (slot a))%k =
      (center.val+k-5+T a)%k) :
    ∃ i, (∀ a, block a = i) ∧ Function.Bijective slot ∧ pick i = center := by
  have hb : ∀ a, block a = block 0 := by
    intro a
    exact same_window_same_block hk pick sep (block a) (block 0) (slot a) (slot 0)
      center (T a) (T 0) (hT a) (hT 0) (he a) (he 0)
  have hs : Function.Injective slot := by
    intro a b hab
    apply hTi
    apply same_offset k center.val (T a) (T b) hk center.isLt (hT a) (hT b)
    rw [← he a, ← he b, hb a, hb b, hab]
  have hj : Function.Bijective slot := ⟨hs, Finite.surjective_of_injective hs⟩
  obtain ⟨a, ha⟩ := hj.2 (0 : Fin 4)
  obtain ⟨b, hb3⟩ := hj.2 (3 : Fin 4)
  have h0 : ((pick (block 0)).val+k-5)%k = (center.val+k-5+T a)%k := by
    simpa [hb a, ha, offset] using he a
  have h3 : ((pick (block 0)).val+k-5+10)%k = (center.val+k-5+T b)%k := by
    simpa [hb b, hb3, offset] using he b
  have hc := window_extremes k (pick (block 0)).val center.val (T a) (T b) hk
    (pick (block 0)).isLt center.isLt (hT a) (hT b) h0 h3
  exact ⟨block 0, hb, hj, Fin.ext hc.1⟩

end PrivateTask346LocalWindows

namespace PrivateTask346FaceQuartic
open PrivateTask346AffineCubic PrivateTask346AffineProducts
open PrivateTask346CubicClosure (Blocks)
open PrivateTask346SeparatedLocations PrivateTask346LocalWindows

def pullCoordinate {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (j : Fin k) : Blocks s →ₗ[F] F where
  toFun := fun z => PrivateTask346FaceSpace.insertLinear ell z j
  map_add' := by intro x y; exact congrFun (map_add (PrivateTask346FaceSpace.insertLinear ell) x y) j
  map_smul' := by intro c x; exact congrFun (map_smul (PrivateTask346FaceSpace.insertLinear ell) c x) j

theorem pullCoordinate_zero {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (j : Fin k)
    (hj : ∀ p, ell p ≠ j) : pullCoordinate ell j = 0 := by
  apply LinearMap.ext
  intro z
  change (∑ i : Fin s, ∑ a : Fin 4, if ell (i,a) = j then z i a else 0) = 0
  simp [hj]

def faceProduct {k s : ℕ} (ell : Fin s × Fin 4 → Fin k)
    (base : Fin k → F) (J : Fin 4 → Fin k) (z : Blocks s) : F :=
  PrivateTask346FaceSpace.face ell base z (J 0) *
    PrivateTask346FaceSpace.face ell base z (J 1) *
    PrivateTask346FaceSpace.face ell base z (J 2) *
    PrivateTask346FaceSpace.face ell base z (J 3)

theorem cubic_if_missing_coordinate {k s : ℕ} (ell : Fin s × Fin 4 → Fin k)
    (base : Fin k → F) (J : Fin 4 → Fin k) (a : Fin 4) (ha : ∀ p, ell p ≠ J a) :
    DegreeThree (faceProduct ell base J) := by
  let L : Fin 4 → Blocks s →ₗ[F] F := fun b => pullCoordinate ell (J b)
  let c : Fin 4 → F := fun b => base (J b)
  have hz : L a = 0 := pullCoordinate_zero ell (J a) ha
  have hp : ∀ z, prod4 L z = 0 := by
    intro z
    have hza : L a z = 0 := by rw [hz]; rfl
    have hprod : (∏ b : Fin 4, L b z) = 0 := Finset.prod_eq_zero (Finset.mem_univ a) hza
    simpa [prod4, Fin.prod_univ_succ, mul_assoc] using hprod
  have hs := cubic_quartic_shift L c
  have he : faceProduct ell base J = (fun z =>
      (L 0 z+c 0)*(L 1 z+c 1)*(L 2 z+c 2)*(L 3 z+c 3)-prod4 L z) := by
    funext z
    rw [hp z, sub_zero]
    simp only [faceProduct, PrivateTask346FaceSpace.face_eq, Pi.add_apply]
    rfl
  rw [he]
  exact hs

def special (T : Fin 4 → ℕ) : Prop :=
  ∃ slot : Fin 4 → Fin 4, Function.Bijective slot ∧ ∀ a, T a = offset (slot a)

def window {k : ℕ} (hk : 0 < k) (center : Fin k) (t : ℕ) : Fin k :=
  ⟨(center.val+k-5+t)%k, Nat.mod_lt _ hk⟩

theorem nonspecial_cubic {k s : ℕ} (hk : 0 < k) (h21 : 21 ≤ k)
    (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : Fin k → F) (center : Fin k) (T : Fin 4 → ℕ)
    (hT : ∀ a, T a ≤ 10) (hTi : Function.Injective T) (hn : ¬ special T) :
    DegreeThree (faceProduct (fun p => loc hk pick p.1 p.2) base (fun a => window hk center (T a))) := by
  classical
  let ell : Fin s × Fin 4 → Fin k := fun p => loc hk pick p.1 p.2
  let J : Fin 4 → Fin k := fun a => window hk center (T a)
  by_cases hall : ∀ a : Fin 4, ∃ p : Fin s × Fin 4, ell p = J a
  · choose p hp using hall
    have he : ∀ a, ((pick (p a).1).val+k-5+offset (p a).2)%k =
        (center.val+k-5+T a)%k := by
      intro a
      exact congrArg Fin.val (hp a)
    obtain ⟨i, hb, hs, hi⟩ := quartet_window h21 pick sep center T hT hTi
      (fun a => (p a).1) (fun a => (p a).2) he
    exfalso
    apply hn
    refine ⟨fun a => (p a).2, hs, ?_⟩
    intro a
    have hea := he a
    rw [hb a, hi] at hea
    exact same_offset k center.val (T a) (offset (p a).2) h21 center.isLt
      (hT a) (offset_le _) hea.symm
  · push_neg at hall
    obtain ⟨a, ha⟩ := hall
    exact cubic_if_missing_coordinate ell base J a ha

end PrivateTask346FaceQuartic

namespace PrivateTask346FaceHigh
open PrivateTask346AffineCubic PrivateTask346CubicClosure
open PrivateTask346SeparatedLocations PrivateTask346FaceQuartic

theorem special_image (T : Fin 4 → ℕ) (h : special T) :
    Finset.univ.image T = Finset.univ.image offset := by
  classical
  obtain ⟨slot, hs, ht⟩ := h
  have he : Finset.univ.image slot = Finset.univ := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact hs.2 a
  have hf : T = offset ∘ slot := funext ht
  rw [hf, ← Finset.image_image, he]

def rowTerms : Fin 24 → Fin 4 → ℕ := ![![4, 5, 6, 7], ![4, 5, 6, 8], ![4, 5, 6, 9], ![4, 5, 7, 8], ![4, 5, 7, 10], ![4, 5, 8, 9], ![4, 5, 8, 10], ![4, 5, 9, 10], ![4, 6, 7, 9], ![4, 6, 7, 10], ![4, 6, 8, 9], ![4, 6, 8, 10], ![4, 6, 9, 10], ![4, 7, 8, 9], ![4, 7, 8, 10], ![4, 7, 9, 10], ![5, 6, 7, 10], ![5, 6, 8, 10], ![5, 6, 9, 10], ![5, 7, 8, 10], ![5, 8, 9, 10], ![6, 7, 9, 10], ![6, 8, 9, 10], ![7, 8, 9, 10]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem row_properties : ∀ j : Fin 24,
    (∀ a, rowTerms j a ≤ 10) ∧ Function.Injective (rowTerms j) ∧
      Finset.univ.image (rowTerms j) ≠ Finset.univ.image offset := by
  decide +kernel

def columnTerms : Fin 75 → Fin 4 → ℕ := ![![0, 1, 3, 4], ![0, 1, 3, 6], ![0, 1, 3, 8], ![0, 1, 4, 5], ![0, 1, 4, 7], ![0, 1, 5, 10], ![0, 1, 6, 9], ![0, 1, 7, 10], ![0, 1, 8, 9], ![0, 3, 4, 7], ![0, 3, 5, 6], ![0, 3, 5, 8], ![0, 3, 5, 10], ![0, 3, 6, 9], ![0, 3, 7, 10], ![0, 3, 8, 9], ![0, 3, 9, 10], ![0, 4, 5, 7], ![0, 5, 6, 9], ![0, 5, 7, 10], ![0, 5, 8, 9], ![0, 5, 9, 10], ![1, 2, 3, 4], ![1, 2, 3, 6], ![1, 2, 3, 8], ![1, 2, 4, 9], ![1, 2, 5, 6], ![1, 2, 5, 8], ![1, 2, 5, 10], ![1, 2, 6, 7], ![1, 2, 7, 8], ![1, 2, 7, 10], ![1, 2, 9, 10], ![1, 3, 4, 6], ![1, 3, 4, 8], ![1, 4, 5, 8], ![1, 4, 5, 10], ![1, 4, 6, 9], ![1, 4, 7, 8], ![1, 4, 7, 10], ![1, 4, 9, 10], ![1, 5, 6, 8], ![1, 6, 7, 8], ![1, 6, 8, 9], ![2, 3, 4, 5], ![2, 3, 4, 9], ![2, 3, 5, 6], ![2, 3, 5, 8], ![2, 3, 6, 9], ![2, 3, 8, 9], ![2, 4, 5, 9], ![2, 5, 6, 7], ![2, 5, 6, 9], ![2, 5, 7, 8], ![2, 5, 7, 10], ![2, 5, 8, 9], ![2, 6, 7, 9], ![2, 7, 8, 9], ![2, 7, 9, 10], ![3, 4, 5, 8], ![3, 4, 6, 7], ![3, 4, 8, 9], ![3, 5, 6, 10], ![3, 6, 7, 10], ![3, 6, 9, 10], ![4, 5, 7, 8], ![4, 5, 7, 10], ![4, 5, 8, 9], ![4, 6, 7, 9], ![4, 7, 8, 9], ![4, 7, 9, 10], ![5, 6, 7, 8], ![5, 6, 9, 10], ![6, 7, 8, 9], ![6, 7, 9, 10]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem column_properties : ∀ j : Fin 75,
    (∀ a, columnTerms j a ≤ 10) ∧ Function.Injective (columnTerms j) ∧
      Finset.univ.image (columnTerms j) ≠ Finset.univ.image offset := by
  decide +kernel

variable {k s : ℕ}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem row_high_cubic (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : Fin k → F) (center : Fin k) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    DegreeThree (fun z : Blocks s => PrivateTask346RowQuartic.highPart (fun t : Fin 7 =>
      PrivateTask346FaceSpace.face ell base z (window hk center (t.val+4)))) := by
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  have ht : ∀ j : Fin 24, DegreeThree
      (faceProduct ell base (fun a => window hk center (rowTerms j a))) := by
    intro j
    have hp := row_properties j
    exact nonspecial_cubic hk h21 pick sep base center (rowTerms j) hp.1 hp.2.1
      (fun h => hp.2.2 (special_image _ h))
  have hs := cubic_finset_sum Finset.univ
    (fun j : Fin 24 => faceProduct ell base (fun a => window hk center (rowTerms j a)))
    (fun j _ => ht j)
  convert hs using 1
  funext z
  norm_num [PrivateTask346RowQuartic.highPart, rowTerms,
    faceProduct, offset, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem column_high_cubic (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : Fin k → F) (center : Fin k) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    DegreeThree (fun z : Blocks s => PrivateTask346ColumnQuartic.highPart (fun t : Fin 11 =>
      PrivateTask346FaceSpace.face ell base z (window hk center t.val)) -
      faceProduct ell base (fun a => window hk center (offset a)) z) := by
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  have ht : ∀ j : Fin 75, DegreeThree
      (faceProduct ell base (fun a => window hk center (columnTerms j a))) := by
    intro j
    have hp := column_properties j
    exact nonspecial_cubic hk h21 pick sep base center (columnTerms j) hp.1 hp.2.1
      (fun h => hp.2.2 (special_image _ h))
  have hs := cubic_finset_sum Finset.univ
    (fun j : Fin 75 => faceProduct ell base (fun a => window hk center (columnTerms j a)))
    (fun j _ => ht j)
  convert hs using 1
  funext z
  norm_num [PrivateTask346ColumnQuartic.highPart, columnTerms,
    faceProduct, offset, Fin.sum_univ_succ]
  ring

end PrivateTask346FaceHigh

namespace PrivateTask346SpecialFace
open PrivateTask346AffineCubic PrivateTask346CubicClosure
open PrivateTask346SeparatedLocations PrivateTask346LocalWindows PrivateTask346FaceQuartic

variable {k s : ℕ}

theorem absent_special_cubic (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : Fin k → F) (center : Fin k) (hn : ∀ i, pick i ≠ center) :
    DegreeThree (faceProduct (fun p => loc hk pick p.1 p.2) base
      (fun a => window hk center (offset a))) := by
  classical
  let ell : Fin s × Fin 4 → Fin k := fun p => loc hk pick p.1 p.2
  let J : Fin 4 → Fin k := fun a => window hk center (offset a)
  by_cases hall : ∀ a : Fin 4, ∃ p : Fin s × Fin 4, ell p = J a
  · choose p hp using hall
    have he : ∀ a, ((pick (p a).1).val+k-5+offset (p a).2)%k =
        (center.val+k-5+offset a)%k := by
      intro a
      exact congrArg Fin.val (hp a)
    obtain ⟨i, hb, hs, hi⟩ := quartet_window h21 pick sep center offset offset_le offset_injective
      (fun a => (p a).1) (fun a => (p a).2) he
    exact (hn i hi).elim
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    exact cubic_if_missing_coordinate ell base J a ha

theorem selected_special_remainder (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : Fin k → F) (i : Fin s) :
    DegreeThree (fun z : Blocks s =>
      faceProduct (fun p => loc hk pick p.1 p.2) base
        (fun a => window hk (pick i) (offset a)) z - PrivateTask346CubePrice.quartic (z i)) := by
  let ell : Fin s × Fin 4 → Fin k := fun p => loc hk pick p.1 p.2
  have he : Function.Injective ell := loc_injective hk h21 pick sep
  let c : Fin 4 → F := fun a => base (ell (i,a))
  have hv (z : Blocks s) (a : Fin 4) :
      PrivateTask346FaceSpace.face ell base z (window hk (pick i) (offset a)) = c a + z i a := by
    have hj : window hk (pick i) (offset a) = ell (i,a) := rfl
    rw [hj, PrivateTask346FaceSpace.face_eq]
    have hs := congrFun (congrFun (PrivateTask346FaceSpace.sample_insert ell he z) i) a
    change PrivateTask346FaceSpace.insertLinear ell z (ell (i,a)) = z i a at hs
    change PrivateTask346FaceSpace.insertLinear ell z (ell (i,a)) + base (ell (i,a)) = _
    rw [hs]
    exact add_comm _ _
  have h := cubic_pullback (blockProj i) 0 _
    (PrivateTask346QuarticTranslate.quartic_translation_cubic c)
  convert h using 1
  funext z
  change faceProduct ell base (fun a => window hk (pick i) (offset a)) z -
    PrivateTask346CubePrice.quartic (z i) = _
  simp only [faceProduct]
  rw [hv z 0, hv z 1, hv z 2, hv z 3]
  simp only [blockProj, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply, Pi.add_apply, add_zero, PrivateTask346CubePrice.quartic]
  ring

theorem special_code_remainder (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (hpi : Function.Injective pick)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : Fin k → F) (center : Fin k) :
    DegreeThree (fun z : Blocks s =>
      faceProduct (fun p => loc hk pick p.1 p.2) base (fun a => window hk center (offset a)) z -
        ∑ i : Fin s, if pick i = center then PrivateTask346CubePrice.quartic (z i) else 0) := by
  classical
  by_cases hx : ∃ i, pick i = center
  · obtain ⟨i, hi⟩ := hx
    have hh : ∀ j, pick j = center ↔ j = i := by
      intro j
      constructor
      · intro hj
        exact hpi (hj.trans hi.symm)
      · rintro rfl
        exact hi
    simp_rw [hh]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hi]
    exact selected_special_remainder hk h21 pick sep base i
  · have hn : ∀ i, pick i ≠ center := by simpa using hx
    have h := absent_special_cubic hk h21 pick sep base center hn
    simpa [hn] using h

end PrivateTask346SpecialFace

namespace PrivateTask346RawFace
open PrivateTask346AffineCubic PrivateTask346CubicClosure PrivateTask346RawDegree
open PrivateTask346RawWindows PrivateTask346SeparatedLocations PrivateTask346FaceQuartic
open scoped Fin.NatCast

variable {k s : ℕ} [NeZero k]

def project (j : Fin k) : W k →ₗ[F] F where
  toFun := fun w => w j
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

lemma window_eq (hk : 0 < k) (h21 : 21 ≤ k) (i : Fin k) (t : ℕ) :
    window hk i t = i-5+(t : Fin k) := by
  have hm : 5%k = 5 := Nat.mod_eq_of_lt (by omega)
  have hc : ((5 : ℕ) : Fin k) = (5 : Fin k) := (nat_smul 5).trans fin5.symm
  have hb : ix hk (i.val+k-5) = i-(5 : Fin k) := by
    simpa only [hm, hc] using ix_back hk i 5
  rw [← ix_plus hk (i-5) t, ← hb]
  apply Fin.ext
  change (i.val+k-5+t)%k = ((i.val+k-5)%k+t)%k
  exact (Nat.mod_add_mod _ _ _).symm

lemma row_nat_window (hk : 0 < k) (h21 : 21 ≤ k) (w : W k) (i : Fin k) :
    rawQuartic hk 1 1 i w = PrivateTask346RowQuartic.rawTop
      (fun t : Fin 7 => w (window hk i (t.val+4))) := by
  rw [row_window]
  congr 1
  funext t
  apply congrArg w
  rw [window_eq hk h21, Nat.cast_add]
  simp only [fin5, fin4, nat_smul 4]
  abel

lemma column_nat_window (hk : 0 < k) (h21 : 21 ≤ k) (w : W k) (i : Fin k) :
    rawQuartic hk 2 3 i w = PrivateTask346ColumnQuartic.rawTop
      (fun t : Fin 11 => w (window hk i t.val)) := by
  rw [column_window]
  congr 1
  funext t
  rw [window_eq hk h21]

lemma cubic_on_face (ell : Fin s × Fin 4 → Fin k) (base : W k) (f : W k → F)
    (hf : DegreeThree f) :
    DegreeThree (fun z : Blocks s => f (PrivateTask346FaceSpace.face ell base z)) := by
  have h := cubic_pullback (PrivateTask346FaceSpace.insertLinear ell) base f hf
  simpa only [PrivateTask346FaceSpace.face_eq] using h

theorem row_face_cubic (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : W k) (E G : W k →ₗ[F] W k) (u c d : W k) (center : Fin k) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    DegreeThree (fun z : Blocks s => outer hk 1 1 E G u c d
      (PrivateTask346FaceSpace.face ell base z) center) := by
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  let L : Fin 7 → W k →ₗ[F] F := fun t => project (window hk center (t.val+4))
  have h1 := cubic_on_face ell base _ (raw_remainder_cubic hk 1 1 E G u c d center)
  have hraw := PrivateTask346RowQuartic.quartic_remainder_cubic L
  have h2 : DegreeThree (fun z : Blocks s =>
      rawQuartic hk 1 1 center (PrivateTask346FaceSpace.face ell base z) -
        PrivateTask346RowQuartic.highPart
          (fun t : Fin 7 => PrivateTask346FaceSpace.face ell base z (window hk center (t.val+4)))) := by
    have h := cubic_on_face ell base _ hraw
    simpa only [row_nat_window hk h21, L, project, LinearMap.coe_mk, AddHom.coe_mk] using h
  have h3 := PrivateTask346FaceHigh.row_high_cubic hk h21 pick sep base center
  convert cubic_add _ _ (cubic_add _ _ h1 h2) h3 using 1
  funext z
  ring

theorem column_face_remainder (hk : 0 < k) (h21 : 21 ≤ k) (pick : Fin s → Fin k)
    (hpi : Function.Injective pick)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : W k) (E G : W k →ₗ[F] W k) (u c d : W k) (center : Fin k) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    DegreeThree (fun z : Blocks s => outer hk 2 3 E G u c d
      (PrivateTask346FaceSpace.face ell base z) center -
        ∑ i : Fin s, if pick i = center then PrivateTask346CubePrice.quartic (z i) else 0) := by
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  let L : Fin 11 → W k →ₗ[F] F := fun t => project (window hk center t.val)
  have h1 := cubic_on_face ell base _ (raw_remainder_cubic hk 2 3 E G u c d center)
  have hraw := PrivateTask346ColumnQuartic.quartic_remainder_cubic L
  have h2 : DegreeThree (fun z : Blocks s =>
      rawQuartic hk 2 3 center (PrivateTask346FaceSpace.face ell base z) -
        PrivateTask346ColumnQuartic.highPart
          (fun t : Fin 11 => PrivateTask346FaceSpace.face ell base z (window hk center t.val))) := by
    have h := cubic_on_face ell base _ hraw
    simpa only [column_nat_window hk h21, L, project, LinearMap.coe_mk, AddHom.coe_mk] using h
  have h3 := PrivateTask346FaceHigh.column_high_cubic hk h21 pick sep base center
  have h4 := PrivateTask346SpecialFace.special_code_remainder hk h21 pick hpi sep base center
  convert cubic_add _ _ (cubic_add _ _ (cubic_add _ _ h1 h2) h3) h4 using 1
  funext z
  ring

end PrivateTask346RawFace

namespace PrivateTask346ObservationDecomposition
open PrivateTask346AffineCubic PrivateTask346CubicClosure PrivateTask346RawDegree
open PrivateTask346SeparatedLocations PrivateTask346RawFace

variable {k s m : ℕ} [NeZero k]

def observe (a : Fin k → Bool) (w : W k) : F := ∑ i, if a i then w i else 0

def value (hk : 0 < k) (u v r1 r2 c1 c2 : W k) (A B : Fin m → Fin k → Bool)
    (w : W k) (j : Fin m) : F :=
  observe (A j) (outer hk 1 1 LinearMap.id (rot hk 2) u r1 r2 w) +
    observe (B j) (outer hk 2 3 (rot hk 4) (rot hk 7) v c1 c2 w)

theorem coded_sum (pick : Fin s → Fin k) (B : Fin k → Bool) (f : Fin s → F) :
    (∑ l : Fin k, if B l then (∑ i : Fin s, if pick i = l then f i else 0) else 0) =
      ∑ i : Fin s, (if B (pick i) then (1 : F) else 0) * f i := by
  classical
  have he : (∑ l : Fin k, if B l then (∑ i : Fin s, if pick i = l then f i else 0) else 0) =
      ∑ l : Fin k, ∑ i : Fin s, if B l then (if pick i = l then f i else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    cases hb : B l <;> simp [hb]
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hh (l : Fin k) :
      (if B l then (if pick i = l then f i else 0) else 0) =
        (if pick i = l then (if B (pick i) then f i else 0) else 0) := by
    by_cases h : pick i = l
    · subst l
      simp
    · simp [h]
  simp_rw [hh]
  simp

theorem residual_cubic (hk : 0 < k) (h21 : 21 ≤ k) (u v r1 r2 c1 c2 : W k)
    (A B : Fin m → Fin k → Bool) (pick : Fin s → Fin k) (hpi : Function.Injective pick)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : W k) (j : Fin m) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    DegreeThree (fun z : Blocks s => value hk u v r1 r2 c1 c2 A B
      (PrivateTask346FaceSpace.face ell base z) j -
        ∑ i : Fin s, (if B j (pick i) then (1 : F) else 0) * PrivateTask346CubePrice.quartic (z i)) := by
  classical
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  let row : Fin k → Blocks s → F := fun l z =>
    outer hk 1 1 LinearMap.id (rot hk 2) u r1 r2 (PrivateTask346FaceSpace.face ell base z) l
  let col : Fin k → Blocks s → F := fun l z =>
    outer hk 2 3 (rot hk 4) (rot hk 7) v c1 c2 (PrivateTask346FaceSpace.face ell base z) l
  let K : Fin k → Blocks s → F := fun l z =>
    ∑ i : Fin s, if pick i = l then PrivateTask346CubePrice.quartic (z i) else 0
  have hr : DegreeThree (fun z => ∑ l : Fin k, if A j l then row l z else 0) := by
    apply cubic_finset_sum Finset.univ
    intro l hl
    cases hb : A j l
    · simpa [hb] using (cubic_zero (V := Blocks s))
    · simpa [hb, row] using row_face_cubic hk h21 pick sep base LinearMap.id (rot hk 2) u r1 r2 l
  have hc : DegreeThree (fun z => ∑ l : Fin k, if B j l then col l z-K l z else 0) := by
    apply cubic_finset_sum Finset.univ
    intro l hl
    cases hb : B j l
    · simpa [hb] using (cubic_zero (V := Blocks s))
    · simpa [hb, col, K] using column_face_remainder hk h21 pick hpi sep base
        (rot hk 4) (rot hk 7) v c1 c2 l
  have he : (fun z : Blocks s => value hk u v r1 r2 c1 c2 A B
      (PrivateTask346FaceSpace.face ell base z) j -
        ∑ i : Fin s, (if B j (pick i) then (1 : F) else 0) * PrivateTask346CubePrice.quartic (z i)) =
      (fun z => (∑ l : Fin k, if A j l then row l z else 0) +
        (∑ l : Fin k, if B j l then col l z-K l z else 0)) := by
    funext z
    have hs : (∑ l : Fin k, if B j l then col l z-K l z else 0) =
        (∑ l : Fin k, if B j l then col l z else 0) -
          (∑ l : Fin k, if B j l then K l z else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      cases hb : B j l <;> simp [hb]
    rw [hs]
    have hcode := coded_sum pick (B j) (fun i => PrivateTask346CubePrice.quartic (z i))
    change (∑ l, if A j l then row l z else 0) + (∑ l, if B j l then col l z else 0) - _ = _
    dsimp [K]
    rw [hcode]
    ring
  change DegreeThree (fun z : Blocks s => value hk u v r1 r2 c1 c2 A B
    (PrivateTask346FaceSpace.face ell base z) j -
      ∑ i : Fin s, (if B j (pick i) then (1 : F) else 0) * PrivateTask346CubePrice.quartic (z i))
  rw [he]
  exact cubic_add _ _ hr hc

theorem face_decomposition (hk : 0 < k) (h21 : 21 ≤ k) (u v r1 r2 c1 c2 : W k)
    (A B : Fin m → Fin k → Bool) (pick : Fin s → Fin k) (hpi : Function.Injective pick)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k) (base : W k) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    ∃ q : Fin m → Blocks s → F, (∀ j, DegreeThree (q j)) ∧
      ∀ z j, value hk u v r1 r2 c1 c2 A B (PrivateTask346FaceSpace.face ell base z) j =
        (∑ i : Fin s, (if B j (pick i) then (1 : F) else 0) *
          PrivateTask346CubePrice.quartic (z i)) + q j z := by
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  let q : Fin m → Blocks s → F := fun j z => value hk u v r1 r2 c1 c2 A B
    (PrivateTask346FaceSpace.face ell base z) j -
      ∑ i : Fin s, (if B j (pick i) then (1 : F) else 0) * PrivateTask346CubePrice.quartic (z i)
  refine ⟨q, fun j => residual_cubic hk h21 u v r1 r2 c1 c2 A B pick hpi sep base j, ?_⟩
  intro z j
  dsimp [q]
  ring

end PrivateTask346ObservationDecomposition

namespace PrivateTask346FixedTrace

abbrev F := ZMod 2
def digit (a : F) : Bool := decide (a ≠ 0)
lemma digit_injective : Function.Injective digit := by decide +kernel

def encode (bs : List Bool) : ℕ := bs.foldl (fun n b => 2*n+b.toNat) 0

lemma encode_snoc (bs : List Bool) (b : Bool) : encode (bs ++ [b]) = 2*encode bs+b.toNat := by
  simp [encode,List.foldl_append]

theorem encode_injective (bs cs : List Bool) :
    bs.length = cs.length → encode bs = encode cs → bs = cs := by
  induction bs using List.reverseRecOn generalizing cs with
  | nil =>
    intro hl he
    have hc : cs = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    simp [hc]
  | append_singleton bs b ih =>
    induction cs using List.reverseRecOn with
    | nil => intro hl; simp at hl
    | append_singleton cs c _ =>
      intro hl he
      have hl' : bs.length = cs.length := by simpa using hl
      have he' : 2*encode bs+b.toNat = 2*encode cs+c.toNat := by simpa only [encode_snoc] using he
      have hb : b = c := by cases b <;> cases c <;> simp_all <;> omega
      have hp : encode bs = encode cs := by rw [hb] at he'; omega
      rw [ih cs hl' hp,hb]

def answers {V : Type*} {h : ℕ} (A : Fin h → V → F) (x : V) : List Bool :=
  (List.finRange h).map fun a => digit (A a x)

def trace {V : Type*} {h : ℕ} (A : Fin h → V → F) (x : V) : ℕ :=
  (List.finRange h).foldl (fun n a => 2*n+(if A a x = 0 then 0 else 1)) 0

lemma trace_eq_encode {V : Type*} {h : ℕ} (A : Fin h → V → F) (x : V) :
    trace A x = encode (answers A x) := by
  unfold trace encode answers
  rw [List.foldl_map]
  congr 1
  funext n a
  by_cases ha : A a x = 0 <;> simp [digit,ha]

theorem trace_preserves_answers {V : Type*} {h : ℕ} (A : Fin h → V → F) (x y : V)
    (he : trace A x = trace A y) (a : Fin h) : A a x = A a y := by
  have hl : answers A x = answers A y := encode_injective _ _ (by simp [answers])
    (by simpa only [← trace_eq_encode] using he)
  apply digit_injective
  have hv := congrArg (fun l : List Bool => l.getD a.val false) hl
  simpa [answers,List.getD_eq_getElem?_getD] using hv

end PrivateTask346FixedTrace

namespace PrivateTask346FaceCard
open PrivateTask346CubePrice PrivateTask346OneFace

lemma vec_bijective : Function.Bijective vec := by decide +kernel

noncomputable def cubeEquiv : Cube ≃ W := Equiv.ofBijective vec vec_bijective

theorem card_face (P : W → Prop) [DecidablePred P] :
    Nat.card {z : W // P z} = ((Finset.univ : Finset Cube).filter fun z => P (vec z)).card := by
  classical
  have h := Nat.card_congr (Equiv.subtypeEquiv cubeEquiv (fun _ => Iff.rfl) :
    {z : Cube // P (vec z)} ≃ {z : W // P z})
  rw [← h,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem zero_query_card_price {m : ℕ} (C : Fin m → F) (q : Fin m → W → F)
    (hq : ∀ j, Cubic (q j)) :
    (∀ p : Fin m → W → F, (∀ j, Cubic (p j)) →
      Nat.card {z : W // ∀ j, C j * quartic z + q j z = p j z} ≤
        if ∀ j, C j = 0 then 16 else 15) ∧
    (∃ p : Fin m → W → F, (∀ j, Cubic (p j)) ∧
      Nat.card {z : W // ∀ j, C j * quartic z + q j z = p j z} =
        if ∀ j, C j = 0 then 16 else 15) := by
  have h := vector_zero_query_price C q hq
  simpa only [card_face,hitSet] using h

end PrivateTask346FaceCard

namespace PrivateTask346IndependentPrice

abbrev F := ZMod 2

def score {s m : ℕ} (C : Fin s → Fin m → F) (D : Finset (Fin s)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin s))).filter fun H =>
    Disjoint H D ∧ ∀ j : Fin m, (∑ i ∈ H, C i j) = 0).sum
      (fun H => 16^D.card * 15^(s-D.card-H.card))

lemma score_independent {s m : ℕ} (C : Fin s → Fin m → F)
    (hk : ∀ H : Finset (Fin s), (∀ j : Fin m, (∑ i ∈ H, C i j) = 0) → H = ∅)
    (D : Finset (Fin s)) : score C D = 16^D.card * 15^(s-D.card) := by
  classical
  have he : ((Finset.univ : Finset (Finset (Fin s))).filter fun H =>
      Disjoint H D ∧ ∀ j : Fin m, (∑ i ∈ H, C i j) = 0) = {∅} := by
    ext H
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro h
      exact hk H h.2
    · intro h
      subst H
      simp
  unfold score
  rw [he]
  simp

lemma ratio_weaken (a e N M : ℕ) (hea : e ≤ a)
    (h : 16^a * N ≤ 15^a * M) : 16^e * N ≤ 15^e * M := by
  have hp : 15^(a-e) ≤ 16^(a-e) := by gcongr <;> norm_num
  have h16 : 16^a = 16^(a-e) * 16^e := by
    rw [← pow_add]
    congr 1
    omega
  have h15 : 15^a = 15^(a-e) * 15^e := by
    rw [← pow_add]
    congr 1
    omega
  rw [h16,h15] at h
  have h' : 16^(a-e) * (16^e * N) ≤ 16^(a-e) * (15^e * M) := by
    calc
      _ ≤ 15^(a-e) * (15^e * M) := by simpa [Nat.mul_assoc] using h
      _ ≤ _ := Nat.mul_le_mul_right _ hp
  exact Nat.le_of_mul_le_mul_left h' (by positivity)

theorem independent_fiber_bound (k s m h N : ℕ) (C : Fin s → Fin m → F)
    (hk : ∀ H : Finset (Fin s), (∀ j : Fin m, (∑ i ∈ H, C i j) = 0) → H = ∅)
    (whole : ∃ D : Finset (Fin s), D.card ≤ h ∧ 16^s * N ≤ 2^k * score C D) :
    16^(s-h) * N ≤ 15^(s-h) * 2^k := by
  obtain ⟨D,hd,hw⟩ := whole
  have ds : D.card ≤ s := by simpa using Finset.card_le_univ D
  have h16 : 16^s = 16^D.card * 16^(s-D.card) := by
    rw [← pow_add]
    congr 1
    omega
  rw [score_independent C hk D,h16] at hw
  have h' : 16^D.card * (16^(s-D.card) * N) ≤ 16^D.card * (15^(s-D.card) * 2^k) := by
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hw
  have hb := Nat.le_of_mul_le_mul_left h' (by positivity)
  exact ratio_weaken (s-D.card) (s-h) N (2^k) (by omega) hb

end PrivateTask346IndependentPrice

namespace PrivateTask346CodeCount
open PrivateTask346CubePrice
open PrivateTask346OneFace (field_cases)

def support {s : ℕ} (z : Fin s → W) : Finset (Fin s) :=
  Finset.univ.filter fun i => quartic (z i) = 1

lemma one_count : Fintype.card {z : W // quartic z = 1} = 1 := by decide +kernel
lemma not_one_count : Fintype.card {z : W // quartic z ≠ 1} = 15 := by decide +kernel

def supportFibreEquiv {s : ℕ} (H : Finset (Fin s)) :
    {z : Fin s → W // support z = H} ≃ ((i : Fin s) → {x : W // quartic x = 1 ↔ i ∈ H}) where
  toFun z i := ⟨z.1 i,by
    have h := Finset.ext_iff.mp z.2 i
    simpa [support] using h⟩
  invFun z := ⟨fun i => (z i).1,by
    apply Finset.ext
    intro i
    simpa [support] using (z i).2⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by intro z; funext i; apply Subtype.ext; rfl

lemma support_fibre_card {s : ℕ} (H : Finset (Fin s)) :
    Nat.card {z : Fin s → W // support z = H} = 15^(s-H.card) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (supportFibreEquiv H),Fintype.card_pi]
  have each (i : Fin s) : Fintype.card {x : W // quartic x = 1 ↔ i ∈ H} =
      if i ∈ H then 1 else 15 := by
    by_cases hi : i ∈ H
    · simpa [hi] using one_count
    · simpa [hi] using not_one_count
  simp_rw [each]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul,Finset.prod_const]
  have he : (Finset.univ.filter fun i : Fin s => i ∉ H) = Finset.univ \ H := by
    ext i
    simp
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ H)]
  simp

def supportSigmaEquiv {s : ℕ} (K : Finset (Fin s) → Prop) :
    {z : Fin s → W // K (support z)} ≃
      (H : {H : Finset (Fin s) // K H}) × {z : Fin s → W // support z = H.1} where
  toFun z := ⟨⟨support z.1,z.2⟩,⟨z.1,rfl⟩⟩
  invFun z := ⟨z.2.1,z.2.2.symm ▸ z.1.2⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by
    rintro ⟨⟨H,hH⟩,⟨z,hz⟩⟩
    cases hz
    rfl

theorem card_support_pred {s : ℕ} (K : Finset (Fin s) → Prop) [DecidablePred K] :
    Nat.card {z : Fin s → W // K (support z)} =
      ((Finset.univ : Finset (Finset (Fin s))).filter K).sum (fun H => 15^(s-H.card)) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (supportSigmaEquiv K),Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card,support_fibre_card]
  exact (Finset.sum_subtype (Finset.univ.filter K) (by simp) (fun H => 15^(s-H.card))).symm

lemma quartic_support {s : ℕ} (z : Fin s → W) (i : Fin s) :
    quartic (z i) = if i ∈ support z then 1 else 0 := by
  by_cases hi : quartic (z i) = 1
  · simp [support,hi]
  · obtain h0 | h1 := field_cases (quartic (z i))
    · simp [support,hi,h0]
    · exact (hi h1).elim

lemma code_values {s m : ℕ} (C : Fin s → Fin m → F) (z : Fin s → W) (j : Fin m) :
    (∑ i : Fin s, C i j * quartic (z i)) = ∑ i ∈ support z, C i j := by
  simp_rw [quartic_support,mul_ite,mul_one,mul_zero]
  simp

theorem unqueried_coded_fibre {s m : ℕ} (C : Fin s → Fin m → F) :
    Nat.card {z : Fin s → W // ∀ j : Fin m, (∑ i : Fin s, C i j * quartic (z i)) = 0} =
      PrivateTask346IndependentPrice.score C ∅ := by
  classical
  calc
    Nat.card {z : Fin s → W // ∀ j : Fin m, (∑ i : Fin s, C i j * quartic (z i)) = 0} =
        Nat.card {z : Fin s → W // ∀ j : Fin m, (∑ i ∈ support z, C i j) = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun z => by simp_rw [code_values]))
    _ = _ := by
      simpa [PrivateTask346IndependentPrice.score] using
        (card_support_pred (fun H : Finset (Fin s) => ∀ j : Fin m, (∑ i ∈ H, C i j) = 0))

end PrivateTask346CodeCount

namespace PrivateTask346IgnoredCodeCount
open PrivateTask346CubePrice PrivateTask346CodeCount

def partialSupport {s : ℕ} (D : Finset (Fin s)) (z : Fin s → W) : Finset (Fin s) := support z \ D

lemma partial_disjoint {s : ℕ} (D : Finset (Fin s)) (z : Fin s → W) :
    Disjoint (partialSupport D z) D := by
  exact Finset.disjoint_left.mpr (fun _ hi hd => (Finset.mem_sdiff.mp hi).2 hd)

def partialFibreEquiv {s : ℕ} (D H : Finset (Fin s)) :
    {z : Fin s → W // partialSupport D z = H} ≃
      ((i : Fin s) → {x : W // (quartic x = 1 ∧ i ∉ D) ↔ i ∈ H}) where
  toFun z i := ⟨z.1 i,by
    have h := Finset.ext_iff.mp z.2 i
    simpa [partialSupport,support] using h⟩
  invFun z := ⟨fun i => (z i).1,by
    apply Finset.ext
    intro i
    simpa [partialSupport,support] using (z i).2⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by intro z; funext i; apply Subtype.ext; rfl

lemma partial_fibre_card {s : ℕ} (D H : Finset (Fin s)) (hdj : Disjoint H D) :
    Nat.card {z : Fin s → W // partialSupport D z = H} =
      16^D.card * 15^(s-D.card-H.card) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (partialFibreEquiv D H),Fintype.card_pi]
  have each (i : Fin s) : Fintype.card {x : W // (quartic x = 1 ∧ i ∉ D) ↔ i ∈ H} =
      if i ∈ D then 16 else if i ∈ H then 1 else 15 := by
    by_cases hi : i ∈ D
    · have hj : i ∉ H := fun h => Finset.disjoint_left.mp hdj h hi
      simpa [hi,hj] using (show Fintype.card W = 16 by decide +kernel)
    · by_cases hj : i ∈ H
      · simpa [hi,hj] using one_count
      · simpa [hi,hj] using not_one_count
  simp_rw [each]
  rw [Finset.prod_ite,Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul,mul_one,Finset.prod_const]
  have hD : (Finset.univ.filter fun i : Fin s => i ∈ D) = D := by ext i; simp
  have he : ((Finset.univ.filter fun i : Fin s => i ∉ D).filter fun i => i ∉ H) =
      Finset.univ \ (D ∪ H) := by
    ext i
    simp
  rw [hD,he,Finset.card_sdiff_of_subset (Finset.subset_univ (D ∪ H)),
    Finset.card_union_of_disjoint hdj.symm]
  simp only [Finset.card_univ,Fintype.card_fin,Nat.sub_sub]

def partialSigmaEquiv {s : ℕ} (D : Finset (Fin s)) (K : Finset (Fin s) → Prop) :
    {z : Fin s → W // K (partialSupport D z)} ≃
      (H : {H : Finset (Fin s) // Disjoint H D ∧ K H}) ×
        {z : Fin s → W // partialSupport D z = H.1} where
  toFun z := ⟨⟨partialSupport D z.1,partial_disjoint D z.1,z.2⟩,⟨z.1,rfl⟩⟩
  invFun z := ⟨z.2.1,z.2.2.symm ▸ z.1.2.2⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by
    rintro ⟨⟨H,hH⟩,⟨z,hz⟩⟩
    cases hz
    rfl

theorem card_partial_pred {s : ℕ} (D : Finset (Fin s))
    (K : Finset (Fin s) → Prop) [DecidablePred K] :
    Nat.card {z : Fin s → W // K (partialSupport D z)} =
      ((Finset.univ : Finset (Finset (Fin s))).filter fun H => Disjoint H D ∧ K H).sum
        (fun H => 16^D.card * 15^(s-D.card-H.card)) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (partialSigmaEquiv D K),Fintype.card_sigma]
  have fibre (H : {H : Finset (Fin s) // Disjoint H D ∧ K H}) :
      Fintype.card {z : Fin s → W // partialSupport D z = H.1} =
        16^D.card * 15^(s-D.card-H.1.card) := by
    rw [← Nat.card_eq_fintype_card]
    exact partial_fibre_card D H.1 H.2.1
  simp_rw [fibre]
  exact (Finset.sum_subtype (Finset.univ.filter fun H => Disjoint H D ∧ K H) (by simp)
    (fun H => 16^D.card * 15^(s-D.card-H.card))).symm

lemma partial_code_values {s m : ℕ} (C : Fin s → Fin m → F) (D : Finset (Fin s))
    (z : Fin s → W) (j : Fin m) :
    (∑ i ∈ Finset.univ \ D, C i j * quartic (z i)) = ∑ i ∈ partialSupport D z, C i j := by
  simp_rw [quartic_support,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_mem]
  have he : (Finset.univ \ D) ∩ support z = partialSupport D z := by
    ext i
    simp only [partialSupport,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  rw [he]

theorem ignored_coded_fibre {s m : ℕ} (C : Fin s → Fin m → F) (D : Finset (Fin s)) :
    Nat.card {z : Fin s → W // ∀ j : Fin m, (∑ i ∈ Finset.univ \ D, C i j * quartic (z i)) = 0} =
      PrivateTask346IndependentPrice.score C D := by
  classical
  calc
    Nat.card {z : Fin s → W // ∀ j : Fin m, (∑ i ∈ Finset.univ \ D, C i j * quartic (z i)) = 0} =
        Nat.card {z : Fin s → W // ∀ j : Fin m, (∑ i ∈ partialSupport D z, C i j) = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun z => by simp_rw [partial_code_values]))
    _ = _ := by
      exact card_partial_pred D (fun H : Finset (Fin s) => ∀ j : Fin m, (∑ i ∈ H, C i j) = 0)

end PrivateTask346IgnoredCodeCount

namespace PrivateTask346Attainment
open PrivateTask346AffineCubic (DegreeThree)
open PrivateTask346CubicClosure (Blocks coordinate cubic_add cubic_const_mul cubic_finset_sum cubic_block_triple)
open PrivateTask346CubePrice (quartic)

abbrev F := ZMod 2

def run {s h : ℕ} (A : Fin h → Blocks s →ₗ[F] F) (z : Blocks s) : ℕ :=
  PrivateTask346FixedTrace.trace (fun a => A a) z

theorem covering_questions {s h : ℕ} (D : Finset (Fin s)) (hd : D.card ≤ h) :
    ∃ A : Fin h → Blocks s →ₗ[F] F, ∀ i ∈ D, ∃ a : Fin h, A a = coordinate i := by
  classical
  have hc : Fintype.card {i : Fin s // i ∈ D} ≤ Fintype.card (Fin h) := by simpa using hd
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let A := fun a : Fin h => if ha : ∃ i : {i : Fin s // i ∈ D}, e i = a then
    coordinate ha.choose.1 else 0
  refine ⟨A,?_⟩
  intro i hi
  let ix : {i : Fin s // i ∈ D} := ⟨i,hi⟩
  refine ⟨e ix,?_⟩
  have ha : ∃ j : {j : Fin s // j ∈ D}, e j = e ix := ⟨ix,rfl⟩
  dsimp [A]
  rw [dif_pos ha]
  have he : ha.choose = ix := e.injective ha.choose_spec
  rw [he]

noncomputable def representative {s h : ℕ} (A : Fin h → Blocks s →ₗ[F] F) (t : ℕ) : Blocks s :=
  if hu : ∃ u : Blocks s, run A u = t then hu.choose else 0

lemma representative_run {s h : ℕ} (A : Fin h → Blocks s →ₗ[F] F) (z : Blocks s) :
    run A (representative A (run A z)) = run A z := by
  have hu : ∃ u : Blocks s, run A u = run A z := ⟨z,rfl⟩
  simp only [representative,dif_pos hu]
  exact hu.choose_spec

lemma representative_coordinate {s h : ℕ} (D : Finset (Fin s))
    (A : Fin h → Blocks s →ₗ[F] F) (cover : ∀ i ∈ D, ∃ a : Fin h, A a = coordinate i)
    (z : Blocks s) (i : Fin s) (hi : i ∈ D) :
    representative A (run A z) i 0 = z i 0 := by
  obtain ⟨a,ha⟩ := cover i hi
  have he := PrivateTask346FixedTrace.trace_preserves_answers (fun a => A a)
    (representative A (run A z)) z (representative_run A z) a
  rw [ha] at he
  exact he

noncomputable def predictor {s m h : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (D : Finset (Fin s)) (A : Fin h → Blocks s →ₗ[F] F) (t : ℕ) (j : Fin m) (z : Blocks s) : F :=
  q j z + ∑ i ∈ D, (C i j * representative A t i 0) * (z i 1 * z i 2 * z i 3)

theorem predictor_cubic {s m h : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (hq : ∀ j, DegreeThree (q j)) (D : Finset (Fin s)) (A : Fin h → Blocks s →ₗ[F] F)
    (t : ℕ) (j : Fin m) : DegreeThree (predictor C q D A t j) := by
  apply cubic_add _ _ (hq j)
  apply cubic_finset_sum
  intro i hi
  exact cubic_const_mul _ (cubic_block_triple i) _

def value {s m : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (z : Blocks s) (j : Fin m) : F := (∑ i : Fin s, C i j * quartic (z i)) + q j z

def hit {s m h : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (A : Fin h → Blocks s →ₗ[F] F) (p : ℕ → Fin m → Blocks s → F) (z : Blocks s) : Prop :=
  ∀ j, value C q z j = p (run A z) j z

lemma hit_iff {s m h : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (D : Finset (Fin s)) (A : Fin h → Blocks s →ₗ[F] F)
    (cover : ∀ i ∈ D, ∃ a : Fin h, A a = coordinate i) (z : Blocks s) :
    hit C q A (predictor C q D A) z ↔
      ∀ j : Fin m, (∑ i ∈ Finset.univ \ D, C i j * quartic (z i)) = 0 := by
  classical
  have rep (j : Fin m) :
      (∑ i ∈ D, (C i j * representative A (run A z) i 0) * (z i 1 * z i 2 * z i 3)) =
      ∑ i ∈ D, C i j * quartic (z i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [representative_coordinate D A cover z i hi]
    unfold quartic
    ring
  have disj : Disjoint D (Finset.univ \ D) :=
    Finset.disjoint_left.mpr (fun _ hi hd => (Finset.mem_sdiff.mp hd).2 hi)
  have un : D ∪ (Finset.univ \ D) = Finset.univ := by ext i; simp
  have split (j : Fin m) :
      (∑ i : Fin s, C i j * quartic (z i)) =
      (∑ i ∈ D, C i j * quartic (z i)) + ∑ i ∈ Finset.univ \ D, C i j * quartic (z i) := by
    rw [← Finset.sum_union disj,un]
  unfold hit value predictor
  simp_rw [rep]
  constructor
  · intro h j
    have hh := h j
    rw [split j] at hh
    linear_combination hh
  · intro h j
    rw [split j,h j]
    ring

theorem fixed_attains_score {s m h : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (hq : ∀ j, DegreeThree (q j)) (D : Finset (Fin s)) (hd : D.card ≤ h) :
    ∃ (A : Fin h → Blocks s →ₗ[F] F) (p : ℕ → Fin m → Blocks s → F),
      (∀ t j, DegreeThree (p t j)) ∧
      Nat.card {z : Blocks s // hit C q A p z} = PrivateTask346IndependentPrice.score C D := by
  classical
  obtain ⟨A,cover⟩ := covering_questions D hd
  refine ⟨A,predictor C q D A,predictor_cubic C q hq D A,?_⟩
  calc
    Nat.card {z : Blocks s // hit C q A (predictor C q D A) z} =
        Nat.card {z : Blocks s // ∀ j : Fin m, (∑ i ∈ Finset.univ \ D, C i j * quartic (z i)) = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (hit_iff C q D A cover))
    _ = _ := PrivateTask346IgnoredCodeCount.ignored_coded_fibre C D

theorem attain_score {s m h : ℕ} (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (hq : ∀ j, DegreeThree (q j)) (D : Finset (Fin s)) (hd : D.card ≤ h) :
    ∃ (ask : Fin h → ℕ → Blocks s →ₗ[F] F) (out : ℕ → Fin m → Blocks s → F),
      (∀ t j, DegreeThree (out t j)) ∧
      Nat.card {z : Blocks s //
        let t := (List.finRange h).foldl (fun n a => 2*n+(if ask a n z = 0 then 0 else 1)) 0
        ∀ j, value C q z j = out t j z} = PrivateTask346IndependentPrice.score C D := by
  obtain ⟨A,p,hp,hcard⟩ := fixed_attains_score C q hq D hd
  exact ⟨fun a _ => A a,p,hp,hcard⟩

end PrivateTask346Attainment

namespace PrivateTask346ProtocolLift
open PrivateTask346FaceSpace
open PrivateTask346CubicClosure (Blocks)
open PrivateTask346AffineCubic (DegreeThree)

theorem fixed_protocol_lift {k s m h : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (base : Raw k) (A : Fin h → Blocks s →ₗ[F] F) (p : ℕ → Fin m → Blocks s → F)
    (hp : ∀ t j, DegreeThree (p t j)) :
    ∃ (B : Fin h → Raw k →ₗ[F] F) (out : ℕ → Fin m → Raw k → F),
      (∀ t j, DegreeThree (out t j)) ∧ ∀ z : Blocks s, ∀ j : Fin m,
        out (PrivateTask346FixedTrace.trace (fun a => B a) (face ell base z)) j (face ell base z) =
          p (PrivateTask346Attainment.run A z) j z := by
  classical
  let B := fun a : Fin h => (A a).comp (sampleLinear ell)
  let tr := fun z : Blocks s => PrivateTask346FixedTrace.trace (fun a => B a) (face ell base z)
  let rep := fun t : ℕ => if hu : ∃ u : Blocks s, tr u = t then hu.choose else 0
  have repTrace (z : Blocks s) : tr (rep (tr z)) = tr z := by
    have hu : ∃ u : Blocks s, tr u = tr z := ⟨z,rfl⟩
    simp only [rep,dif_pos hu]
    exact hu.choose_spec
  have evalB (a : Fin h) (z : Blocks s) :
      B a (face ell base z) = A a z + A a (sampleLinear ell base) := by
    simp only [B,LinearMap.comp_apply,face_eq,map_add,sample_insert ell he]
  have names (z : Blocks s) :
      PrivateTask346Attainment.run A (rep (tr z)) = PrivateTask346Attainment.run A z := by
    have av (a : Fin h) : A a (rep (tr z)) = A a z := by
      have hv := PrivateTask346FixedTrace.trace_preserves_answers (fun a => B a)
        (face ell base (rep (tr z))) (face ell base z) (repTrace z) a
      rw [evalB,evalB] at hv
      exact add_right_cancel hv
    unfold PrivateTask346Attainment.run PrivateTask346FixedTrace.trace
    simp_rw [av]
  have lifts (t : ℕ) (j : Fin m) :
      ∃ f : Raw k → F, DegreeThree f ∧ ∀ z : Blocks s,
        f (face ell base z) = p (PrivateTask346Attainment.run A (rep t)) j z :=
    cubic_lift_face ell he base _ (hp _ j)
  choose out houtC houtEq using lifts
  refine ⟨B,out,houtC,?_⟩
  intro z j
  change out (tr z) j (face ell base z) = p (PrivateTask346Attainment.run A z) j z
  rw [houtEq,names]

theorem raw_attains_score {k s m h : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (base : Raw k) (g : Raw k → Fin m → F) (C : Fin s → Fin m → F)
    (q : Fin m → Blocks s → F) (hq : ∀ j, DegreeThree (q j))
    (decomp : ∀ z : Blocks s, ∀ j : Fin m,
      g (face ell base z) j = PrivateTask346Attainment.value C q z j)
    (D : Finset (Fin s)) (hd : D.card ≤ h) :
    ∃ (ask : Fin h → ℕ → Raw k →ₗ[F] F) (out : ℕ → Fin m → Raw k → F),
      (∀ t j, DegreeThree (out t j)) ∧
      Nat.card {z : Blocks s //
        let w := face ell base z
        let t := (List.finRange h).foldl (fun n a => 2*n+(if ask a n w = 0 then 0 else 1)) 0
        ∀ j, g w j = out t j w} = PrivateTask346IndependentPrice.score C D := by
  classical
  obtain ⟨A,p,hp,hcard⟩ := PrivateTask346Attainment.fixed_attains_score C q hq D hd
  obtain ⟨B,out,hout,hmatch⟩ := fixed_protocol_lift ell he base A p hp
  refine ⟨fun a _ => B a,out,hout,?_⟩
  change Nat.card {z : Blocks s // ∀ j : Fin m,
    g (face ell base z) j = out (PrivateTask346FixedTrace.trace (fun a => B a) (face ell base z)) j
      (face ell base z)} = PrivateTask346IndependentPrice.score C D
  calc
    Nat.card {z : Blocks s // ∀ j : Fin m,
      g (face ell base z) j = out (PrivateTask346FixedTrace.trace (fun a => B a) (face ell base z)) j
        (face ell base z)} =
        Nat.card {z : Blocks s // PrivateTask346Attainment.hit C q A p z} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro z
      unfold PrivateTask346Attainment.hit
      simp_rw [decomp,hmatch]
    _ = _ := hcard

end PrivateTask346ProtocolLift

namespace PrivateTask346ActualAttainment
open PrivateTask346AffineCubic PrivateTask346CubicClosure PrivateTask346RawDegree
open PrivateTask346SeparatedLocations PrivateTask346ObservationDecomposition

variable {k s m h : ℕ} [NeZero k]

theorem attain_actual_score (hk : 0 < k) (h21 : 21 ≤ k) (u v r1 r2 c1 c2 : W k)
    (A B : Fin m → Fin k → Bool) (pick : Fin s → Fin k) (hpi : Function.Injective pick)
    (sep : ∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val)%k)
    (base : W k) (D : Finset (Fin s)) (hd : D.card ≤ h) :
    let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
    let C := fun i : Fin s => fun j : Fin m => if B j (pick i) then (1 : F) else 0
    ∃ (ask : Fin h → ℕ → W k →ₗ[F] F) (out : ℕ → Fin m → W k → F),
      (∀ n j, DegreeThree (out n j)) ∧
      Nat.card {z : Blocks s //
        let w := PrivateTask346FaceSpace.face ell base z
        let n := (List.finRange h).foldl (fun n a => 2*n+(if ask a n w = 0 then 0 else 1)) 0
        ∀ j, value hk u v r1 r2 c1 c2 A B w j = out n j w} =
          PrivateTask346IndependentPrice.score C D := by
  let ell := fun p : Fin s × Fin 4 => loc hk pick p.1 p.2
  let C := fun i : Fin s => fun j : Fin m => if B j (pick i) then (1 : F) else 0
  obtain ⟨q, hq, heq⟩ := face_decomposition hk h21 u v r1 r2 c1 c2 A B pick hpi sep base
  have he : Function.Injective ell := loc_injective hk h21 pick sep
  apply PrivateTask346ProtocolLift.raw_attains_score ell he base
    (value hk u v r1 r2 c1 c2 A B) C q hq
  · intro z j
    simpa only [PrivateTask346Attainment.value, C] using heq z j
  · exact hd

end PrivateTask346ActualAttainment

namespace PrivateTask346BooleanANF

abbrev F := ZMod 2
variable {ι : Type*} [DecidableEq ι]

lemma add_self_zero : ∀ a : F, a+a = 0 := by decide +kernel

def zeta (f : Finset ι → F) (S : Finset ι) : F := ∑ T ∈ S.powerset, f T

lemma zeta_add (f g : Finset ι → F) (S : Finset ι) :
    zeta (fun T => f T+g T) S = zeta f S+zeta g S := by simp [zeta,Finset.sum_add_distrib]

lemma zeta_const_mul (f : Finset ι → F) (a : F) (S : Finset ι) :
    zeta (fun T => a*f T) S = a*zeta f S := by simp [zeta,Finset.mul_sum]

lemma zeta_insert (f : Finset ι → F) {i : ι} {S : Finset ι} (hi : i ∉ S) :
    zeta f (insert i S) = zeta f S+zeta (fun T => f (insert i T)) S :=
  Finset.sum_powerset_insert hi f

theorem zeta_involution (f : Finset ι → F) (S : Finset ι) : zeta (zeta f) S = f S := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp [zeta]
  | @insert i S hi ih =>
    rw [zeta_insert (zeta f) hi]
    have he : zeta (fun T => zeta f (insert i T)) S =
        zeta (zeta f) S+zeta (zeta (fun T => f (insert i T))) S := by
      change (∑ T ∈ S.powerset, zeta f (insert i T)) =
        (∑ T ∈ S.powerset, zeta f T)+(∑ T ∈ S.powerset, zeta (fun U => f (insert i U)) T)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      exact zeta_insert f (fun h => hi ((Finset.mem_powerset.mp hT) h))
    rw [he]
    simp only [ih]
    calc
      f S+(f S+f (insert i S)) = (f S+f S)+f (insert i S) := by abel
      _ = f (insert i S) := by rw [add_self_zero,zero_add]

def zetaEquiv : (Finset ι → F) ≃ₗ[F] (Finset ι → F) where
  toFun := zeta
  invFun := zeta
  left_inv := by intro f; funext S; exact zeta_involution f S
  right_inv := by intro f; funext S; exact zeta_involution f S
  map_add' := by intro f g; funext S; exact zeta_add f g S
  map_smul' := by intro a f; funext S; exact zeta_const_mul f a S

def monomial (A B : Finset ι) : F := if A ⊆ B then 1 else 0

lemma zeta_delta (A B : Finset ι) :
    zeta (fun T : Finset ι => if T=A then 1 else 0) B = monomial A B := by
  simp [zeta,monomial,Finset.mem_powerset]

noncomputable def monomialBasis [Finite ι] : Module.Basis (Finset ι) F (Finset ι → F) :=
  (Pi.basisFun F (Finset ι)).map zetaEquiv

theorem monomialBasis_apply [Finite ι] (A B : Finset ι) :
    monomialBasis A B = monomial A B := by
  change zeta ((Pi.basisFun F (Finset ι)) A) B = monomial A B
  rw [Pi.basisFun_apply]
  unfold zeta monomial
  simp [Pi.single_apply,Finset.mem_powerset]

theorem reconstruct (f : Finset ι → F) (B : Finset ι) :
    f B = ∑ A ∈ B.powerset, zeta f A := (zeta_involution f B).symm

theorem coefficient_monomial (A B : Finset ι) :
    zeta (monomial A) B = if B=A then 1 else 0 := by
  have he : monomial A = zeta (fun T : Finset ι => if T=A then 1 else 0) := by
    funext T
    exact (zeta_delta A T).symm
  rw [he,zeta_involution]

end PrivateTask346BooleanANF

namespace PrivateTask346BooleanProduct
open PrivateTask346BooleanANF

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

lemma zeta_sum {σ : Type*} (I : Finset σ) (g : σ → Finset ι → F) (S : Finset ι) :
    zeta (fun B => ∑ i ∈ I, g i B) S = ∑ i ∈ I, zeta (g i) S := by
  unfold zeta
  rw [Finset.sum_comm]

lemma monomial_mul (A B S : Finset ι) : monomial A S * monomial B S = monomial (A ∪ B) S := by
  by_cases ha : A ⊆ S <;> by_cases hb : B ⊆ S <;>
    simp [monomial,Finset.union_subset_iff,ha,hb]

theorem set_expansion (f : Finset ι → F) (B : Finset ι) :
    f B = ∑ T : Finset ι, zeta f T * monomial T B := by
  calc
    f B = ∑ T ∈ B.powerset, zeta f T := reconstruct f B
    _ = _ := by
      simp_rw [monomial,mul_ite,mul_one,mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext T
      simp

theorem product_transform (f : Finset ι → F) (A S : Finset ι) :
    zeta (fun B => f B * monomial A B) S =
      ∑ T : Finset ι, if A ∪ T = S then zeta f T else 0 := by
  have hp : (fun B => f B * monomial A B) =
      (fun B => ∑ T : Finset ι, zeta f T * monomial (A ∪ T) B) := by
    funext B
    rw [set_expansion f B,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T hT
    rw [mul_assoc,monomial_mul]
    simp only [Finset.union_comm]
  rw [hp,zeta_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [zeta_const_mul,coefficient_monomial]
  by_cases he : A ∪ T = S
  · simp [he]
  · have hn : S ≠ A ∪ T := Ne.symm he
    simp [he,hn]

theorem product_degree_bound (d : ℕ) (f : Finset ι → F)
    (hf : ∀ T : Finset ι, d < T.card → zeta f T = 0) (A S : Finset ι)
    (hs : d+A.card < S.card) : zeta (fun B => f B * monomial A B) S = 0 := by
  rw [product_transform]
  apply Finset.sum_eq_zero
  intro T hT
  by_cases he : A ∪ T = S
  · have hc : S.card ≤ A.card+T.card := by rw [← he]; exact Finset.card_union_le _ _
    have ht : d < T.card := by omega
    simp [he,hf T ht]
  · simp [he]

theorem top_degree_product (d : ℕ) (f : Finset ι → F)
    (hf : ∀ T : Finset ι, d < T.card → zeta f T = 0) (A S : Finset ι)
    (hs : S.card = d+A.card) :
    zeta (fun B => f B * monomial A B) S =
      ∑ T : Finset ι, if Disjoint A T ∧ T.card = d ∧ A ∪ T = S then zeta f T else 0 := by
  rw [product_transform]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases he : A ∪ T = S
  · by_cases ht : T.card ≤ d
    · have hc : S.card ≤ A.card+T.card := by rw [← he]; exact Finset.card_union_le _ _
      have htd : T.card = d := by omega
      have hi := Finset.card_union_add_card_inter A T
      have hz : (A ∩ T).card = 0 := by rw [he] at hi; omega
      have hd : Disjoint A T := by
        apply Finset.disjoint_left.mpr
        intro i hiA hiT
        have hp : 0 < (A ∩ T).card := Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr ⟨hiA,hiT⟩⟩
        omega
      simp [he,htd,hd]
    · have hz := hf T (by omega)
      simp [he,hz]
  · have hn : ¬ (Disjoint A T ∧ T.card = d ∧ A ∪ T = S) := fun h => he h.2.2
    simp [he,hn]

end PrivateTask346BooleanProduct

namespace PrivateTask346FilteredIndependence

theorem independent_perturbation {K ι κ : Type*} [Field K]
    (v w : ι → κ → K) (weight : ι → ℕ) (degree : κ → ℕ)
    (hv : LinearIndependent K v)
    (homogeneous : ∀ i k, degree k ≠ weight i → v i k = 0)
    (top : ∀ i k, degree k = weight i → w i k = v i k)
    (higher : ∀ i k, weight i < degree k → w i k = 0) :
    LinearIndependent K w := by
  classical
  apply linearIndependent_iff'.mpr
  intro S c hsum i hi
  by_contra hci
  let T := S.filter fun j => c j ≠ 0
  have ht : T.Nonempty := ⟨i,by simp [T,hi,hci]⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image T weight ht
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  let U := T.filter fun l => weight l = weight j
  have hju : j ∈ U := by simp [U,hj]
  have hrel : ∑ l ∈ U, c l • v l = 0 := by
    funext k
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
    by_cases hd : degree k = weight j
    · have hh := congrArg (fun f : κ → K => f k) hsum
      have hc : (∑ l ∈ S, c l * w l k) = 0 := by
        simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hh
      calc
        (∑ l ∈ U, c l * v l k) = ∑ l ∈ S, c l * w l k := by
          dsimp [U,T]
          rw [Finset.sum_filter,Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro l hl
          by_cases hcl : c l = 0
          · simp [hcl]
          · have hlt : l ∈ T := by simp [T,hl,hcl]
            have hle := hmax l hlt
            by_cases he : weight l = weight j
            · have he' : degree k = weight l := hd.trans he.symm
              simp [hcl,he,top l k he']
            · have hw : w l k = 0 := higher l k (by omega)
              simp [hcl,he,hw]
        _ = 0 := hc
    · apply Finset.sum_eq_zero
      intro l hl
      have he : weight l = weight j := (Finset.mem_filter.mp hl).2
      rw [homogeneous l k (by omega),mul_zero]
  have hz := (linearIndependent_iff'.mp hv) U c hrel j hju
  exact hcj hz

end PrivateTask346FilteredIndependence

namespace PrivateTask346FilteredRank
open Submodule Module
open PrivateTask346FilteredIndependence

theorem finrank_span_perturbation {K ι κ : Type*} [Field K] [Finite ι] [Finite κ]
    (v w : ι → κ → K) (weight : ι → ℕ) (degree : κ → ℕ)
    (homogeneous : ∀ i k, degree k ≠ weight i → v i k = 0)
    (top : ∀ i k, degree k = weight i → w i k = v i k)
    (higher : ∀ i k, weight i < degree k → w i k = 0) :
    finrank K (span K (Set.range v)) ≤ finrank K (span K (Set.range w)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  obtain ⟨J, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  letI : Finite J := Finite.of_injective a ha
  letI : Fintype J := Fintype.ofFinite J
  have hliw : LinearIndependent K (w ∘ a) :=
    independent_perturbation (v ∘ a) (w ∘ a) (weight ∘ a) degree hli
      (fun j k => homogeneous (a j) k)
      (fun j k => top (a j) k)
      (fun j k => higher (a j) k)
  have hv : finrank K (span K (Set.range v)) = Fintype.card J := by
    rw [← hspan]
    exact finrank_span_eq_card hli
  have hw : finrank K (span K (Set.range (w ∘ a))) = Fintype.card J :=
    finrank_span_eq_card hliw
  have hsub : span K (Set.range (w ∘ a)) ≤ span K (Set.range w) := by
    apply span_mono
    rintro x ⟨j, rfl⟩
    exact ⟨a j, rfl⟩
  calc
    finrank K (span K (Set.range v)) = Fintype.card J := hv
    _ = finrank K (span K (Set.range (w ∘ a))) := hw.symm
    _ ≤ finrank K (span K (Set.range w)) := Submodule.finrank_mono hsub

end PrivateTask346FilteredRank

namespace PrivateTask346SparseLeading
open PrivateTask346BooleanANF PrivateTask346BooleanProduct

variable {κ : Type*} [DecidableEq κ] [Fintype κ] {s m : ℕ}

def equation (B : Fin s → Finset κ) (C : Fin s → Fin m → F)
    (q : Fin m → Finset κ → F) (j : Fin m) (S : Finset κ) : F :=
  (∑ i, C i j * monomial (B i) S) + q j S

def row (B : Fin s → Finset κ) (C : Fin s → Fin m → F)
    (q : Fin m → Finset κ → F) (r : Fin m × Finset κ) (S : Finset κ) : F :=
  zeta (fun T => equation B C q r.1 T * monomial r.2 T) S

def leading (B : Fin s → Finset κ) (C : Fin s → Fin m → F)
    (r : Fin m × Finset κ) (S : Finset κ) : F :=
  ∑ i, C i r.1 * if Disjoint r.2 (B i) ∧ r.2 ∪ B i = S then 1 else 0

theorem row_formula (B : Fin s → Finset κ) (C : Fin s → Fin m → F)
    (q : Fin m → Finset κ → F) (r : Fin m × Finset κ) (S : Finset κ) :
    row B C q r S =
      (∑ i, C i r.1 * if S = B i ∪ r.2 then 1 else 0) +
        zeta (fun T => q r.1 T * monomial r.2 T) S := by
  have hp : (fun T => equation B C q r.1 T * monomial r.2 T) =
      (fun T => (∑ i, C i r.1 * monomial (B i ∪ r.2) T) +
        q r.1 T * monomial r.2 T) := by
    funext T
    unfold equation
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc, monomial_mul]
  unfold row
  rw [hp, zeta_add, zeta_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [zeta_const_mul, coefficient_monomial]

theorem leading_homogeneous (B : Fin s → Finset κ) (hB : ∀ i, (B i).card = 4)
    (C : Fin s → Fin m → F) (r : Fin m × Finset κ) (S : Finset κ)
    (hne : S.card ≠ 4 + r.2.card) : leading B C r S = 0 := by
  unfold leading
  apply Finset.sum_eq_zero
  intro i hi
  have hn : ¬ (Disjoint r.2 (B i) ∧ r.2 ∪ B i = S) := by
    rintro ⟨hd, he⟩
    have hc := Finset.card_union_of_disjoint hd
    rw [he, hB] at hc
    omega
  simp [hn]

theorem row_top (B : Fin s → Finset κ) (hB : ∀ i, (B i).card = 4)
    (C : Fin s → Fin m → F) (q : Fin m → Finset κ → F)
    (hq : ∀ j S, 3 < S.card → zeta (q j) S = 0)
    (r : Fin m × Finset κ) (S : Finset κ) (hs : S.card = 4 + r.2.card) :
    row B C q r S = leading B C r S := by
  rw [row_formula, product_degree_bound 3 (q r.1) (hq r.1) r.2 S (by omega), add_zero]
  unfold leading
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have heq : (S = B i ∪ r.2) ↔ (Disjoint r.2 (B i) ∧ r.2 ∪ B i = S) := by
    constructor
    · intro he
      have hu : r.2 ∪ B i = S := by simpa [Finset.union_comm] using he.symm
      have hc := Finset.card_union_add_card_inter r.2 (B i)
      rw [hu, hB] at hc
      have hz : (r.2 ∩ B i).card = 0 := by omega
      have hd : Disjoint r.2 (B i) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have hp : 0 < (r.2 ∩ B i).card :=
          Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx, hy⟩⟩
        omega
      exact ⟨hd, hu⟩
    · rintro ⟨hd, he⟩
      simpa [Finset.union_comm] using he.symm
  simp only [heq]

theorem row_higher (B : Fin s → Finset κ) (hB : ∀ i, (B i).card = 4)
    (C : Fin s → Fin m → F) (q : Fin m → Finset κ → F)
    (hq : ∀ j S, 3 < S.card → zeta (q j) S = 0)
    (r : Fin m × Finset κ) (S : Finset κ) (hs : 4 + r.2.card < S.card) :
    row B C q r S = 0 := by
  rw [row_formula, product_degree_bound 3 (q r.1) (hq r.1) r.2 S (by omega), add_zero]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : S ≠ B i ∪ r.2 := by
    intro he
    have hc := Finset.card_union_le (B i) r.2
    rw [← he, hB] at hc
    omega
  simp [hn]

theorem independent_rows {μ : Type*} (B : Fin s → Finset κ)
    (hB : ∀ i, (B i).card = 4) (C : Fin s → Fin m → F)
    (q : Fin m → Finset κ → F) (hq : ∀ j S, 3 < S.card → zeta (q j) S = 0)
    (r : μ → Fin m × Finset κ)
    (hi : LinearIndependent F (fun u => leading B C (r u))) :
    LinearIndependent F (fun u => row B C q (r u)) := by
  apply PrivateTask346FilteredIndependence.independent_perturbation
    (fun u => leading B C (r u)) (fun u => row B C q (r u))
    (fun u => 4 + (r u).2.card) Finset.card hi
  · exact fun u S h => leading_homogeneous B hB C (r u) S h
  · exact fun u S h => row_top B hB C q hq (r u) S h
  · exact fun u S h => row_higher B hB C q hq (r u) S h

theorem rank_bound (B : Fin s → Finset κ) (hB : ∀ i, (B i).card = 4)
    (C : Fin s → Fin m → F) (q : Fin m → Finset κ → F)
    (hq : ∀ j S, 3 < S.card → zeta (q j) S = 0) :
    Module.finrank F (Submodule.span F (Set.range (leading B C))) ≤
      Module.finrank F (Submodule.span F (Set.range (row B C q))) := by
  apply PrivateTask346FilteredRank.finrank_span_perturbation
    (leading B C) (row B C q) (fun r => 4 + r.2.card) Finset.card
  · exact fun r S h => leading_homogeneous B hB C r S h
  · exact fun r S h => row_top B hB C q hq r S h
  · exact fun r S h => row_higher B hB C q hq r S h

end PrivateTask346SparseLeading

namespace PrivateTask346ZeroSetRank
open Module Submodule

theorem count_add_rank_le {K X κ ι : Type*} [Field K] [Fintype X] [Fintype κ]
    (T : (κ → K) ≃ₗ[K] (X → K)) (P : X → Prop) (v : ι → κ → K)
    (hv : ∀ i x, P x → T (v i) x = 0) :
    Nat.card {x // P x} + finrank K (span K (Set.range v)) ≤ Fintype.card κ := by
  classical
  let E : (κ → K) →ₗ[K] ({x // P x} → K) :=
    { toFun := fun f x => T f x.val
      map_add' := by intro f g; ext x; simp
      map_smul' := by intro c f; ext x; simp }
  have hsurj : Function.Surjective E := by
    intro g
    let f : X → K := fun x => if h : P x then g ⟨x, h⟩ else 0
    refine ⟨T.symm f, ?_⟩
    ext x
    simp [E, f, x.property]
  have hr : LinearMap.range E = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hs : span K (Set.range v) ≤ LinearMap.ker E := by
    apply span_le.mpr
    rintro f ⟨i, rfl⟩
    change E (v i) = 0
    ext x
    exact hv i x.val x.property
  have hd := E.finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_pi, Module.finrank_pi] at hd
  have hm := Submodule.finrank_mono hs
  rw [Nat.card_eq_fintype_card]
  omega

end PrivateTask346ZeroSetRank

namespace PrivateTask346CubicANF
open PrivateTask346BooleanANF
open PrivateTask346AffineCubic (delta DegreeThree)

variable {ι : Type*} [DecidableEq ι]

lemma sub_eq_add : ∀ a b : F, a-b = a+b := by decide +kernel
lemma field_cases : ∀ a : F, a=0 ∨ a=1 := by decide +kernel

def point (S : Finset ι) : ι → F := fun i => if i ∈ S then 1 else 0
def unit (i : ι) : ι → F := fun j => if j=i then 1 else 0

lemma point_empty : point (∅ : Finset ι) = 0 := by funext i; simp [point]

lemma point_insert (i : ι) (S : Finset ι) (hi : i ∉ S) :
    point (insert i S) = point S+unit i := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [point,unit,hi]
  · simp [point,unit,hj]

def coefficient (f : (ι → F) → F) (S : Finset ι) : F := zeta (fun T => f (point T)) S

lemma coefficient_insert (f : (ι → F) → F) {i : ι} {S : Finset ι} (hi : i ∉ S) :
    coefficient f (insert i S) = coefficient (delta f (unit i)) S := by
  unfold coefficient
  rw [zeta_insert _ hi]
  have he : zeta (fun T => delta f (unit i) (point T)) S =
      zeta (fun T => f (point (insert i T))) S+zeta (fun T => f (point T)) S := by
    change (∑ T ∈ S.powerset, delta f (unit i) (point T)) =
      (∑ T ∈ S.powerset, f (point (insert i T)))+(∑ T ∈ S.powerset, f (point T))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    have hit : i ∉ T := fun h => hi ((Finset.mem_powerset.mp hT) h)
    unfold delta
    rw [← point_insert i T hit,sub_eq_add]
  rw [he]
  exact add_comm _ _

theorem coefficient_list (xs : List ι) : ∀ f : (ι → F) → F, xs.Nodup →
    coefficient f xs.toFinset = ((xs.map unit).foldl delta f) 0 := by
  induction xs with
  | nil => intro f hn; simp [coefficient,zeta,point_empty]
  | cons i xs ih =>
    intro f hn
    have hi : i ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    rw [List.toFinset_cons,coefficient_insert f hi]
    simpa only [List.map_cons,List.foldl_cons] using ih (delta f (unit i)) ht

theorem coefficient_differences (f : (ι → F) → F) (S : Finset ι) :
    coefficient f S = ((S.toList.map unit).foldl delta f) 0 := by
  simpa using coefficient_list S.toList f (Finset.nodup_toList S)

lemma fold_zero (vs : List (ι → F)) : vs.foldl delta (fun _ : ι → F => 0) = fun _ => 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hz : delta (fun _ : ι → F => 0) v = fun _ => 0 := by funext x; simp [delta]
    rw [List.foldl_cons,hz]
    exact ih

theorem fold_zero_of_cubic (f : (ι → F) → F) (hf : DegreeThree f) (vs : List (ι → F))
    (hlen : 4 ≤ vs.length) : vs.foldl delta f = fun _ => 0 := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d,rest⟩⟩⟩⟩ <;> try simp at hlen
  have h4 : ([a,b,c,d].foldl delta f) = fun _ => 0 := by
    funext x
    simpa [List.ofFn_succ] using hf ![a,b,c,d] x
  change rest.foldl delta ([a,b,c,d].foldl delta f) = fun _ => 0
  rw [h4,fold_zero]

theorem cubic_coefficient_zero (f : (ι → F) → F) (hf : DegreeThree f) (S : Finset ι)
    (hs : 4 ≤ S.card) : coefficient f S = 0 := by
  rw [coefficient_differences,fold_zero_of_cubic f hf _ (by simpa using hs)]

section Finite
variable [Fintype ι]

def ones (x : ι → F) : Finset ι := Finset.univ.filter fun i => x i = 1

lemma point_ones (x : ι → F) : point (ones x) = x := by
  funext i
  obtain hi | hi := field_cases (x i) <;> simp [point,ones,hi]

lemma monomial_prod (S : Finset ι) (x : ι → F) : monomial S (ones x) = ∏ i ∈ S, x i := by
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    obtain hx | hx := field_cases (x i)
    · rw [hx,zero_mul]
      have hn : ¬ insert i S ⊆ ones x := by
        intro h
        have hit := h (Finset.mem_insert_self i S)
        simp [ones,hx] at hit
      simp [monomial,hn]
    · rw [hx,one_mul]
      have he : insert i S ⊆ ones x ↔ S ⊆ ones x := by
        rw [Finset.insert_subset_iff]
        simp [ones,hx]
      simpa only [monomial,he] using ih

theorem full_expansion (f : (ι → F) → F) (x : ι → F) :
    f x = ∑ S : Finset ι, coefficient f S * ∏ i ∈ S, x i := by
  have h := reconstruct (fun T : Finset ι => f (point T)) (ones x)
  rw [point_ones] at h
  calc
    f x = ∑ S ∈ (ones x).powerset, coefficient f S := h
    _ = ∑ S : Finset ι, coefficient f S * monomial S (ones x) := by
      simp_rw [monomial,mul_ite,mul_one,mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext S
      simp
    _ = _ := by simp_rw [monomial_prod]

theorem cubic_expansion (f : (ι → F) → F) (hf : DegreeThree f) (x : ι → F) :
    f x = ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ 3).sum
      (fun S => coefficient f S * ∏ i ∈ S, x i) := by
  rw [full_expansion f x,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hs : S.card ≤ 3
  · simp [hs]
  · have hz := cubic_coefficient_zero f hf S (by omega)
    simp [hs,hz]

end Finite
end PrivateTask346CubicANF

namespace PrivateTask346CodeUpperRank
open PrivateTask346BooleanANF PrivateTask346SparseLeading
open Module Submodule

variable {κ : Type*} [DecidableEq κ] [Fintype κ] {s m : ℕ}

theorem set_count_add_rank_le (B : Fin s → Finset κ) (hB : ∀ i, (B i).card = 4)
    (C : Fin s → Fin m → F) (q : Fin m → Finset κ → F)
    (hq : ∀ j S, 3 < S.card → zeta (q j) S = 0) :
    Nat.card {S : Finset κ // ∀ j, equation B C q j S = 0} +
      finrank F (span F (Set.range (leading B C))) ≤ 2 ^ Fintype.card κ := by
  have hv := PrivateTask346ZeroSetRank.count_add_rank_le
    (zetaEquiv : (Finset κ → F) ≃ₗ[F] (Finset κ → F))
    (fun S => ∀ j, equation B C q j S = 0) (row B C q) (by
      intro r S hS
      change zeta (zeta (fun T => equation B C q r.1 T * monomial r.2 T)) S = 0
      rw [zeta_involution, hS r.1, zero_mul])
  have hr := rank_bound B hB C q hq
  have hc : Fintype.card (Finset κ) = 2 ^ Fintype.card κ := Fintype.card_finset
  omega

def pointEquiv : Finset κ ≃ (κ → F) where
  toFun := PrivateTask346CubicANF.point
  invFun := PrivateTask346CubicANF.ones
  left_inv := by
    intro S
    ext i
    simp [PrivateTask346CubicANF.ones, PrivateTask346CubicANF.point]
  right_inv := PrivateTask346CubicANF.point_ones

def observation (B : Fin s → Finset κ) (C : Fin s → Fin m → F)
    (q : Fin m → (κ → F) → F) (j : Fin m) (x : κ → F) : F :=
  (∑ i, C i j * ∏ a ∈ B i, x a) + q j x

theorem cubic_count_add_rank_le (B : Fin s → Finset κ)
    (hB : ∀ i, (B i).card = 4) (C : Fin s → Fin m → F)
    (q : Fin m → (κ → F) → F) (hq : ∀ j, PrivateTask346AffineCubic.DegreeThree (q j)) :
    Nat.card {x : κ → F // ∀ j, observation B C q j x = 0} +
      finrank F (span F (Set.range (leading B C))) ≤ 2 ^ Fintype.card κ := by
  let qS : Fin m → Finset κ → F := fun j S => q j (PrivateTask346CubicANF.point S)
  have hqS : ∀ j S, 3 < S.card → zeta (qS j) S = 0 := by
    intro j S hS
    exact PrivateTask346CubicANF.cubic_coefficient_zero (q j) (hq j) S (by omega)
  have hobs (j : Fin m) (S : Finset κ) :
      equation B C qS j S = observation B C q j (pointEquiv S) := by
    have he : PrivateTask346CubicANF.ones (pointEquiv S) = S := pointEquiv.left_inv S
    unfold equation observation
    simp_rw [← PrivateTask346CubicANF.monomial_prod, he]
    rfl
  let e : {S : Finset κ // ∀ j, equation B C qS j S = 0} ≃
      {x : κ → F // ∀ j, observation B C q j x = 0} :=
    pointEquiv.subtypeEquiv (by intro S; simp only [hobs])
  have hc := Nat.card_congr e
  have hb := set_count_add_rank_le B hB C qS hqS
  omega

theorem cubic_count_le_of_rank (B : Fin s → Finset κ)
    (hB : ∀ i, (B i).card = 4) (C : Fin s → Fin m → F)
    (q : Fin m → (κ → F) → F) (hq : ∀ j, PrivateTask346AffineCubic.DegreeThree (q j))
    (N : ℕ) (hr : 2 ^ Fintype.card κ ≤ finrank F (span F (Set.range (leading B C))) + N) :
    Nat.card {x : κ → F // ∀ j, observation B C q j x = 0} ≤ N := by
  have h := cubic_count_add_rank_le B hB C q hq
  omega

end PrivateTask346CodeUpperRank

namespace PrivateTask346NilpotentElimination
open PrivateTask346AffineCubic

variable {V ι : Type*} [AddCommGroup V] [Module F V]

lemma add_self_zero (v : V) : v+v=0 := by
  calc
    v+v = (1+1 : F) • v := by rw [add_smul, one_smul]
    _ = 0 := by
      have h : (1+1 : F)=0 := by decide +kernel
      rw [h, zero_smul]

def jointKernel (B : ι → V →ₗ[F] V) : Submodule F V := ⨅ j, LinearMap.ker (B j)

lemma mem_jointKernel (B : ι → V →ₗ[F] V) (v : V) :
    v ∈ jointKernel B ↔ ∀ j, B j v=0 := by simp [jointKernel]

def coupledKernel (Q : V →ₗ[F] V) (B : ι → V →ₗ[F] V) : Submodule F (V × V) :=
  LinearMap.ker (LinearMap.fst F V V + LinearMap.snd F V V + Q.comp (LinearMap.fst F V V)) ⊓
    (LinearMap.ker (LinearMap.fst F V V + LinearMap.snd F V V + Q.comp (LinearMap.snd F V V)) ⊓
      ⨅ j, LinearMap.ker ((B j).comp (LinearMap.fst F V V)) ⊓
        LinearMap.ker ((B j).comp (LinearMap.snd F V V)))

lemma mem_coupledKernel (Q : V →ₗ[F] V) (B : ι → V →ₗ[F] V) (v : V × V) :
    v ∈ coupledKernel Q B ↔
      v.1+v.2+Q v.1=0 ∧ v.1+v.2+Q v.2=0 ∧ ∀ j, B j v.1=0 ∧ B j v.2=0 := by
  simp [coupledKernel]

theorem graph_mem (Q : V →ₗ[F] V) (B : ι → V →ₗ[F] V)
    (hQ : ∀ v, Q (Q v)=0) (hc : ∀ j v, B j (Q v)=Q (B j v))
    (v : jointKernel B) : ((v : V), (v : V)+Q v) ∈ coupledKernel Q B := by
  rw [mem_coupledKernel]
  have hb := (mem_jointKernel B v).mp v.property
  have h0 : (v : V)+((v : V)+Q v)+Q v=0 := by
    calc
      _ = ((v : V)+(v : V))+(Q v+Q v) := by abel
      _ = 0 := by rw [add_self_zero, add_self_zero, add_zero]
  refine ⟨h0, ?_, ?_⟩
  · simpa only [map_add, hQ, add_zero] using h0
  · intro j
    refine ⟨hb j, ?_⟩
    rw [map_add, hc, hb, map_zero, zero_add]

noncomputable def eliminate (Q : V →ₗ[F] V) (B : ι → V →ₗ[F] V)
    (hQ : ∀ v, Q (Q v)=0) (hc : ∀ j v, B j (Q v)=Q (B j v)) :
    jointKernel B ≃ₗ[F] coupledKernel Q B where
  toFun := fun v => ⟨((v : V), (v : V)+Q v), graph_mem Q B hQ hc v⟩
  invFun := fun v => ⟨v.val.1, (mem_jointKernel B _).mpr
    (fun j => ((mem_coupledKernel Q B _).mp v.property).2.2 j |>.1)⟩
  left_inv := by intro v; rfl
  right_inv := by
    intro v
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hz := ((mem_coupledKernel Q B _).mp v.property).1
      have hh : v.val.2+(v.val.1+Q v.val.1) =
          (v.val.1+Q v.val.1)+(v.val.1+Q v.val.1) := by
        calc
          _ = v.val.1+v.val.2+Q v.val.1 := by abel
          _ = 0 := hz
          _ = _ := (add_self_zero _).symm
      exact (add_right_cancel hh).symm
  map_add' := by
    intro v w
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (v : V)+(w : V)+Q ((v : V)+(w : V)) = (v : V)+Q v+((w : V)+Q w)
      rw [map_add]
      abel
  map_smul' := by
    intro c v
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change c • (v : V)+Q (c • (v : V)) = c • ((v : V)+Q v)
      rw [map_smul, smul_add]

theorem finrank_eliminate (Q : V →ₗ[F] V) (B : ι → V →ₗ[F] V)
    (hQ : ∀ v, Q (Q v)=0) (hc : ∀ j v, B j (Q v)=Q (B j v)) :
    Module.finrank F (coupledKernel Q B) = Module.finrank F (jointKernel B) :=
  (eliminate Q B hQ hc).finrank_eq.symm

end PrivateTask346NilpotentElimination

namespace PrivateTask346LeadingKernel
open PrivateTask346BooleanANF PrivateTask346SparseLeading PrivateTask346NilpotentElimination
open Module

variable {κ : Type*} [DecidableEq κ] [Fintype κ] {s m : ℕ}

def lowerBlock (B : Finset κ) : (Finset κ → F) →ₗ[F] (Finset κ → F) where
  toFun := fun f A => if Disjoint A B then f (A ∪ B) else 0
  map_add' := by intro f g; funext A; by_cases h : Disjoint A B <;> simp [h]
  map_smul' := by intro c f; funext A; by_cases h : Disjoint A B <;> simp [h]

def codedLower (B : Fin s → Finset κ) (C : Fin s → Fin m → F) (j : Fin m) :
    (Finset κ → F) →ₗ[F] (Finset κ → F) := ∑ i, C i j • lowerBlock (B i)

def leadingMatrix (B : Fin s → Finset κ) (C : Fin s → Fin m → F) :
    Matrix (Fin m × Finset κ) (Finset κ) F := leading B C

theorem mulVec_lower (B : Fin s → Finset κ) (C : Fin s → Fin m → F)
    (f : Finset κ → F) (j : Fin m) (A : Finset κ) :
    (leadingMatrix B C).mulVecLin f (j,A)=codedLower B C j f A := by
  change (∑ S : Finset κ, (∑ i : Fin s, C i j *
    (if Disjoint A (B i) ∧ A ∪ B i=S then 1 else 0)) * f S)=_
  simp only [codedLower, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, lowerBlock, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : Disjoint A (B i)
  · simp [hd, mul_ite, ite_mul, eq_comm]
  · simp [hd]

theorem kernel_matrix (B : Fin s → Finset κ) (C : Fin s → Fin m → F) :
    LinearMap.ker (leadingMatrix B C).mulVecLin=jointKernel (codedLower B C) := by
  ext f
  rw [LinearMap.mem_ker, mem_jointKernel]
  constructor
  · intro h j
    funext A
    have hh := congrFun h (j,A)
    simpa only [mulVec_lower, Pi.zero_apply] using hh
  · intro h
    funext r
    rcases r with ⟨j,A⟩
    rw [mulVec_lower]
    exact congrFun (h j) A

theorem leading_rank_nullity (B : Fin s → Finset κ) (C : Fin s → Fin m → F) :
    finrank F (Submodule.span F (Set.range (leading B C))) +
      finrank F (jointKernel (codedLower B C))=2 ^ Fintype.card κ := by
  have h := (leadingMatrix B C).mulVecLin.finrank_range_add_finrank_ker
  change (leadingMatrix B C).rank + finrank F (LinearMap.ker (leadingMatrix B C).mulVecLin)=
    finrank F (Finset κ → F) at h
  rw [Matrix.rank_eq_finrank_span_row, kernel_matrix, Module.finrank_pi, Fintype.card_finset] at h
  exact h

theorem cubic_count_le_kernel (B : Fin s → Finset κ) (hB : ∀ i, (B i).card=4)
    (C : Fin s → Fin m → F) (q : Fin m → (κ → F) → F)
    (hq : ∀ j, PrivateTask346AffineCubic.DegreeThree (q j)) :
    Nat.card {x : κ → F // ∀ j, PrivateTask346CodeUpperRank.observation B C q j x=0} ≤
      finrank F (jointKernel (codedLower B C)) := by
  have h1 := PrivateTask346CodeUpperRank.cubic_count_add_rank_le B hB C q hq
  have h2 := leading_rank_nullity B C
  omega

end PrivateTask346LeadingKernel

namespace PrivateTask346Derivatives
open PrivateTask346AffineCubic PrivateTask346NilpotentElimination

variable {U : Type*} [AddCommGroup U] [Module F U]

def derivative (v : U) : (U → F) →ₗ[F] (U → F) where
  toFun := fun f x => f (x+v)+f x
  map_add' := by intro f g; funext x; simp only [Pi.add_apply]; ring
  map_smul' := by
    intro c f
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem derivative_square (v : U) (f : U → F) : derivative v (derivative v f)=0 := by
  funext x
  have he : (x+v)+v=x := by rw [add_assoc, add_self_zero, add_zero]
  change (f ((x+v)+v)+f (x+v))+(f (x+v)+f x)=0
  rw [he]
  calc
    _ = (f x+f x)+(f (x+v)+f (x+v)) := by abel
    _ = 0 := by rw [add_self_zero, add_self_zero, add_zero]

theorem derivative_commute (v w : U) (f : U → F) :
    derivative v (derivative w f)=derivative w (derivative v f) := by
  funext x
  have he : (x+v)+w=(x+w)+v := by abel
  change (f ((x+v)+w)+f (x+v))+(f (x+w)+f x) =
    (f ((x+w)+v)+f (x+w))+(f (x+v)+f x)
  rw [he]
  abel

variable {V σ : Type*} [AddCommGroup V] [Module F V]

theorem sum_square_zero (T : σ → V →ₗ[F] V) (S : Finset σ) :
    (∀ i ∈ S, ∀ v, T i (T i v)=0) →
    (∀ i ∈ S, ∀ j ∈ S, ∀ v, T i (T j v)=T j (T i v)) →
    ∀ v, (∑ i ∈ S, T i) ((∑ i ∈ S, T i) v)=0 := by
  classical
  induction S using Finset.induction_on with
  | empty => intro hs hc v; simp
  | @insert i S hi ih =>
    intro hs hc v
    let Q : V →ₗ[F] V := ∑ j ∈ S, T j
    have hQ : ∀ v, Q (Q v)=0 := ih
      (fun j hj => hs j (Finset.mem_insert_of_mem hj))
      (fun j hj l hl => hc j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl))
    have hcomm : T i (Q v)=Q (T i v) := by
      simp only [Q, LinearMap.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact hc i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj) v
    rw [Finset.sum_insert hi]
    change T i (T i v+Q v)+Q (T i v+Q v)=0
    rw [map_add, map_add, hs i (Finset.mem_insert_self i S), hQ,
      zero_add, add_zero, hcomm]
    exact add_self_zero _

theorem weighted_square_zero (T : σ → V →ₗ[F] V) (S : Finset σ) (c : σ → F)
    (hs : ∀ i ∈ S, ∀ v, T i (T i v)=0)
    (hc : ∀ i ∈ S, ∀ j ∈ S, ∀ v, T i (T j v)=T j (T i v)) :
    ∀ v, (∑ i ∈ S, c i • T i) ((∑ i ∈ S, c i • T i) v)=0 := by
  apply sum_square_zero
  · intro i hi v
    change c i • T i (c i • T i v)=0
    rw [map_smul, hs i hi, smul_zero, smul_zero]
  · intro i hi j hj v
    change c i • T i (c j • T j v)=c j • T j (c i • T i v)
    rw [map_smul, map_smul, hc i hi j hj]
    exact smul_comm _ _ _

theorem weighted_commute (T : σ → V →ₗ[F] V) (S : Finset σ) (c d : σ → F)
    (hc : ∀ i ∈ S, ∀ j ∈ S, ∀ v, T i (T j v)=T j (T i v)) (v : V) :
    (∑ i ∈ S, c i • T i) ((∑ i ∈ S, d i • T i) v) =
      (∑ i ∈ S, d i • T i) ((∑ i ∈ S, c i • T i) v) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi j hj]
  exact smul_comm _ _ _

end PrivateTask346Derivatives

namespace PrivateTask346LiftedElimination
open PrivateTask346AffineCubic PrivateTask346NilpotentElimination

variable {V ι : Type*} [AddCommGroup V] [Module F V]

def lifted (a : F) (Q : V →ₗ[F] V) : (V × V) →ₗ[F] (V × V) :=
  (a • (LinearMap.fst F V V + LinearMap.snd F V V) + Q.comp (LinearMap.fst F V V)).prod
    (a • (LinearMap.fst F V V + LinearMap.snd F V V) + Q.comp (LinearMap.snd F V V))

lemma lifted_apply (a : F) (Q : V →ₗ[F] V) (v : V × V) :
    lifted a Q v = (a • (v.1+v.2)+Q v.1, a • (v.1+v.2)+Q v.2) := rfl

lemma eq_of_add_zero (a b : V) (h : a+b=0) : a=b :=
  by exact add_right_cancel (h.trans (add_self_zero b).symm)

lemma mem_lifted (a : ι → F) (Q : ι → V →ₗ[F] V) (v : V × V) :
    v ∈ jointKernel (fun j => lifted (a j) (Q j)) ↔
      ∀ j, a j • (v.1+v.2)+Q j v.1=0 ∧ a j • (v.1+v.2)+Q j v.2=0 := by
  rw [mem_jointKernel]
  apply forall_congr'
  intro j
  rw [lifted_apply]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h0, h1⟩
    exact Prod.ext h0 h1

theorem kernel_row_elimination (a : ι → F) (Q : ι → V →ₗ[F] V) (p : ι) (hp : a p=1) :
    jointKernel (fun j => lifted (a j) (Q j)) =
      coupledKernel (Q p) (fun j => Q j+a j • Q p) := by
  ext v
  rw [mem_lifted, mem_coupledKernel]
  constructor
  · intro h
    have h0 := (h p).1
    have h1 := (h p).2
    rw [hp, one_smul] at h0 h1
    have d0 := eq_of_add_zero _ _ h0
    have d1 := eq_of_add_zero _ _ h1
    refine ⟨h0, h1, ?_⟩
    intro j
    constructor
    · have hj := (h j).1
      rw [d0] at hj
      change Q j v.1+a j • Q p v.1=0
      simpa only [add_comm] using hj
    · have hj := (h j).2
      rw [d1] at hj
      change Q j v.2+a j • Q p v.2=0
      simpa only [add_comm] using hj
  · rintro ⟨h0, h1, hB⟩
    have d0 := eq_of_add_zero _ _ h0
    have d1 := eq_of_add_zero _ _ h1
    intro j
    constructor
    · rw [d0]
      have hj := (hB j).1
      change Q j v.1+a j • Q p v.1=0 at hj
      simpa only [add_comm] using hj
    · rw [d1]
      have hj := (hB j).2
      change Q j v.2+a j • Q p v.2=0 at hj
      simpa only [add_comm] using hj

theorem finrank_row_elimination (a : ι → F) (Q : ι → V →ₗ[F] V) (p : ι) (hp : a p=1)
    (hsq : ∀ v, Q p (Q p v)=0) (hc : ∀ j v, Q j (Q p v)=Q p (Q j v)) :
    Module.finrank F (jointKernel (fun j => lifted (a j) (Q j))) =
      Module.finrank F (jointKernel (fun j => Q j+a j • Q p)) := by
  rw [kernel_row_elimination a Q p hp]
  apply finrank_eliminate
  · exact hsq
  · intro j v
    change Q j (Q p v)+a j • Q p (Q p v) = Q p (Q j v+a j • Q p v)
    rw [hc, map_add, map_smul]

end PrivateTask346LiftedElimination

namespace PrivateTask346RegularSlices
open PrivateTask346AffineCubic PrivateTask346Derivatives PrivateTask346LiftedElimination

abbrev Cube (n : ℕ) := Fin n → F

def unit {n : ℕ} (i : Fin n) : Cube n := Pi.single i 1

def coded {n : ℕ} (c : Fin n → F) : (Cube n → F) →ₗ[F] (Cube n → F) :=
  ∑ i, c i • derivative (unit i)

theorem coded_add {n : ℕ} (c d : Fin n → F) :
    coded (fun i => c i+d i)=coded c+coded d := by
  simp only [coded, add_smul, Finset.sum_add_distrib]

theorem coded_mul {n : ℕ} (a : F) (c : Fin n → F) :
    coded (fun i => a*c i)=a • coded c := by
  simp only [coded, Finset.smul_sum, smul_smul]

theorem coded_square {n : ℕ} (c : Fin n → F) (f : Cube n → F) : coded c (coded c f)=0 := by
  exact weighted_square_zero (fun i : Fin n => derivative (unit i)) Finset.univ c
    (fun i _ => derivative_square (unit i))
    (fun i _ j _ => derivative_commute (unit i) (unit j)) f

theorem coded_commute {n : ℕ} (c d : Fin n → F) (f : Cube n → F) :
    coded c (coded d f)=coded d (coded c f) := by
  exact weighted_commute (fun i : Fin n => derivative (unit i)) Finset.univ c d
    (fun i _ j _ => derivative_commute (unit i) (unit j)) f

def sliceEquiv (n : ℕ) : (Cube (n+1) → F) ≃ₗ[F] ((Cube n → F) × (Cube n → F)) where
  toFun := fun f => (fun x => f (Fin.cons 0 x), fun x => f (Fin.cons 1 x))
  invFun := fun p x => if x 0=0 then p.1 (Fin.tail x) else p.2 (Fin.tail x)
  left_inv := by
    intro f
    funext x
    change (if x 0=0 then f (Fin.cons 0 (Fin.tail x)) else f (Fin.cons 1 (Fin.tail x)))=f x
    obtain hx | hx := PrivateTask346OneFace.field_cases (x 0)
    · rw [if_pos hx]
      apply congrArg f
      rw [← hx]
      exact Fin.cons_self_tail x
    · rw [if_neg (by rw [hx]; decide)]
      apply congrArg f
      rw [← hx]
      exact Fin.cons_self_tail x
  right_inv := by
    intro p
    apply Prod.ext <;> funext x <;> simp
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl

lemma sliceEquiv_apply (n : ℕ) (f : Cube (n+1) → F) :
    sliceEquiv n f = (fun x => f (Fin.cons 0 x), fun x => f (Fin.cons 1 x)) := rfl

theorem unit_zero_cons {n : ℕ} (b : F) (x : Cube n) :
    Fin.cons b x + unit (0 : Fin (n+1))=Fin.cons (b+1) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [unit, Pi.single_apply]
  · simp [unit, Pi.single_apply]

theorem unit_succ_cons {n : ℕ} (b : F) (x : Cube n) (i : Fin n) :
    Fin.cons b x + unit i.succ=Fin.cons b (x+unit i) := by
  funext j
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [unit, Pi.single_apply]
  · simp [unit, Pi.single_apply, Fin.succ_inj]

theorem coded_at_cons {n : ℕ} (c : Fin (n+1) → F) (f : Cube (n+1) → F) (b : F) (x : Cube n) :
    coded c f (Fin.cons b x) =
      c 0 * (f (Fin.cons (b+1) x)+f (Fin.cons b x)) +
        ∑ i : Fin n, c i.succ * (f (Fin.cons b (x+unit i))+f (Fin.cons b x)) := by
  unfold coded
  rw [Fin.sum_univ_succ]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, derivative, LinearMap.coe_mk, AddHom.coe_mk]
  rw [unit_zero_cons]
  simp_rw [unit_succ_cons]

theorem split_coded {n : ℕ} (c : Fin (n+1) → F) (f : Cube (n+1) → F) :
    sliceEquiv n (coded c f) = lifted (c 0) (coded (fun i : Fin n => c i.succ)) (sliceEquiv n f) := by
  have h11 : (1+1 : F)=0 := by decide +kernel
  rw [lifted_apply]
  apply Prod.ext
  · funext x
    change coded c f (Fin.cons 0 x) = _
    rw [coded_at_cons]
    simp only [sliceEquiv_apply, coded, derivative,
      LinearMap.sum_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, zero_add]
    ring
  · funext x
    change coded c f (Fin.cons 1 x) = _
    rw [coded_at_cons]
    simp only [sliceEquiv_apply, coded, derivative,
      LinearMap.sum_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, h11]

end PrivateTask346RegularSlices

namespace PrivateTask346BlockComponents
open PrivateTask346BooleanANF

abbrev Local := Finset (Fin 4)
abbrev Partial := {S : Local // S ≠ ∅ ∧ S ≠ Finset.univ}
abbrev Label := Option Partial

def classify (S : Local) : Label :=
  if he : S=∅ then none else if hf : S=Finset.univ then none else some ⟨S, he, hf⟩

def bit (S : Local) : F := if S=Finset.univ then 1 else 0

def decode : Label → F → Local
  | none, b => if b=0 then ∅ else Finset.univ
  | some p, _ => p.val

theorem decode_classify : ∀ S : Local, decode (classify S) (bit S)=S := by decide +kernel
theorem classify_decode : ∀ l : Label, ∀ b : F, classify (decode l b)=l := by decide +kernel
theorem bit_decode_none : ∀ b : F, bit (decode none b)=b := by decide +kernel
theorem bit_inactive : ∀ S : Local, classify S ≠ none → bit S=0 := by decide +kernel
theorem decode_empty : ∀ l : Label, ∀ b : F, decode l b=∅ ↔ l=none ∧ b=0 := by decide +kernel
theorem decode_full : ∀ l : Label, ∀ b : F, decode l b=Finset.univ ↔ l=none ∧ b=1 := by decide +kernel

abbrev States (s : ℕ) := Fin s → Local
abbrev Components (s : ℕ) := Fin s → Label
abbrev Active {s : ℕ} (ω : Components s) := {i : Fin s // ω i=none}

def component {s : ℕ} (T : States s) : Components s := fun i => classify (T i)

def restore {s : ℕ} (ω : Components s) (b : Active ω → F) (i : Fin s) : Local :=
  decode (ω i) (if h : ω i=none then b ⟨i,h⟩ else 0)

theorem restore_component {s : ℕ} (ω : Components s) (b : Active ω → F) :
    component (restore ω b)=ω := by
  funext i
  exact classify_decode (ω i) _

theorem restore_bit {s : ℕ} (ω : Components s) (b : Active ω → F) (i : Active ω) :
    bit (restore ω b i.val)=b i := by
  have he : restore ω b i.val=decode none (b i) := by simp [restore, i.property]
  rw [he, bit_decode_none]

def restoreAll {s : ℕ} (p : Σ ω : Components s, Active ω → F) : States s := restore p.1 p.2

theorem restore_injective (s : ℕ) : Function.Injective (@restoreAll s) := by
  rintro ⟨ω,b⟩ ⟨ω',b'⟩ he
  have hw : ω=ω' := by
    have h := congrArg component he
    simpa only [restoreAll, restore_component] using h
  subst ω'
  have hb : b=b' := by
    funext i
    have h := congrArg (fun T : States s => bit (T i.val)) he
    simpa only [restoreAll, restore_bit] using h
  subst b'
  rfl

theorem restore_surjective (s : ℕ) : Function.Surjective (@restoreAll s) := by
  intro T
  refine ⟨⟨component T, fun i => bit (T i.val)⟩, ?_⟩
  funext i
  change decode (classify (T i)) (if h : classify (T i)=none then bit (T i) else 0)=T i
  by_cases h : classify (T i)=none
  · rw [dif_pos h]
    exact decode_classify (T i)
  · rw [dif_neg h, ← bit_inactive (T i) h]
    exact decode_classify (T i)

noncomputable def componentEquiv (s : ℕ) : States s ≃ (Σ ω : Components s, Active ω → F) :=
  (Equiv.ofBijective (@restoreAll s) ⟨restore_injective s, restore_surjective s⟩).symm

noncomputable def functionComponents (s : ℕ) :
    (States s → F) ≃ₗ[F] (∀ ω : Components s, (Active ω → F) → F) :=
  (LinearEquiv.piCongrLeft' F (fun _ : States s => F) (componentEquiv s)).trans
    (LinearEquiv.piCurry F (fun _ _ => F))

theorem component_function_apply (s : ℕ) (f : States s → F)
    (ω : Components s) (b : Active ω → F) : functionComponents s f ω b=f (restore ω b) := rfl

theorem restore_empty_iff {s : ℕ} (ω : Components s) (b : Active ω → F) (i : Fin s) :
    restore ω b i=∅ ↔ ∃ h : ω i=none, b ⟨i,h⟩=0 := by
  by_cases h : ω i=none
  · simp [restore, h, decode_empty]
  · simp [restore, h, decode_empty]

end PrivateTask346BlockComponents

namespace PrivateTask346SubsetBlocks
open PrivateTask346BooleanANF PrivateTask346BlockComponents PrivateTask346LeadingKernel

def wholeBlock {s : ℕ} (i : Fin s) : Finset (Fin s × Fin 4) :=
  Finset.univ.image (fun a : Fin 4 => (i,a))

def fibres {s : ℕ} (A : Finset (Fin s × Fin 4)) : States s :=
  fun i => Finset.univ.filter (fun a => (i,a) ∈ A)

def assemble {s : ℕ} (T : States s) : Finset (Fin s × Fin 4) :=
  Finset.univ.biUnion (fun i => (T i).image (fun a => (i,a)))

def fibresEquiv (s : ℕ) : Finset (Fin s × Fin 4) ≃ States s where
  toFun := fibres
  invFun := assemble
  left_inv := by
    intro A
    ext p
    rcases p with ⟨i,a⟩
    simp [assemble, fibres]
  right_inv := by
    intro T
    funext i
    ext a
    simp [assemble, fibres]

theorem block_card {s : ℕ} (i : Fin s) : (wholeBlock i).card=4 := by
  have hi : Function.Injective (fun a : Fin 4 => (i,a)) := fun a b h => congrArg Prod.snd h
  simpa [wholeBlock] using Finset.card_image_of_injective Finset.univ hi

theorem disjoint_iff {s : ℕ} (A : Finset (Fin s × Fin 4)) (i : Fin s) :
    Disjoint A (wholeBlock i) ↔ fibres A i=∅ := by
  constructor
  · intro h
    ext a
    constructor
    · intro ha
      have hp : (i,a) ∈ A := (Finset.mem_filter.mp ha).2
      have hb : (i,a) ∈ wholeBlock i := by simp [wholeBlock]
      exact ((Finset.disjoint_left.mp h) hp hb).elim
    · intro ha
      simp at ha
  · intro h
    apply Finset.disjoint_left.mpr
    intro p hp hb
    obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hb
    subst p
    have hm : a ∈ fibres A i := by simp [fibres, hp]
    rw [h] at hm
    simp at hm

theorem fibres_union {s : ℕ} (A : Finset (Fin s × Fin 4)) (i : Fin s) :
    fibres (A ∪ wholeBlock i)=Function.update (fibres A) i Finset.univ := by
  funext j
  ext a
  by_cases hj : j=i
  · subst j
    simp [fibres, wholeBlock]
  · simp [fibres, wholeBlock, Function.update, hj, Ne.symm hj]

noncomputable def functionEquiv (s : ℕ) :
    (Finset (Fin s × Fin 4) → F) ≃ₗ[F] (States s → F) :=
  LinearEquiv.piCongrLeft' F (fun _ : Finset (Fin s × Fin 4) => F) (fibresEquiv s)

lemma functionEquiv_apply (s : ℕ) (f : Finset (Fin s × Fin 4) → F) (T : States s) :
    functionEquiv s f T=f ((fibresEquiv s).symm T) := rfl

lemma functionEquiv_fibres (s : ℕ) (f : Finset (Fin s × Fin 4) → F) (A : Finset (Fin s × Fin 4)) :
    functionEquiv s f (fibres A)=f A := by
  change f ((fibresEquiv s).symm (fibresEquiv s A))=f A
  rw [Equiv.symm_apply_apply]

def stateLower {s : ℕ} (i : Fin s) : (States s → F) →ₗ[F] (States s → F) where
  toFun := fun f T => if T i=∅ then f (Function.update T i Finset.univ) else 0
  map_add' := by intro f g; funext T; by_cases h : T i=∅ <;> simp [h]
  map_smul' := by intro c f; funext T; by_cases h : T i=∅ <;> simp [h]

theorem transform_lower {s : ℕ} (i : Fin s) (f : Finset (Fin s × Fin 4) → F) :
    functionEquiv s (lowerBlock (wholeBlock i) f)=stateLower i (functionEquiv s f) := by
  funext T
  obtain ⟨A, rfl⟩ := (fibresEquiv s).surjective T
  change functionEquiv s (lowerBlock (wholeBlock i) f) (fibres A)=_
  rw [functionEquiv_fibres]
  change (if Disjoint A (wholeBlock i) then f (A ∪ wholeBlock i) else 0)=
    (if fibres A i=∅ then functionEquiv s f (Function.update (fibres A) i Finset.univ) else 0)
  simp only [disjoint_iff, ← fibres_union, functionEquiv_fibres]

end PrivateTask346SubsetBlocks

namespace PrivateTask346ZetaDerivative
open PrivateTask346BooleanANF

variable {ι : Type*} [DecidableEq ι]

def toggle (i : ι) (S : Finset ι) : Finset ι := if i ∈ S then S.erase i else insert i S
def setDifference (i : ι) (f : Finset ι → F) (S : Finset ι) : F := f (toggle i S)+f S

def lower (i : ι) : (Finset ι → F) →ₗ[F] (Finset ι → F) where
  toFun := fun f S => if i ∈ S then 0 else f (insert i S)
  map_add' := by intro f g; funext S; by_cases h : i ∈ S <;> simp [h]
  map_smul' := by intro c f; funext S; by_cases h : i ∈ S <;> simp [h]

lemma zeta_congr (f g : Finset ι → F) (S : Finset ι) (h : ∀ T ⊆ S, f T=g T) :
    zeta f S=zeta g S := by
  unfold zeta
  apply Finset.sum_congr rfl
  intro T hT
  exact h T (Finset.mem_powerset.mp hT)

theorem zeta_difference (i : ι) (f : Finset ι → F) (S : Finset ι) :
    zeta (setDifference i f) S=lower i (zeta f) S := by
  change zeta (setDifference i f) S=(if i ∈ S then 0 else zeta f (insert i S))
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    let T := S.erase i
    have ht : i ∉ T := by simp [T]
    have hs : S=insert i T := (Finset.insert_erase hi).symm
    have hh : zeta (fun U => setDifference i f (insert i U)) T=zeta (setDifference i f) T := by
      apply zeta_congr
      intro U hU
      have hu : i ∉ U := fun h => ht (hU h)
      simp [setDifference, toggle, hu, add_comm]
    rw [hs, zeta_insert _ ht, hh, PrivateTask346BooleanANF.add_self_zero]
  · rw [if_neg hi]
    have he : zeta (setDifference i f) S=zeta (fun T => f (insert i T)+f T) S := by
      apply zeta_congr
      intro T hT
      have ht : i ∉ T := fun h => hi (hT h)
      simp [setDifference, toggle, ht]
    rw [he, zeta_add, zeta_insert _ hi]
    exact add_comm _ _

theorem point_toggle (i : ι) (S : Finset ι) :
    PrivateTask346CubicANF.point (toggle i S) = PrivateTask346CubicANF.point S+Pi.single i (1 : F) := by
  have h11 : (1+1 : F)=0 := by decide +kernel
  funext a
  by_cases ha : a=i
  · subst a
    by_cases hi : i ∈ S <;> simp [PrivateTask346CubicANF.point, toggle, hi, Pi.single_apply, h11]
  · by_cases hi : i ∈ S <;>
      simp [PrivateTask346CubicANF.point, toggle, hi, Pi.single_apply, ha, Ne.symm ha]

theorem zeta_cube_difference {n : ℕ} (i : Fin n) (f : PrivateTask346RegularSlices.Cube n → F) :
    zeta (fun S => PrivateTask346Derivatives.derivative (PrivateTask346RegularSlices.unit i) f
      (PrivateTask346CubicANF.point S)) =
        lower i (zeta (fun S => f (PrivateTask346CubicANF.point S))) := by
  have he : (fun S => PrivateTask346Derivatives.derivative (PrivateTask346RegularSlices.unit i) f
      (PrivateTask346CubicANF.point S)) = setDifference i (fun S => f (PrivateTask346CubicANF.point S)) := by
    funext S
    change f (PrivateTask346CubicANF.point S+Pi.single i (1 : F))+f (PrivateTask346CubicANF.point S)=_
    rw [← point_toggle]
    rfl
  rw [he]
  funext S
  exact zeta_difference i _ S

end PrivateTask346ZetaDerivative

namespace PrivateTask346ComponentOperators
open PrivateTask346BooleanANF PrivateTask346BlockComponents PrivateTask346SubsetBlocks
open PrivateTask346ZetaDerivative

noncomputable def setComponents (s : ℕ) :
    (States s → F) ≃ₗ[F] (∀ ω : Components s, Finset (Active ω) → F) :=
  (functionComponents s).trans (LinearEquiv.piCongrRight (fun ω =>
    (LinearEquiv.piCongrLeft F (fun _ : Active ω → F => F)
      (PrivateTask346CodeUpperRank.pointEquiv : Finset (Active ω) ≃ (Active ω → F))).symm))

def restoreSet {s : ℕ} (ω : Components s) (S : Finset (Active ω)) : States s :=
  restore ω (PrivateTask346CubicANF.point S)

lemma setComponents_apply (s : ℕ) (f : States s → F) (ω : Components s) (S : Finset (Active ω)) :
    setComponents s f ω S=f (restoreSet ω S) := rfl

theorem restoreSet_active {s : ℕ} (ω : Components s) (S : Finset (Active ω)) (i : Active ω) :
    restoreSet ω S i.val=(if i ∈ S then Finset.univ else ∅) := by
  by_cases hi : i ∈ S <;>
    simp [restoreSet, restore, i.property, PrivateTask346CubicANF.point, decode, hi]

theorem restoreSet_inactive {s : ℕ} (ω : Components s) (S : Finset (Active ω)) (i : Fin s)
    (hi : ω i ≠ none) : restoreSet ω S i ≠ ∅ := by
  intro h
  obtain ⟨hh, hb⟩ := (restore_empty_iff ω (PrivateTask346CubicANF.point S) i).mp h
  exact hi hh

theorem restoreSet_insert {s : ℕ} (ω : Components s) (S : Finset (Active ω)) (i : Active ω) :
    restoreSet ω (insert i S)=Function.update (restoreSet ω S) i.val Finset.univ := by
  funext j
  by_cases hj : j=i.val
  · subst j
    simp [restoreSet_active]
  · by_cases hω : ω j=none
    · let a : Active ω := ⟨j,hω⟩
      have ha : a ≠ i := fun h => hj (congrArg Subtype.val h)
      have hv : restoreSet ω (insert i S) j=restoreSet ω S j := by
        change restoreSet ω (insert i S) a.val=restoreSet ω S a.val
        rw [restoreSet_active, restoreSet_active]
        simp [ha]
      simpa [Function.update, hj] using hv
    · simp [restoreSet, restore, hω, Function.update, hj]

theorem stateLower_component {s : ℕ} (i : Fin s) (f : States s → F)
    (ω : Components s) (S : Finset (Active ω)) :
    setComponents s (stateLower i f) ω S=
      if hi : ω i=none then lower (⟨i,hi⟩ : Active ω) (setComponents s f ω) S else 0 := by
  by_cases hi : ω i=none
  · rw [dif_pos hi]
    let a : Active ω := ⟨i,hi⟩
    change (if restoreSet ω S i=∅ then f (Function.update (restoreSet ω S) i Finset.univ) else 0)=
      (if a ∈ S then 0 else f (restoreSet ω (insert a S)))
    have hv : restoreSet ω S i=(if a ∈ S then Finset.univ else ∅) := restoreSet_active ω S a
    rw [hv]
    by_cases ha : a ∈ S
    · have hn : (Finset.univ : Local) ≠ ∅ := by decide +kernel
      simp [ha, hn]
    · simp only [ha, if_false, if_true]
      rw [← restoreSet_insert ω S a]
  · rw [dif_neg hi]
    change (if restoreSet ω S i=∅ then f (Function.update (restoreSet ω S) i Finset.univ) else 0)=0
    rw [if_neg (restoreSet_inactive ω S i hi)]

end PrivateTask346ComponentOperators

namespace PrivateTask346RegularKernel
open PrivateTask346AffineCubic PrivateTask346NilpotentElimination
open PrivateTask346LiftedElimination PrivateTask346RegularSlices

def regularKernel {n m : ℕ} (C : Fin n → Fin m → F) : Submodule F (Cube n → F) :=
  jointKernel (fun j => coded (fun i => C i j))

def liftedKernel {n m : ℕ} (C : Fin (n+1) → Fin m → F) :
    Submodule F ((Cube n → F) × (Cube n → F)) :=
  jointKernel (fun j => lifted (C 0 j) (coded (fun i : Fin n => C i.succ j)))

theorem kernel_slice {n m : ℕ} (C : Fin (n+1) → Fin m → F) :
    (liftedKernel C).comap (sliceEquiv n).toLinearMap = regularKernel C := by
  ext f
  rw [Submodule.mem_comap]
  simp only [liftedKernel, regularKernel, mem_jointKernel, LinearEquiv.coe_toLinearMap]
  apply forall_congr'
  intro j
  rw [← split_coded (fun i => C i j) f]
  constructor
  · intro h
    apply (sliceEquiv n).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

theorem finrank_slice {n m : ℕ} (C : Fin (n+1) → Fin m → F) :
    Module.finrank F (regularKernel C) = Module.finrank F (liftedKernel C) := by
  have h := ((sliceEquiv n).ofSubmodule' (liftedKernel C)).finrank_eq
  rw [kernel_slice] at h
  exact h

theorem finrank_pivot {n m : ℕ} (C : Fin (n+1) → Fin m → F) (p : Fin m) (hp : C 0 p=1) :
    Module.finrank F (regularKernel C) =
      Module.finrank F (regularKernel (fun i : Fin n => fun j => C i.succ j+C 0 j*C i.succ p)) := by
  rw [finrank_slice]
  have h := finrank_row_elimination (fun j => C 0 j)
    (fun j => coded (fun i : Fin n => C i.succ j)) p hp
    (coded_square (fun i : Fin n => C i.succ p))
    (fun j => coded_commute (fun i : Fin n => C i.succ j) (fun i : Fin n => C i.succ p))
  change Module.finrank F (liftedKernel C) = _ at h
  have he : (fun j => coded (fun i : Fin n => C i.succ j)+C 0 j • coded (fun i : Fin n => C i.succ p)) =
      (fun j => coded (fun i : Fin n => C i.succ j+C 0 j*C i.succ p)) := by
    funext j
    rw [coded_add, coded_mul]
  exact h.trans (congrArg (fun T => Module.finrank F (jointKernel T)) he)

def productEquiv {n : ℕ} (P Q : Submodule F (Cube n → F)) :
    P.prod Q ≃ₗ[F] (P × Q) where
  toFun := fun v => (⟨v.val.1, v.property.1⟩, ⟨v.val.2, v.property.2⟩)
  invFun := fun v => ⟨(v.1.val, v.2.val), v.1.property, v.2.property⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl

theorem lifted_zero {n m : ℕ} (C : Fin (n+1) → Fin m → F) (hz : ∀ j, C 0 j=0) :
    liftedKernel C = (regularKernel (fun i : Fin n => fun j => C i.succ j)).prod
      (regularKernel (fun i : Fin n => fun j => C i.succ j)) := by
  ext v
  change v ∈ jointKernel (fun j => lifted (C 0 j) (coded (fun i : Fin n => C i.succ j))) ↔
    v.1 ∈ regularKernel (fun i : Fin n => fun j => C i.succ j) ∧
      v.2 ∈ regularKernel (fun i : Fin n => fun j => C i.succ j)
  rw [mem_lifted]
  simp only [hz, zero_smul, zero_add, regularKernel, mem_jointKernel, forall_and]

theorem finrank_free {n m : ℕ} (C : Fin (n+1) → Fin m → F) (hz : ∀ j, C 0 j=0) :
    Module.finrank F (regularKernel C) =
      2 * Module.finrank F (regularKernel (fun i : Fin n => fun j => C i.succ j)) := by
  rw [finrank_slice, lifted_zero C hz, (productEquiv _ _).finrank_eq, Module.finrank_prod]
  omega

end PrivateTask346RegularKernel

namespace PrivateTask346CodeZeros
open PrivateTask346AffineCubic PrivateTask346RegularSlices PrivateTask346LiftedElimination

abbrev Zeros {n m : ℕ} (C : Fin n → Fin m → F) :=
  {y : Cube n // ∀ j : Fin m, (∑ i : Fin n, C i j*y i)=0}

def freeEquiv {n m : ℕ} (C : Fin (n+1) → Fin m → F) (hz : ∀ j, C 0 j=0) :
    Zeros C ≃ F × Zeros (fun i : Fin n => fun j => C i.succ j) where
  toFun := fun y => (y.val 0, ⟨Fin.tail y.val, by
    intro j
    have h := y.property j
    rw [Fin.sum_univ_succ] at h
    simpa only [Fin.tail, hz, zero_mul, zero_add] using h⟩)
  invFun := fun p => ⟨Fin.cons p.1 p.2.val, by
    intro j
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hz, zero_mul, zero_add]
      using p.2.property j⟩
  left_inv := by intro y; apply Subtype.ext; exact Fin.cons_self_tail y.val
  right_inv := by intro p; apply Prod.ext; rfl; apply Subtype.ext; rfl

theorem card_free {n m : ℕ} (C : Fin (n+1) → Fin m → F) (hz : ∀ j, C 0 j=0) :
    Nat.card (Zeros C) = 2 * Nat.card (Zeros (fun i : Fin n => fun j => C i.succ j)) := by
  rw [Nat.card_congr (freeEquiv C hz), Nat.card_prod]
  have hF : Nat.card F=2 := by simp [F]
  rw [hF]

lemma head_eq {n m : ℕ} (C : Fin (n+1) → Fin m → F) (p : Fin m) (hp : C 0 p=1)
    (y : Zeros C) : y.val 0 = ∑ i : Fin n, C i.succ p*y.val i.succ := by
  have h := y.property p
  rw [Fin.sum_univ_succ, hp, one_mul] at h
  exact eq_of_add_zero _ _ h

lemma reduced_sum {n m : ℕ} (C : Fin (n+1) → Fin m → F) (p j : Fin m) (x : Cube n) :
    (∑ i : Fin n, (C i.succ j+C 0 j*C i.succ p)*x i) =
      (∑ i : Fin n, C i.succ j*x i) + C 0 j*(∑ i : Fin n, C i.succ p*x i) := by
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

def pivotEquiv {n m : ℕ} (C : Fin (n+1) → Fin m → F) (p : Fin m) (hp : C 0 p=1) :
    Zeros C ≃ Zeros (fun i : Fin n => fun j => C i.succ j+C 0 j*C i.succ p) where
  toFun := fun y => ⟨Fin.tail y.val, by
    intro j
    have h := y.property j
    rw [Fin.sum_univ_succ, head_eq C p hp y] at h
    rw [reduced_sum C p j]
    simpa only [Fin.tail, add_comm] using h⟩
  invFun := fun x => ⟨Fin.cons (∑ i : Fin n, C i.succ p*x.val i) x.val, by
    intro j
    have h := x.property j
    rw [reduced_sum C p j] at h
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_comm] using h⟩
  left_inv := by
    intro y
    apply Subtype.ext
    change Fin.cons (∑ i : Fin n, C i.succ p*y.val i.succ) (Fin.tail y.val)=y.val
    rw [← head_eq C p hp y]
    exact Fin.cons_self_tail y.val
  right_inv := by intro x; apply Subtype.ext; rfl

theorem card_pivot {n m : ℕ} (C : Fin (n+1) → Fin m → F) (p : Fin m) (hp : C 0 p=1) :
    Nat.card (Zeros C) =
      Nat.card (Zeros (fun i : Fin n => fun j => C i.succ j+C 0 j*C i.succ p)) :=
  Nat.card_congr (pivotEquiv C p hp)

theorem card_zero {m : ℕ} (C : Fin 0 → Fin m → F) : Nat.card (Zeros C)=1 := by
  simp [Zeros, Cube]

end PrivateTask346CodeZeros

namespace PrivateTask346RegularDimension
open PrivateTask346AffineCubic PrivateTask346NilpotentElimination
open PrivateTask346RegularSlices PrivateTask346RegularKernel PrivateTask346CodeZeros
open Module

theorem dim_zero {m : ℕ} (C : Fin 0 → Fin m → F) :
    finrank F (regularKernel C)=1 := by
  have h : regularKernel C=⊤ := by
    ext f
    simp [regularKernel, mem_jointKernel, coded]
  rw [h, finrank_top, Module.finrank_pi]
  simp [Cube]

theorem regular_dimension (n m : ℕ) : ∀ C : Fin n → Fin m → F,
    finrank F (regularKernel C)=Nat.card (Zeros C) := by
  induction n with
  | zero =>
    intro C
    rw [dim_zero, card_zero]
  | succ n ih =>
    intro C
    classical
    by_cases hz : ∀ j, C 0 j=0
    · rw [finrank_free C hz, card_free C hz, ih]
    · obtain ⟨p, hp⟩ := not_forall.mp hz
      have hp1 : C 0 p=1 := by
        obtain h | h := PrivateTask346OneFace.field_cases (C 0 p)
        · exact (hp h).elim
        · exact h
      rw [finrank_pivot C p hp1, card_pivot C p hp1, ih]

end PrivateTask346RegularDimension

namespace PrivateTask346RegularLower
open PrivateTask346BooleanANF PrivateTask346RegularSlices PrivateTask346ZetaDerivative
open PrivateTask346NilpotentElimination PrivateTask346RegularKernel PrivateTask346CodeZeros

noncomputable def transform (n : ℕ) : (Cube n → F) ≃ₗ[F] (Finset (Fin n) → F) :=
  ((LinearEquiv.piCongrLeft F (fun _ : Cube n => F)
    (PrivateTask346CodeUpperRank.pointEquiv : Finset (Fin n) ≃ Cube n)).symm).trans zetaEquiv

lemma transform_apply (n : ℕ) (f : Cube n → F) (S : Finset (Fin n)) :
    transform n f S=zeta (fun A => f (PrivateTask346CubicANF.point A)) S := rfl

def lowerCode {n : ℕ} (c : Fin n → F) :
    (Finset (Fin n) → F) →ₗ[F] (Finset (Fin n) → F) := ∑ i, c i • lower i

theorem transform_coded {n : ℕ} (c : Fin n → F) (f : Cube n → F) :
    transform n (coded c f)=lowerCode c (transform n f) := by
  have hi (i : Fin n) : transform n (PrivateTask346Derivatives.derivative (unit i) f)=
      lower i (transform n f) := by
    change zeta (fun A => PrivateTask346Derivatives.derivative (unit i) f
      (PrivateTask346CubicANF.point A)) =
        lower i (zeta (fun A => f (PrivateTask346CubicANF.point A)))
    exact zeta_cube_difference i f
  simp only [coded, lowerCode, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, hi]

def lowerKernel {n m : ℕ} (C : Fin n → Fin m → F) : Submodule F (Finset (Fin n) → F) :=
  jointKernel (fun j => lowerCode (fun i => C i j))

theorem kernel_comap {n m : ℕ} (C : Fin n → Fin m → F) :
    (lowerKernel C).comap (transform n).toLinearMap=regularKernel C := by
  ext f
  rw [Submodule.mem_comap]
  simp only [lowerKernel, regularKernel, mem_jointKernel, LinearEquiv.coe_toLinearMap]
  apply forall_congr'
  intro j
  rw [← transform_coded (fun i => C i j) f]
  constructor
  · intro h
    apply (transform n).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

theorem lower_dimension {n m : ℕ} (C : Fin n → Fin m → F) :
    Module.finrank F (lowerKernel C)=Nat.card (Zeros C) := by
  have h := ((transform n).ofSubmodule' (lowerKernel C)).finrank_eq
  rw [kernel_comap] at h
  exact h.symm.trans (PrivateTask346RegularDimension.regular_dimension n m C)

end PrivateTask346RegularLower

namespace PrivateTask346FiniteLower
open PrivateTask346BooleanANF PrivateTask346ZetaDerivative PrivateTask346NilpotentElimination

variable {I : Type*} [DecidableEq I] [Fintype I] {n m : ℕ}

def familyLower (c : I → F) : (Finset I → F) →ₗ[F] (Finset I → F) := ∑ i, c i • lower i

noncomputable def relabel (e : I ≃ Fin n) : (Finset I → F) ≃ₗ[F] (Finset (Fin n) → F) :=
  LinearEquiv.piCongrLeft' F (fun _ : Finset I => F) e.finsetCongr

lemma relabel_image (e : I ≃ Fin n) (f : Finset I → F) (A : Finset I) :
    relabel e f (e.finsetCongr A)=f A := by
  change f (e.finsetCongr.symm (e.finsetCongr A))=f A
  rw [Equiv.symm_apply_apply]

theorem relabel_lower (e : I ≃ Fin n) (i : I) (f : Finset I → F) :
    relabel e (lower i f)=lower (e i) (relabel e f) := by
  funext B
  obtain ⟨A, rfl⟩ := e.finsetCongr.surjective B
  rw [relabel_image]
  have hm : e i ∈ e.finsetCongr A ↔ i ∈ A := by simp [Equiv.finsetCongr_apply]
  have hu : e.finsetCongr (insert i A)=insert (e i) (e.finsetCongr A) := by
    simp [Equiv.finsetCongr_apply]
  change (if i ∈ A then 0 else f (insert i A))=
    (if e i ∈ e.finsetCongr A then 0 else relabel e f (insert (e i) (e.finsetCongr A)))
  simp only [hm, ← hu, relabel_image]

theorem relabel_family (e : I ≃ Fin n) (c : I → F) (f : Finset I → F) :
    relabel e (familyLower c f)=PrivateTask346RegularLower.lowerCode
      (fun t => c (e.symm t)) (relabel e f) := by
  simp only [familyLower, PrivateTask346RegularLower.lowerCode, LinearMap.sum_apply,
    map_sum, LinearMap.smul_apply, map_smul, relabel_lower]
  apply Fintype.sum_equiv e
  intro i
  simp

abbrev Zeros (C : I → Fin m → F) := {x : I → F // ∀ j : Fin m, (∑ i, C i j*x i)=0}

def zeroRelabel (e : I ≃ Fin n) (C : I → Fin m → F) :
    Zeros C ≃ PrivateTask346CodeZeros.Zeros (fun t : Fin n => fun j => C (e.symm t) j) where
  toFun := fun x => ⟨fun t => x.val (e.symm t), by
    intro j
    have hs : (∑ i : I, C i j*x.val i) =
        ∑ t : Fin n, C (e.symm t) j*x.val (e.symm t) := by
      apply Fintype.sum_equiv e
      intro i
      simp
    exact hs.symm.trans (x.property j)⟩
  invFun := fun y => ⟨fun i => y.val (e i), by
    intro j
    have hs : (∑ i : I, C i j*y.val (e i)) =
        ∑ t : Fin n, C (e.symm t) j*y.val t := by
      apply Fintype.sum_equiv e
      intro i
      simp
    exact hs.trans (y.property j)⟩
  left_inv := by intro x; apply Subtype.ext; funext i; simp
  right_inv := by intro y; apply Subtype.ext; funext t; simp

theorem kernel_comap (e : I ≃ Fin n) (C : I → Fin m → F) :
    (PrivateTask346RegularLower.lowerKernel (fun t : Fin n => fun j => C (e.symm t) j)).comap
      (relabel e).toLinearMap=jointKernel (fun j => familyLower (fun i => C i j)) := by
  ext f
  rw [Submodule.mem_comap]
  simp only [PrivateTask346RegularLower.lowerKernel, mem_jointKernel, LinearEquiv.coe_toLinearMap]
  apply forall_congr'
  intro j
  rw [← relabel_family e (fun i => C i j) f]
  constructor
  · intro h
    apply (relabel e).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

theorem finite_lower_dimension (C : I → Fin m → F) :
    Module.finrank F (jointKernel (fun j => familyLower (fun i => C i j)))=Nat.card (Zeros C) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have h := ((relabel e).ofSubmodule'
    (PrivateTask346RegularLower.lowerKernel (fun t : Fin (Fintype.card I) => fun j => C (e.symm t) j))).finrank_eq
  rw [kernel_comap] at h
  calc
    _ = Module.finrank F (PrivateTask346RegularLower.lowerKernel
        (fun t : Fin (Fintype.card I) => fun j => C (e.symm t) j)) := h
    _ = Nat.card (PrivateTask346CodeZeros.Zeros
        (fun t : Fin (Fintype.card I) => fun j => C (e.symm t) j)) :=
      PrivateTask346RegularLower.lower_dimension _
    _ = Nat.card (Zeros C) := (Nat.card_congr (zeroRelabel e C)).symm

end PrivateTask346FiniteLower

namespace PrivateTask346KernelProducts
open PrivateTask346AffineCubic PrivateTask346NilpotentElimination

variable {X Ω : Type*} {V : Ω → Type*} [AddCommGroup X] [Module F X]
  [∀ ω, AddCommGroup (V ω)] [∀ ω, Module F (V ω)] {m : ℕ}

noncomputable def kernelProduct (T : X ≃ₗ[F] (∀ ω, V ω))
    (A : Fin m → X →ₗ[F] X) (B : ∀ ω, Fin m → V ω →ₗ[F] V ω)
    (ht : ∀ j f ω, T (A j f) ω=B ω j (T f ω)) :
    jointKernel A ≃ₗ[F] (∀ ω, jointKernel (B ω)) where
  toFun := fun f ω => ⟨T f ω, by
    rw [mem_jointKernel]
    intro j
    have hf := (mem_jointKernel A f).mp f.property j
    rw [← ht, hf, map_zero, Pi.zero_apply]⟩
  invFun := fun g => ⟨T.symm (fun ω => (g ω).val), by
    rw [mem_jointKernel]
    intro j
    apply T.injective
    funext ω
    rw [ht, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply]
    exact (mem_jointKernel (B ω) _).mp (g ω).property j⟩
  left_inv := by
    intro f
    apply Subtype.ext
    exact T.symm_apply_apply f
  right_inv := by
    intro g
    funext ω
    apply Subtype.ext
    exact congrFun (T.apply_symm_apply (fun ω => (g ω).val)) ω
  map_add' := by
    intro f g
    funext ω
    apply Subtype.ext
    exact congrFun (map_add T (f : X) (g : X)) ω
  map_smul' := by
    intro c f
    funext ω
    apply Subtype.ext
    exact congrFun (map_smul T c (f : X)) ω

theorem product_dimension [Fintype Ω] [∀ ω, Module.Finite F (V ω)]
    (T : X ≃ₗ[F] (∀ ω, V ω)) (A : Fin m → X →ₗ[F] X)
    (B : ∀ ω, Fin m → V ω →ₗ[F] V ω)
    (ht : ∀ j f ω, T (A j f) ω=B ω j (T f ω)) :
    Module.finrank F (jointKernel A)=∑ ω, Module.finrank F (jointKernel (B ω)) := by
  rw [(kernelProduct T A B ht).finrank_eq, Module.finrank_pi_fintype]

theorem conjugate_dimension {Y : Type*} [AddCommGroup Y] [Module F Y]
    (T : X ≃ₗ[F] Y) (A : Fin m → X →ₗ[F] X) (B : Fin m → Y →ₗ[F] Y)
    (ht : ∀ j f, T (A j f)=B j (T f)) :
    Module.finrank F (jointKernel A)=Module.finrank F (jointKernel B) := by
  have he : (jointKernel B).comap T.toLinearMap=jointKernel A := by
    ext f
    rw [Submodule.mem_comap, mem_jointKernel, mem_jointKernel]
    apply forall_congr'
    intro j
    change B j (T f)=0 ↔ A j f=0
    rw [← ht j f]
    constructor
    · intro h
      apply T.injective
      simpa only [map_zero] using h
    · intro h
      rw [h, map_zero]
  have h := (T.ofSubmodule' (jointKernel B)).finrank_eq
  rw [he] at h
  exact h

end PrivateTask346KernelProducts

namespace PrivateTask346ComponentDimension
open PrivateTask346BooleanANF PrivateTask346BlockComponents PrivateTask346SubsetBlocks
open PrivateTask346ComponentOperators PrivateTask346FiniteLower
open PrivateTask346ZetaDerivative
open PrivateTask346NilpotentElimination PrivateTask346LeadingKernel PrivateTask346KernelProducts

theorem sum_subtype_of_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) (hf : ∀ a, ¬p a → f a=0) :
    (∑ a, f a)=∑ a : {x // p x}, f a.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ a : {x // ¬p x}, f a.val)=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact hf a.val a.property
  rw [hz, add_zero] at h
  exact h.symm

def stateCode {s m : ℕ} (C : Fin s → Fin m → F) (j : Fin m) :
    (States s → F) →ₗ[F] (States s → F) := ∑ i, C i j • stateLower i

theorem state_component_code {s m : ℕ} (C : Fin s → Fin m → F) (j : Fin m)
    (f : States s → F) (ω : Components s) :
    setComponents s (stateCode C j f) ω=
      familyLower (fun a : Active ω => C a.val j) (setComponents s f ω) := by
  classical
  funext S
  simp only [stateCode, familyLower, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
    map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stateLower_component]
  let g : Fin s → F := fun i => C i j *
    (if hi : ω i=none then lower (⟨i,hi⟩ : Active ω) (setComponents s f ω) S else 0)
  have hs := sum_subtype_of_zero (fun i : Fin s => ω i=none) g (by
    intro i hi
    simp only [g, dif_neg hi, mul_zero])
  have hr : (∑ a : Active ω, g a.val)=
      ∑ a : Active ω, C a.val j * lower a (setComponents s f ω) S := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [g, dif_pos a.property]
  exact hs.trans hr

theorem state_dimension {s m : ℕ} (C : Fin s → Fin m → F) :
    Module.finrank F (jointKernel (stateCode C))=
      ∑ ω : Components s, Nat.card (Zeros (fun a : Active ω => C a.val)) := by
  classical
  have h := product_dimension (setComponents s) (stateCode C)
    (fun ω j => familyLower (fun a : Active ω => C a.val j))
    (fun j f ω => state_component_code C j f ω)
  calc
    _ = ∑ ω : Components s,
        Module.finrank F (jointKernel (fun j => familyLower (fun a : Active ω => C a.val j))) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact finite_lower_dimension (fun a : Active ω => C a.val)

theorem block_dimension_components {s m : ℕ} (C : Fin s → Fin m → F) :
    Module.finrank F (jointKernel (codedLower (@wholeBlock s) C))=
      ∑ ω : Components s, Nat.card (Zeros (fun a : Active ω => C a.val)) := by
  have ht : ∀ j f, functionEquiv s (codedLower (@wholeBlock s) C j f)=
      stateCode C j (functionEquiv s f) := by
    intro j f
    simp only [codedLower, stateCode, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
      map_smul, transform_lower]
  rw [conjugate_dimension (functionEquiv s) (codedLower (@wholeBlock s) C) (stateCode C) ht]
  exact state_dimension C

end PrivateTask346ComponentDimension

namespace PrivateTask346ComponentCount
open PrivateTask346BooleanANF PrivateTask346BlockComponents PrivateTask346ComponentDimension

variable {s m : ℕ}

lemma restored_inactive_bit (ω : Components s) (b : Active ω → F) (i : Fin s) (hi : ω i ≠ none) :
    bit (restore ω b i)=0 := by
  have hc := congrFun (restore_component ω b) i
  change classify (restore ω b i)=ω i at hc
  apply bit_inactive
  change classify (restore ω b i) ≠ none
  rw [hc]
  exact hi

theorem code_restore (C : Fin s → Fin m → F) (ω : Components s) (b : Active ω → F) (j : Fin m) :
    (∑ i : Fin s, C i j*bit (restore ω b i)) = ∑ a : Active ω, C a.val j*b a := by
  classical
  have hs := sum_subtype_of_zero (fun i : Fin s => ω i=none)
    (fun i => C i j*bit (restore ω b i)) (by
      intro i hi
      rw [restored_inactive_bit ω b i hi, mul_zero])
  calc
    _ = ∑ a : Active ω, C a.val j*bit (restore ω b a.val) := hs
    _ = _ := by simp only [restore_bit]

abbrev StateZeros (C : Fin s → Fin m → F) :=
  {T : States s // ∀ j : Fin m, (∑ i : Fin s, C i j*bit (T i))=0}

def regroup (C : Fin s → Fin m → F) :
    {p : Σ ω : Components s, Active ω → F //
      ∀ j : Fin m, (∑ a : Active p.1, C a.val j*p.2 a)=0} ≃
      (Σ ω : Components s, PrivateTask346FiniteLower.Zeros (fun a : Active ω => C a.val)) where
  toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun := fun p => ⟨⟨p.1, p.2.val⟩, p.2.property⟩
  left_inv := by rintro ⟨⟨ω,b⟩,h⟩; rfl
  right_inv := by rintro ⟨ω,⟨b,h⟩⟩; rfl

noncomputable def stateSigmaZeros (C : Fin s → Fin m → F) :
    StateZeros C ≃ (Σ ω : Components s, PrivateTask346FiniteLower.Zeros (fun a : Active ω => C a.val)) := by
  have hp (T : States s) :
      (∀ j : Fin m, (∑ i : Fin s, C i j*bit (T i))=0) ↔
        (∀ j : Fin m, (∑ a : Active (componentEquiv s T).1,
          C a.val j*(componentEquiv s T).2 a)=0) := by
    have hr : restore (componentEquiv s T).1 (componentEquiv s T).2=T :=
      (componentEquiv s).symm_apply_apply T
    have he (j : Fin m) := code_restore C (componentEquiv s T).1 (componentEquiv s T).2 j
    rw [hr] at he
    simp only [he]
  exact ((componentEquiv s).subtypeEquiv hp).trans (regroup C)

def stateCubeEquiv (s : ℕ) : States s ≃ (Fin s → Fin 4 → F) where
  toFun := fun T i => PrivateTask346CubicANF.point (T i)
  invFun := fun z i => PrivateTask346CubicANF.ones (z i)
  left_inv := by
    intro T
    funext i
    exact (PrivateTask346CodeUpperRank.pointEquiv : Local ≃ (Fin 4 → F)).left_inv (T i)
  right_inv := by
    intro z
    funext i
    exact PrivateTask346CubicANF.point_ones (z i)

lemma stateCubeEquiv_apply (T : States s) (i : Fin s) :
    stateCubeEquiv s T i=PrivateTask346CubicANF.point (T i) := rfl

theorem quartic_point : ∀ S : Local,
    PrivateTask346CubePrice.quartic (PrivateTask346CubicANF.point S)=bit S := by decide +kernel

theorem state_zeros_card (C : Fin s → Fin m → F) :
    Nat.card (StateZeros C)=PrivateTask346IndependentPrice.score C ∅ := by
  have e : StateZeros C ≃ {z : Fin s → Fin 4 → F // ∀ j : Fin m,
      (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))=0} :=
    (stateCubeEquiv s).subtypeEquiv (by intro T; simp only [stateCubeEquiv_apply, quartic_point])
  exact (Nat.card_congr e).trans (PrivateTask346CodeCount.unqueried_coded_fibre C)

theorem sum_component_zeros (C : Fin s → Fin m → F) :
    (∑ ω : Components s, Nat.card (PrivateTask346FiniteLower.Zeros (fun a : Active ω => C a.val))) =
      PrivateTask346IndependentPrice.score C ∅ := by
  classical
  have hs : Nat.card (Σ ω : Components s, PrivateTask346FiniteLower.Zeros (fun a : Active ω => C a.val)) =
      ∑ ω : Components s, Nat.card (PrivateTask346FiniteLower.Zeros (fun a : Active ω => C a.val)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [Nat.card_eq_fintype_card]
  calc
    _ = Nat.card (Σ ω : Components s, PrivateTask346FiniteLower.Zeros (fun a : Active ω => C a.val)) := hs.symm
    _ = Nat.card (StateZeros C) := (Nat.card_congr (stateSigmaZeros C)).symm
    _ = _ := state_zeros_card C

end PrivateTask346ComponentCount

namespace PrivateTask346NoQuestionPrice
open PrivateTask346BooleanANF
open PrivateTask346SubsetBlocks PrivateTask346LeadingKernel PrivateTask346NilpotentElimination
open PrivateTask346AffineCubic (DegreeThree cubic_pullback)
open PrivateTask346CubicClosure (Blocks)

theorem block_kernel_score {s m : ℕ} (C : Fin s → Fin m → F) :
    Module.finrank F (jointKernel (codedLower (@wholeBlock s) C))=
      PrivateTask346IndependentPrice.score C ∅ :=
  (PrivateTask346ComponentDimension.block_dimension_components C).trans
    (PrivateTask346ComponentCount.sum_component_zeros C)

def curryLinear (s : ℕ) : ((Fin s × Fin 4) → F) →ₗ[F] Blocks s where
  toFun := fun x i a => x (i,a)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def flattenEquiv (s : ℕ) : Blocks s ≃ ((Fin s × Fin 4) → F) where
  toFun := fun z p => z p.1 p.2
  invFun := curryLinear s
  left_inv := by intro z; funext i a; rfl
  right_inv := by intro x; funext p; rcases p with ⟨i,a⟩; rfl

theorem block_product {s : ℕ} (z : Blocks s) (i : Fin s) :
    (∏ p ∈ wholeBlock i, flattenEquiv s z p)=PrivateTask346CubePrice.quartic (z i) := by
  classical
  rw [wholeBlock, Finset.prod_image]
  · simp only [Fin.prod_univ_succ, flattenEquiv, Equiv.coe_fn_mk,
      PrivateTask346CubePrice.quartic]
    change z i 0 * (z i 1 * (z i 2 * (z i 3 * 1))) = z i 0 * z i 1 * z i 2 * z i 3
    ring
  · intro a ha b hb hab
    exact congrArg Prod.snd hab

theorem cubic_count_le_score {s m : ℕ} (C : Fin s → Fin m → F)
    (q : Fin m → Blocks s → F) (hq : ∀ j, DegreeThree (q j)) :
    Nat.card {z : Blocks s // ∀ j : Fin m,
      (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))+q j z=0} ≤
      PrivateTask346IndependentPrice.score C ∅ := by
  classical
  let qf : Fin m → ((Fin s × Fin 4) → F) → F := fun j x => q j (curryLinear s x)
  have hqf : ∀ j, DegreeThree (qf j) := by
    intro j
    simpa only [add_zero] using cubic_pullback (curryLinear s) 0 (q j) (hq j)
  have he (z : Blocks s) :
      (∀ j : Fin m, (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))+q j z=0) ↔
      (∀ j : Fin m, PrivateTask346CodeUpperRank.observation wholeBlock C qf j (flattenEquiv s z)=0) := by
    simp only [PrivateTask346CodeUpperRank.observation, block_product]
    rfl
  have e : {z : Blocks s // ∀ j : Fin m,
      (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))+q j z=0} ≃
      {x : (Fin s × Fin 4) → F // ∀ j : Fin m,
        PrivateTask346CodeUpperRank.observation wholeBlock C qf j x=0} :=
    (flattenEquiv s).subtypeEquiv he
  have hc := Nat.card_congr e
  rw [hc]
  calc
    _ ≤ Module.finrank F (jointKernel (codedLower (@wholeBlock s) C)) :=
      cubic_count_le_kernel wholeBlock block_card C qf hqf
    _ = _ := block_kernel_score C

end PrivateTask346NoQuestionPrice

namespace PrivateTask346FinitePrice
open PrivateTask346BooleanANF
open PrivateTask346AffineCubic (DegreeThree cubic_pullback)

abbrev Block := Fin 4 → F
abbrev Cube (I : Type*) := I → Block

variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J] {m : ℕ}

def ignored (C : I → Fin m → F) (D : Finset I) (z : Cube I) (j : Fin m) : F :=
  ∑ i : I, if i ∈ D then 0 else C i j*PrivateTask346CubePrice.quartic (z i)

noncomputable def capacity (C : I → Fin m → F) (D : Finset I) : ℕ :=
  Nat.card {z : Cube I // ∀ j : Fin m, ignored C D z j=0}

noncomputable def relabel (e : I ≃ J) : Cube I ≃ₗ[F] Cube J :=
  LinearEquiv.piCongrLeft' F (fun _ : I => Block) e

lemma relabel_apply (e : I ≃ J) (z : Cube I) (i : I) : relabel e z (e i)=z i := by
  change z (e.symm (e i))=z i
  rw [Equiv.symm_apply_apply]

theorem ignored_relabel (e : I ≃ J) (C : I → Fin m → F) (D : Finset I)
    (z : Cube I) (j : Fin m) :
    ignored (fun t : J => C (e.symm t)) (e.finsetCongr D) (relabel e z) j=ignored C D z j := by
  classical
  symm
  apply Fintype.sum_equiv e
  intro i
  simp only [Equiv.symm_apply_apply, relabel_apply, Equiv.finsetCongr_apply,
    Finset.mem_map_equiv]

theorem capacity_relabel (e : I ≃ J) (C : I → Fin m → F) (D : Finset I) :
    capacity C D=capacity (fun t : J => C (e.symm t)) (e.finsetCongr D) := by
  have he : {z : Cube I // ∀ j : Fin m, ignored C D z j=0} ≃
      {x : Cube J // ∀ j : Fin m,
        ignored (fun t : J => C (e.symm t)) (e.finsetCongr D) x j=0} :=
    (relabel e).toEquiv.subtypeEquiv (by
      intro z
      change (∀ j, ignored C D z j=0) ↔
        (∀ j, ignored (fun t : J => C (e.symm t)) (e.finsetCongr D) (relabel e z) j=0)
      simp only [ignored_relabel])
  exact Nat.card_congr he

theorem capacity_fin {s : ℕ} (C : Fin s → Fin m → F) (D : Finset (Fin s)) :
    capacity C D=PrivateTask346IndependentPrice.score C D := by
  have hi (z : Cube (Fin s)) (j : Fin m) : ignored C D z j=
      ∑ i ∈ Finset.univ \ D, C i j*PrivateTask346CubePrice.quartic (z i) := by
    classical
    simp only [ignored, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    congr 1
    ext i
    simp
  unfold capacity
  simp_rw [hi]
  exact PrivateTask346IgnoredCodeCount.ignored_coded_fibre C D

theorem cubic_count_le_capacity (C : I → Fin m → F) (q : Fin m → Cube I → F)
    (hq : ∀ j, DegreeThree (q j)) :
    Nat.card {z : Cube I // ∀ j : Fin m, ignored C ∅ z j+q j z=0} ≤ capacity C ∅ := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let T := relabel e
  let C' : Fin (Fintype.card I) → Fin m → F := fun t => C (e.symm t)
  let q' : Fin m → Cube (Fin (Fintype.card I)) → F := fun j x => q j (T.symm x)
  have hq' (j : Fin m) : DegreeThree (q' j) := by
    change DegreeThree (fun x => q j (T.symm x))
    simpa only [add_zero, LinearEquiv.coe_toLinearMap] using
      cubic_pullback T.symm.toLinearMap 0 (q j) (hq j)
  have hempty : e.finsetCongr ∅=∅ := by simp [Equiv.finsetCongr_apply]
  have hp (z : Cube I) : (∀ j : Fin m, ignored C ∅ z j+q j z=0) ↔
      (∀ j : Fin m, (∑ i, C' i j*PrivateTask346CubePrice.quartic (T z i))+q' j (T z)=0) := by
    have hi (j : Fin m) : (∑ i, C' i j*PrivateTask346CubePrice.quartic (T z i))=
        ignored C ∅ z j := by
      simpa [hempty, ignored, C', T] using ignored_relabel e C ∅ z j
    simp only [q', LinearEquiv.symm_apply_apply]
    simp only [hi]
  have he : {z : Cube I // ∀ j : Fin m, ignored C ∅ z j+q j z=0} ≃
      {x : Cube (Fin (Fintype.card I)) // ∀ j : Fin m,
        (∑ i, C' i j*PrivateTask346CubePrice.quartic (x i))+q' j x=0} :=
    T.toEquiv.subtypeEquiv hp
  rw [Nat.card_congr he, capacity_relabel e C ∅]
  simpa only [hempty, capacity_fin] using
    PrivateTask346NoQuestionPrice.cubic_count_le_score C' q' hq'

noncomputable def best (C : I → Fin m → F) (h : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset I)).filter fun D => D.card≤h).sup (capacity C)

theorem capacity_le_best (C : I → Fin m → F) (h : ℕ) (D : Finset I) (hd : D.card≤h) :
    capacity C D≤best C h := by
  apply Finset.le_sup
  simp [hd]

theorem best_mono (C : I → Fin m → F) {h k : ℕ} (hh : h≤k) : best C h≤best C k := by
  apply Finset.sup_le
  intro D hd
  exact capacity_le_best C k D (le_trans (Finset.mem_filter.mp hd).2 hh)

theorem best_zero (C : I → Fin m → F) : best C 0=capacity C ∅ := by
  apply le_antisymm
  · apply Finset.sup_le
    intro D hd
    have hz : D=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (Finset.mem_filter.mp hd).2)
    subst D
    exact le_rfl
  · exact capacity_le_best C 0 ∅ (by simp)

end PrivateTask346FinitePrice

namespace PrivateTask346RemoveBlock
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice

variable {I : Type} [DecidableEq I] [Fintype I] {m : ℕ}

abbrev Rest (i : I) := {j : I // j≠i}

def splitBlock (i : I) : Cube I ≃ (Block × Cube (Rest i)) where
  toFun := fun z => (z i,fun j => z j.val)
  invFun := fun p j => if h : j=i then p.1 else p.2 ⟨j,h⟩
  left_inv := by
    intro z
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [h]
  right_inv := by
    intro p
    apply Prod.ext
    · simp
    · funext j
      simp [j.property]

def adjoin (i : I) (D : Finset (Rest i)) : Finset I :=
  insert i (D.image Subtype.val)

theorem adjoin_card (i : I) (D : Finset (Rest i)) : (adjoin i D).card=D.card+1 := by
  have hi : i ∉ D.image Subtype.val := by
    intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
    exact j.property he
  rw [adjoin, Finset.card_insert_of_notMem hi,
    Finset.card_image_of_injective D Subtype.val_injective]

theorem ignored_adjoin (C : I → Fin m → F) (i : I) (D : Finset (Rest i))
    (z : Cube I) (j : Fin m) :
    ignored C (adjoin i D) z j=ignored (fun t : Rest i => C t.val) D (fun t => z t.val) j := by
  classical
  unfold ignored
  have hs := PrivateTask346ComponentDimension.sum_subtype_of_zero (fun t : I => t≠i)
    (fun t => if t ∈ adjoin i D then (0 : F) else C t j*PrivateTask346CubePrice.quartic (z t)) (by
      intro t ht
      have he : t=i := not_ne_iff.mp ht
      subst t
      simp [adjoin])
  rw [hs]
  apply Finset.sum_congr rfl
  intro t ht
  have hm : t.val ∈ adjoin i D ↔ t ∈ D := by
    simp only [adjoin, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h
      rcases h with h | ⟨a,ha,he⟩
      · exact False.elim (t.property h)
      · have he' : a=t := Subtype.ext he
        simpa only [he'] using ha
    · intro h
      exact Or.inr ⟨t,h,rfl⟩
  simp only [hm]

def capacityEquiv (C : I → Fin m → F) (i : I) (D : Finset (Rest i)) :
    {z : Cube I // ∀ j : Fin m, ignored C (adjoin i D) z j=0} ≃
      (Block × {x : Cube (Rest i) // ∀ j : Fin m, ignored (fun t : Rest i => C t.val) D x j=0}) where
  toFun := fun z => (z.val i,⟨fun t => z.val t.val,by
    intro j
    exact (ignored_adjoin C i D z.val j).symm.trans (z.property j)⟩)
  invFun := fun p => ⟨(splitBlock i).symm (p.1,p.2.val),by
    intro j
    rw [ignored_adjoin]
    have he : (fun t : Rest i => (splitBlock i).symm (p.1,p.2.val) t.val)=p.2.val := by
      funext t
      simp [splitBlock, t.property]
    rw [he]
    exact p.2.property j⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact (splitBlock i).symm_apply_apply z.val
  right_inv := by
    intro p
    apply Prod.ext
    · simp [splitBlock]
    · apply Subtype.ext
      funext t
      simp [splitBlock,t.property]

theorem capacity_adjoin (C : I → Fin m → F) (i : I) (D : Finset (Rest i)) :
    capacity C (adjoin i D)=16*capacity (fun t : Rest i => C t.val) D := by
  unfold capacity
  rw [Nat.card_congr (capacityEquiv C i D), Nat.card_prod]
  have hc : Nat.card Block=16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]

theorem best_attained (C : I → Fin m → F) (h : ℕ) :
    ∃ D : Finset I, D.card≤h ∧ best C h=capacity C D := by
  classical
  have hn : ((Finset.univ : Finset (Finset I)).filter fun D => D.card≤h).Nonempty :=
    ⟨∅,by simp⟩
  obtain ⟨D,hd,he⟩ := Finset.exists_mem_eq_sup _ hn (capacity C)
  exact ⟨D,(Finset.mem_filter.mp hd).2,he⟩

theorem best_remove (C : I → Fin m → F) (i : I) (h : ℕ) :
    16*best (fun t : Rest i => C t.val) h≤best C (h+1) := by
  obtain ⟨D,hd,he⟩ := best_attained (fun t : Rest i => C t.val) h
  rw [he, ← capacity_adjoin]
  apply capacity_le_best
  rw [adjoin_card]
  omega

end PrivateTask346RemoveBlock

namespace PrivateTask346PivotSlice
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice
open PrivateTask346RemoveBlock (Rest)

variable {I : Type} [DecidableEq I] [Fintype I]

def unit (i : I) (p : Fin 4) : Cube I := Pi.single i (Pi.single p 1)

theorem expand (z : Cube I) : z=∑ i : I, ∑ p : Fin 4, z i p • unit i p := by
  ext i p
  simp [unit, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply]

theorem exists_pivot (l : Cube I →ₗ[F] F) (hl : l≠0) :
    ∃ i : I, ∃ p : Fin 4, l (unit i p)=1 := by
  by_contra hn
  push_neg at hn
  have hz (i : I) (p : Fin 4) : l (unit i p)=0 := by
    obtain h | h := PrivateTask346OneFace.field_cases (l (unit i p))
    · exact h
    · exact False.elim (hn i p h)
  apply hl
  apply LinearMap.ext
  intro z
  change l z=0
  rw [expand z]
  simp [map_sum, map_smul, hz]

def insertRest (i : I) : Cube (Rest i) →ₗ[F] Cube I where
  toFun := fun x j => if h : j=i then 0 else x ⟨j,h⟩
  map_add' := by
    intro x y
    ext j a
    by_cases h : j=i <;> simp [h]
  map_smul' := by
    intro c x
    ext j a
    by_cases h : j=i <;> simp [h]

@[local simp] theorem insertRest_same (i : I) (x : Cube (Rest i)) : insertRest i x i=0 := by
  simp [insertRest]

@[local simp] theorem insertRest_other (i : I) (x : Cube (Rest i)) (j : Rest i) :
    insertRest i x j.val=x j := by simp [insertRest,j.property]

abbrev ZeroBlock (p : Fin 4) := {u : Block // u p=0}
abbrev Label (p : Fin 4) := F × ZeroBlock p

theorem label_card (p : Fin 4) : Fintype.card (Label p)=16 := by
  fin_cases p <;> decide +kernel

def base (i : I) {p : Fin 4} (u : ZeroBlock p) : Cube I := Pi.single i u.val

def sliceLinear (l : Cube I →ₗ[F] F) (i : I) (p : Fin 4) : Cube (Rest i) →ₗ[F] Cube I :=
  insertRest i - (l.comp (insertRest i)).smulRight (unit i p)

def sliceConstant (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4) (v : Label p) : Cube I :=
  base i v.2+(v.1-c-l (base i v.2)) • unit i p

def slice (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (v : Label p) (x : Cube (Rest i)) : Cube I := sliceLinear l i p x+sliceConstant l c i p v

theorem slice_formula (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (v : Label p) (x : Cube (Rest i)) :
    slice l c i p v x=insertRest i x+base i v.2+
      (v.1-c-l (insertRest i x)-l (base i v.2)) • unit i p := by
  simp only [slice, sliceLinear, sliceConstant, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply]
  module

theorem slice_answer (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (hp : l (unit i p)=1) (v : Label p) (x : Cube (Rest i)) :
    l (slice l c i p v x)+c=v.1 := by
  rw [slice_formula, map_add, map_add, map_smul, hp]
  simp only [smul_eq_mul,mul_one]
  ring

theorem slice_other (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (v : Label p) (x : Cube (Rest i)) (j : Rest i) : slice l c i p v x j.val=x j := by
  rw [slice_formula]
  ext a
  simp [base,unit,j.property,Pi.single_apply,Pi.add_apply,Pi.smul_apply]

theorem slice_local_other (l : Cube I →ₗ[F] F) (c : F) (i : I) (p a : Fin 4)
    (v : Label p) (x : Cube (Rest i)) (ha : a≠p) : slice l c i p v x i a=v.2.val a := by
  rw [slice_formula]
  simp [base,unit,ha,Pi.single_apply,Pi.add_apply,Pi.smul_apply]

def encode (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4) (z : Cube I) :
    Label p × Cube (Rest i) :=
  ((l z+c,⟨Function.update (z i) p 0,by simp⟩),fun j => z j.val)

theorem slice_encode (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (hp : l (unit i p)=1) (z : Cube I) :
    slice l c i p (encode l c i p z).1 (encode l c i p z).2=z := by
  have hd : insertRest i (fun j : Rest i => z j.val)+
      base i (encode l c i p z).1.2+z i p • unit i p=z := by
    ext j a
    by_cases hj : j=i
    · subst j
      by_cases ha : a=p
      · subst a; simp [base,unit,encode,Pi.single_apply,Pi.add_apply,Pi.smul_apply]
      · simp [base,unit,encode,ha,Pi.single_apply,Pi.add_apply,Pi.smul_apply,Function.update]
    · simp [insertRest,base,unit,encode,hj,Pi.single_apply,Pi.add_apply,Pi.smul_apply]
  have hl := congrArg l hd
  simp only [map_add,map_smul,hp,smul_eq_mul,mul_one] at hl
  have hs : (encode l c i p z).1.1-c-l (insertRest i (encode l c i p z).2)-
      l (base i (encode l c i p z).1.2)=z i p := by
    change l z+c-c-l (insertRest i (fun j : Rest i => z j.val))-
      l (base i (encode l c i p z).1.2)=z i p
    linear_combination -hl
  rw [slice_formula,hs]
  exact hd

theorem encode_slice (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (hp : l (unit i p)=1) (v : Label p) (x : Cube (Rest i)) :
    encode l c i p (slice l c i p v x)=(v,x) := by
  apply Prod.ext
  · apply Prod.ext
    · exact slice_answer l c i p hp v x
    · apply Subtype.ext
      funext a
      by_cases ha : a=p
      · subst a
        simpa [encode] using v.2.property.symm
      · simpa [encode,ha] using slice_local_other l c i p a v x ha
  · funext j
    exact slice_other l c i p v x j

def sliceEquiv (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (hp : l (unit i p)=1) : Cube I ≃ (Label p × Cube (Rest i)) where
  toFun := encode l c i p
  invFun := fun v => slice l c i p v.1 v.2
  left_inv := slice_encode l c i p hp
  right_inv := by rintro ⟨v,x⟩; exact encode_slice l c i p hp v x

end PrivateTask346PivotSlice

namespace PrivateTask346QueryTree
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice (Cube)
open PrivateTask346AffineCubic (DegreeThree cubic_pullback)

abbrev Tree (I : Type) (m : ℕ) : ℕ → Type
  | 0 => {q : Fin m → Cube I → F // ∀ j, DegreeThree (q j)}
  | h+1 => (Cube I →ₗ[F] F) × F × (F → Tree I m h)

abbrev Tree.leaf {I : Type} {m : ℕ} (q : Fin m → Cube I → F)
    (hq : ∀ j, DegreeThree (q j)) : Tree I m 0 := ⟨q,hq⟩

abbrev Tree.node {I : Type} {m h : ℕ} (l : Cube I →ₗ[F] F) (c : F)
    (next : F → Tree I m h) : Tree I m (h+1) := (l,c,next)

def error {I : Type} {m : ℕ} : {h : ℕ} → Tree I m h → Cube I → Fin m → F
  | 0, t, z, j => t.val j z
  | _+1, t, z, j => error (t.2.2 (t.1 z+t.2.1)) z j

def pullback {I J : Type} {m h : ℕ} (t : Tree I m h) (L : Cube J →ₗ[F] Cube I)
    (c : Cube I) (e : Fin m → Cube J → F) (he : ∀ j, DegreeThree (e j)) : Tree J m h :=
  match h with
  | 0 => Tree.leaf (fun j x => t.val j (L x+c)+e j x) (fun j =>
      PrivateTask346CubicClosure.cubic_add _ _ (cubic_pullback L c (t.val j) (t.property j)) (he j))
  | _+1 => Tree.node (t.1.comp L) (t.1 c+t.2.1) (fun a => pullback (t.2.2 a) L c e he)

theorem error_pullback {I J : Type} {m h : ℕ} (t : Tree I m h) (L : Cube J →ₗ[F] Cube I)
    (c : Cube I) (e : Fin m → Cube J → F) (he : ∀ j, DegreeThree (e j))
    (x : Cube J) (j : Fin m) :
    error (pullback t L c e he) x j=error t (L x+c) j+e j x := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simpa only [pullback,error,Tree.node,LinearMap.comp_apply,map_add,add_assoc] using
      ih (t := t.2.2 (t.1 (L x)+(t.1 c+t.2.1)))

def Hit {I : Type} [DecidableEq I] [Fintype I] {m h : ℕ}
    (C : I → Fin m → F) (t : Tree I m h) (z : Cube I) : Prop :=
  ∀ j : Fin m, PrivateTask346FinitePrice.ignored C ∅ z j+error t z j=0

end PrivateTask346QueryTree

namespace PrivateTask346SliceCubic
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice
open PrivateTask346RemoveBlock (Rest)
open PrivateTask346PivotSlice
open PrivateTask346AffineCubic (DegreeThree)

variable {I : Type} [DecidableEq I] [Fintype I] {m : ℕ}

theorem quartic_product (z : Block) : PrivateTask346CubePrice.quartic z=∏ a : Fin 4, z a := by
  simp only [Fin.prod_univ_succ,PrivateTask346CubePrice.quartic]
  change z 0*z 1*z 2*z 3=z 0*(z 1*(z 2*(z 3*1)))
  ring

def coordinate (i : I) (p : Fin 4) : Cube I →ₗ[F] F where
  toFun := fun z => z i p
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem slice_quartic_cubic (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4) (v : Label p) :
    DegreeThree (fun x : Cube (Rest i) => PrivateTask346CubePrice.quartic (slice l c i p v x i)) := by
  let K : F := ∏ a ∈ (Finset.univ : Finset (Fin 4)).erase p, v.2.val a
  let L : Cube (Rest i) →ₗ[F] F := (coordinate i p).comp (sliceLinear l i p)
  let d : F := sliceConstant l c i p v i p
  have he (x : Cube (Rest i)) : PrivateTask346CubePrice.quartic (slice l c i p v x i)=K*(L x+d) := by
    rw [quartic_product, ← Finset.mul_prod_erase Finset.univ (fun a => slice l c i p v x i a) (Finset.mem_univ p)]
    have hr : (∏ a ∈ (Finset.univ : Finset (Fin 4)).erase p, slice l c i p v x i a)=K := by
      apply Finset.prod_congr rfl
      intro a ha
      exact slice_local_other l c i p a v x (Finset.mem_erase.mp ha).1
    rw [hr]
    change (L x+d)*K=K*(L x+d)
    ring
  have hc := PrivateTask346CubicClosure.cubic_const_mul _
    (PrivateTask346AffineProducts.cubic_affine L d) K
  simpa only [← he] using hc

def correction (C : I → Fin m → F) (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (v : Label p) (j : Fin m) (x : Cube (Rest i)) : F :=
  C i j*PrivateTask346CubePrice.quartic (slice l c i p v x i)

theorem correction_cubic (C : I → Fin m → F) (l : Cube I →ₗ[F] F) (c : F)
    (i : I) (p : Fin 4) (v : Label p) (j : Fin m) : DegreeThree (correction C l c i p v j) :=
  PrivateTask346CubicClosure.cubic_const_mul _ (slice_quartic_cubic l c i p v) (C i j)

theorem ignored_slice (C : I → Fin m → F) (l : Cube I →ₗ[F] F) (c : F) (i : I) (p : Fin 4)
    (v : Label p) (x : Cube (Rest i)) (j : Fin m) :
    ignored C ∅ (slice l c i p v x) j=
      ignored (fun t : Rest i => C t.val) ∅ x j+correction C l c i p v j x := by
  classical
  simp only [ignored, Finset.notMem_empty, ite_false, correction]
  have h := Fintype.sum_subtype_add_sum_subtype (fun t : I => t≠i)
    (fun t => C t j*PrivateTask346CubePrice.quartic (slice l c i p v x t))
  have hz : (∑ t : {t : I // ¬t≠i}, C t.val j*
      PrivateTask346CubePrice.quartic (slice l c i p v x t.val))=
      C i j*PrivateTask346CubePrice.quartic (slice l c i p v x i) := by
    have hs : (Finset.univ : Finset {t : I // ¬t≠i})={⟨i,by simp⟩} := by
      ext t
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      apply Subtype.ext
      exact not_ne_iff.mp t.property
    rw [hs, Finset.sum_singleton]
  rw [hz] at h
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [slice_other]

end PrivateTask346SliceCubic

namespace PrivateTask346TreeSlices
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice
open PrivateTask346RemoveBlock (Rest)
open PrivateTask346PivotSlice
open PrivateTask346SliceCubic
open PrivateTask346QueryTree

variable {I : Type} [DecidableEq I] [Fintype I] {m h : ℕ}

def residualTree (C : I → Fin m → F) (l : Cube I →ₗ[F] F) (c : F)
    (i : I) (p : Fin 4) (v : Label p) (t : Tree I m h) : Tree (Rest i) m h :=
  pullback t (sliceLinear l i p) (sliceConstant l c i p v)
    (correction C l c i p v) (correction_cubic C l c i p v)

theorem hit_slice (C : I → Fin m → F) (l : Cube I →ₗ[F] F) (c : F)
    (i : I) (p : Fin 4) (hp : l (unit i p)=1) (next : F → Tree I m h)
    (v : Label p) (x : Cube (Rest i)) :
    Hit C (PrivateTask346QueryTree.Tree.node l c next) (slice l c i p v x) ↔
      Hit (fun t : Rest i => C t.val) (residualTree C l c i p v (next v.1)) x := by
  simp only [Hit, error, PrivateTask346QueryTree.Tree.node, residualTree, error_pullback,
    slice_answer l c i p hp, ignored_slice]
  apply forall_congr'
  intro j
  have he : ignored (fun t : Rest i => C t.val) ∅ x j+correction C l c i p v j x+
      error (next v.1) (slice l c i p v x) j=
      ignored (fun t : Rest i => C t.val) ∅ x j+
        (error (next v.1) (slice l c i p v x) j+correction C l c i p v j x) := by ring
  rw [he]
  rfl

theorem card_slices {X V Y : Type} [Finite X] [Fintype V] [Finite Y]
    (e : X ≃ V × Y) (P : X → Prop) (Q : V → Y → Prop)
    (he : ∀ v y, P (e.symm (v,y)) ↔ Q v y) :
    Nat.card {x : X // P x}=∑ v : V, Nat.card {y : Y // Q v y} := by
  have he' (x : X) : P x ↔ Q (e x).1 (e x).2 := by
    simpa only [Prod.mk.eta,Equiv.symm_apply_apply] using he (e x).1 (e x).2
  have eqv : {x : X // P x} ≃ (Σ v : V, {y : Y // Q v y}) :=
    (e.subtypeEquiv he').trans (Equiv.subtypeProdEquivSigmaSubtype Q)
  rw [Nat.card_congr eqv,Nat.card_sigma]

theorem hit_card_slices (C : I → Fin m → F) (l : Cube I →ₗ[F] F) (c : F)
    (i : I) (p : Fin 4) (hp : l (unit i p)=1) (next : F → Tree I m h) :
    Nat.card {z : Cube I // Hit C (PrivateTask346QueryTree.Tree.node l c next) z}=
      ∑ v : Label p, Nat.card {x : Cube (Rest i) //
        Hit (fun t : Rest i => C t.val) (residualTree C l c i p v (next v.1)) x} := by
  exact card_slices (sliceEquiv l c i p hp) _ _ (hit_slice C l c i p hp next)

end PrivateTask346TreeSlices

namespace PrivateTask346TreeUpper
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice
open PrivateTask346RemoveBlock
open PrivateTask346PivotSlice
open PrivateTask346QueryTree
open PrivateTask346TreeSlices

theorem tree_upper (h : ℕ) : ∀ (I : Type) [DecidableEq I] [Fintype I]
    (m : ℕ) (C : I → Fin m → F) (t : Tree I m h),
    Nat.card {z : Cube I // Hit C t z}≤best C h := by
  induction h with
  | zero =>
    intro I _ _ m C t
    rcases t with ⟨q,hq⟩
    simpa only [best_zero,Hit,error] using cubic_count_le_capacity C q hq
  | succ h ih =>
    intro I _ _ m C t
    rcases t with ⟨l,c,next⟩
    by_cases hl : l=0
    · have he : {z : Cube I // Hit C (PrivateTask346QueryTree.Tree.node l c next) z} ≃
          {z : Cube I // Hit C (next c) z} :=
        Equiv.subtypeEquivRight (by intro z; simp only [Hit,error,PrivateTask346QueryTree.Tree.node,hl,LinearMap.zero_apply,zero_add])
      rw [Nat.card_congr he]
      exact (ih I m C (next c)).trans (best_mono C (Nat.le_succ h))
    · obtain ⟨i,p,hp⟩ := exists_pivot l hl
      rw [hit_card_slices C l c i p hp next]
      calc
        _ ≤ ∑ v : Label p, best (fun a : Rest i => C a.val) h := by
          apply Finset.sum_le_sum
          intro v hv
          exact ih (Rest i) m (fun a : Rest i => C a.val)
            (residualTree C l c i p v (next v.1))
        _ = 16*best (fun a : Rest i => C a.val) h := by
          rw [Finset.sum_const,Finset.card_univ,label_card,nsmul_eq_mul]
          norm_num
        _ ≤ best C (h+1) := best_remove C i h

theorem tree_exists_score {s m h : ℕ} (C : Fin s → Fin m → F) (t : Tree (Fin s) m h) :
    ∃ D : Finset (Fin s), D.card≤h ∧
      Nat.card {z : Cube (Fin s) // Hit C t z}≤PrivateTask346IndependentPrice.score C D := by
  obtain ⟨D,hd,he⟩ := best_attained C h
  refine ⟨D,hd,?_⟩
  have hh := tree_upper h (Fin s) m C t
  rw [he,capacity_fin] at hh
  exact hh

end PrivateTask346TreeUpper

namespace PrivateTask346AdaptiveTrace
open PrivateTask346FaceSpace (Raw face face_eq insertLinear)
open PrivateTask346CubicClosure (Blocks)

abbrev F := ZMod 2
def bit (a : F) : ℕ := if a = 0 then 0 else 1
lemma bit_le (a : F) : bit a ≤ 1 := by unfold bit; split_ifs <;> omega
lemma bit_injective : Function.Injective bit := by decide +kernel

variable {α V : Type*} [AddCommGroup V] [Module F V]

def runFrom (n : ℕ) (xs : List α) (A : α → ℕ → V →ₗ[F] F) (x : V) : ℕ :=
  xs.foldl (fun m a => 2*m+bit (A a m x)) n

end PrivateTask346AdaptiveTrace

namespace PrivateTask346QueryProtocol
open PrivateTask346BooleanANF
open PrivateTask346FinitePrice (Cube)
open PrivateTask346QueryTree
open PrivateTask346AffineCubic (DegreeThree)

variable {I α : Type} {m : ℕ}

def runAffine (n : ℕ) (xs : List α) (A : α → ℕ → Cube I →ₗ[F] F)
    (c : α → ℕ → F) (z : Cube I) : ℕ :=
  xs.foldl (fun t a => 2*t+PrivateTask346AdaptiveTrace.bit (A a t z+c a t)) n

def build (n : ℕ) (xs : List α) (A : α → ℕ → Cube I →ₗ[F] F) (c : α → ℕ → F)
    (q : ℕ → Fin m → Cube I → F) (hq : ∀ t j, DegreeThree (q t j)) : Tree I m xs.length :=
  match xs with
  | [] => PrivateTask346QueryTree.Tree.leaf (q n) (hq n)
  | a::ys => PrivateTask346QueryTree.Tree.node (A a n) (c a n) (fun b =>
      build (2*n+PrivateTask346AdaptiveTrace.bit b) ys A c q hq)

theorem error_build (n : ℕ) (xs : List α) (A : α → ℕ → Cube I →ₗ[F] F) (c : α → ℕ → F)
    (q : ℕ → Fin m → Cube I → F) (hq : ∀ t j, DegreeThree (q t j)) (z : Cube I) (j : Fin m) :
    error (build n xs A c q hq) z j=q (runAffine n xs A c z) j z := by
  induction xs generalizing n with
  | nil => rfl
  | cons a ys ih =>
    change error (build (2*n+PrivateTask346AdaptiveTrace.bit (A a n z+c a n)) ys A c q hq) z j=_
    rw [ih]
    rfl

end PrivateTask346QueryProtocol

namespace PrivateTask346ProtocolUpper
open PrivateTask346BooleanANF
open PrivateTask346FaceSpace (Raw face insertLinear face_eq)
open PrivateTask346CubicClosure (Blocks)
open PrivateTask346AffineCubic (DegreeThree cubic_pullback)

def rawHit {k m h : ℕ} (g : Raw k → Fin m → F)
    (ask : Fin h → ℕ → Raw k →ₗ[F] F) (out : ℕ → Fin m → Raw k → F) (w : Raw k) : Prop :=
  let n := (List.finRange h).foldl (fun n a => 2*n+(if ask a n w=0 then 0 else 1)) 0
  ∀ j, g w j=out n j w

theorem trace_face {k s : ℕ} {α : Type} (xs : List α) (ask : α → ℕ → Raw k →ₗ[F] F)
    (ell : Fin s × Fin 4 → Fin k) (base : Raw k) (z : Blocks s) :
    PrivateTask346QueryProtocol.runAffine 0 xs
      (fun a n => (ask a n).comp (insertLinear ell)) (fun a n => ask a n base) z=
      PrivateTask346AdaptiveTrace.runFrom 0 xs ask (face ell base z) := by
  unfold PrivateTask346QueryProtocol.runAffine PrivateTask346AdaptiveTrace.runFrom
  simp only [face_eq,map_add,LinearMap.comp_apply]

theorem local_upper {k s m h : ℕ} (ell : Fin s × Fin 4 → Fin k) (base : Raw k)
    (g : Raw k → Fin m → F) (C : Fin s → Fin m → F) (q : Fin m → Blocks s → F)
    (hq : ∀ j, DegreeThree (q j))
    (decomp : ∀ z j, g (face ell base z) j=
      (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))+q j z)
    (ask : Fin h → ℕ → Raw k →ₗ[F] F) (out : ℕ → Fin m → Raw k → F)
    (hout : ∀ n j, DegreeThree (out n j)) :
    ∃ D : Finset (Fin s), D.card≤h ∧
      Nat.card {z : Blocks s // rawHit g ask out (face ell base z)}≤
        PrivateTask346IndependentPrice.score C D := by
  classical
  let qr : ℕ → Fin m → Blocks s → F := fun n j z => q j z-out n j (face ell base z)
  have hqr (n : ℕ) (j : Fin m) : DegreeThree (qr n j) := by
    have ho := cubic_pullback (insertLinear ell) base (out n j) (hout n j)
    have hn := PrivateTask346CubicClosure.cubic_const_mul _ ho (-1)
    have hs := PrivateTask346CubicClosure.cubic_add _ _ (hq j) hn
    simpa only [qr,face_eq,sub_eq_add_neg,neg_one_mul] using hs
  let T := PrivateTask346QueryProtocol.build 0 (List.finRange h)
    (fun a n => (ask a n).comp (insertLinear ell)) (fun a n => ask a n base) qr hqr
  have hp (z : Blocks s) : PrivateTask346QueryTree.Hit C T z ↔
      rawHit g ask out (face ell base z) := by
    simp only [PrivateTask346QueryTree.Hit,PrivateTask346FinitePrice.ignored,
      Finset.notMem_empty,ite_false,T,PrivateTask346QueryProtocol.error_build,qr,trace_face]
    change (∀ j : Fin m, (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))+
      (q j z-out (PrivateTask346AdaptiveTrace.runFrom 0 (List.finRange h) ask (face ell base z)) j
        (face ell base z))=0) ↔ _
    unfold rawHit
    change (∀ j : Fin m, (∑ i : Fin s, C i j*PrivateTask346CubePrice.quartic (z i))+
      (q j z-out (PrivateTask346AdaptiveTrace.runFrom 0 (List.finRange h) ask (face ell base z)) j
        (face ell base z))=0) ↔
      (∀ j : Fin m, g (face ell base z) j=
        out (PrivateTask346AdaptiveTrace.runFrom 0 (List.finRange h) ask (face ell base z)) j
          (face ell base z))
    apply forall_congr'
    intro j
    rw [← add_sub_assoc,sub_eq_zero,← decomp z j]
  have he : {z : Blocks s // PrivateTask346QueryTree.Hit C T z} ≃
      {z : Blocks s // rawHit g ask out (face ell base z)} := Equiv.subtypeEquivRight hp
  obtain ⟨D,hd,hD⟩ := PrivateTask346TreeUpper.tree_exists_score C T
  refine ⟨D,by simpa using hd,?_⟩
  rw [← Nat.card_congr he]
  exact hD

end PrivateTask346ProtocolUpper

namespace PrivateTask346Averaging
open PrivateTask346FaceSpace
open PrivateTask346CubicClosure (Blocks)

def prodSigmaEquiv {A B : Type*} (P : A × B → Prop) :
    {x : A × B // P x} ≃ ((a : A) × {b : B // P (a,b)}) where
  toFun x := ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  invFun x := ⟨(x.1,x.2.1),x.2.2⟩
  left_inv := by rintro ⟨⟨a,b⟩,h⟩; rfl
  right_inv := by rintro ⟨a,⟨b,h⟩⟩; rfl

theorem card_fibres {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (P : Raw k → Prop) :
    Nat.card {w : Raw k // P w} = ∑ b : NormalBase ell,
      Nat.card {z : Blocks s // P (face ell b.1 z)} := by
  classical
  let Q : NormalBase ell × Blocks s → Prop := fun x => P ((faceEquiv ell he).symm x)
  have e : {x : NormalBase ell × Blocks s // Q x} ≃ {w : Raw k // P w} :=
    Equiv.subtypeEquiv (faceEquiv ell he).symm (fun _ => Iff.rfl)
  calc
    Nat.card {w : Raw k // P w} = Nat.card {x : NormalBase ell × Blocks s // Q x} := Nat.card_congr e.symm
    _ = Nat.card ((b : NormalBase ell) × {z : Blocks s // Q (b,z)}) :=
      Nat.card_congr (prodSigmaEquiv Q)
    _ = ∑ b : NormalBase ell, Nat.card {z : Blocks s // Q (b,z)} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
      simp_rw [← Nat.card_eq_fintype_card]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro z
      change P (insertLinear ell z+b.1) ↔ P (face ell b.1 z)
      rw [face_eq]

theorem whole_bound {k s : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (P : Raw k → Prop) (N : ℕ)
    (hN : ∀ b : NormalBase ell, Nat.card {z : Blocks s // P (face ell b.1 z)} ≤ N) :
    16^s * Nat.card {w : Raw k // P w} ≤ 2^k * N := by
  classical
  have hc : Nat.card {w : Raw k // P w} ≤ Nat.card (NormalBase ell) * N := by
    rw [card_fibres ell he P]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (b : NormalBase ell) _ => hN b)
    simpa [Nat.card_eq_fintype_card] using h
  calc
    16^s * Nat.card {w : Raw k // P w} ≤ 16^s * (Nat.card (NormalBase ell) * N) :=
      Nat.mul_le_mul_left _ hc
    _ = (Nat.card (NormalBase ell) * 16^s) * N := by ring
    _ = 2^k * N := by rw [split_card ell he]

theorem coded_whole_bound {k s m h : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (C : Fin s → Fin m → F) (P : Raw k → Prop)
    (hlocal : ∀ b : Raw k, ∃ D : Finset (Fin s), D.card ≤ h ∧
      Nat.card {z : Blocks s // P (face ell b z)} ≤ PrivateTask346IndependentPrice.score C D) :
    ∃ D : Finset (Fin s), D.card ≤ h ∧
      16^s * Nat.card {w : Raw k // P w} ≤ 2^k * PrivateTask346IndependentPrice.score C D := by
  classical
  let S : Finset (Finset (Fin s)) := Finset.univ.filter fun D => D.card ≤ h
  have hs : S.Nonempty := ⟨∅,by simp [S]⟩
  obtain ⟨D,hd,hmax⟩ := Finset.exists_max_image S (fun D => PrivateTask346IndependentPrice.score C D) hs
  refine ⟨D,(Finset.mem_filter.mp hd).2,?_⟩
  apply whole_bound ell he P
  intro b
  obtain ⟨E,hE,hb⟩ := hlocal b.1
  exact hb.trans (hmax E (by simp [S,hE]))

theorem independent_from_local {k s m h : ℕ} (ell : Fin s × Fin 4 → Fin k) (he : Function.Injective ell)
    (C : Fin s → Fin m → F) (P : Raw k → Prop)
    (hk : ∀ H : Finset (Fin s), (∀ j : Fin m, (∑ i ∈ H, C i j) = 0) → H = ∅)
    (hlocal : ∀ b : Raw k, ∃ D : Finset (Fin s), D.card ≤ h ∧
      Nat.card {z : Blocks s // P (face ell b z)} ≤ PrivateTask346IndependentPrice.score C D) :
    16^(s-h) * Nat.card {w : Raw k // P w} ≤ 15^(s-h) * 2^k := by
  exact PrivateTask346IndependentPrice.independent_fiber_bound k s m h _ C hk
    (coded_whole_bound ell he C P hlocal)

end PrivateTask346Averaging

end PEqualNP.Outside.L_meta_32485_aux

open PEqualNP.Outside.L_meta_32485_aux

theorem PEqualNP.Outside.L_meta_32485 :
∀ (k s m h : ℕ) (hk : 0 < k), 21 ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (s : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + s)) + x (ix (i.val + k - s % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let cubic := fun (f : W → F) => ∀ (v : Fin 4 → W) (x : W), (List.ofFn v).foldl diff f x = 0
  let U := Fin s → Fin 4 → F
  ∀ (u v r₁ r₂ c₁ c₂ : W) (A B : Fin m → Fin k → Bool) (pick : Fin s → Fin k),
    Function.Injective pick →
    (∀ i j : Fin s, i ≠ j → 21 ≤ ((pick j).val+k-(pick i).val) % k) →
    let obs := fun (a : Fin k → Bool) (w : W) => ∑ i : Fin k, if a i then w i else 0
    let value := fun (w : W) (j : Fin m) =>
      let row := step (mix 1 (rot 1 w + u)) + w + r₁
      let col := step (mix 2 (rot 3 w + v)) + rot 4 w + c₁
      obs (A j) (step (mix 1 row) + rot 2 w + r₂) +
        obs (B j) (step (mix 2 col) + rot 7 w + c₂)
    let C := fun (i : Fin s) (j : Fin m) => if B j (pick i) then (1 : F) else 0
    let loc := fun (i : Fin s) (a : Fin 4) =>
      ix ((pick i).val+k-5+(if a.val = 0 then 0 else if a.val = 1 then 1 else if a.val = 2 then 9 else 10))
    let face := fun (base : W) (z : U) (j : Fin k) => base j +
      ∑ i : Fin s, ∑ a : Fin 4, if loc i a = j then z i a else 0
    let score := fun (D : Finset (Fin s)) =>
      ((Finset.univ : Finset (Finset (Fin s))).filter (fun H =>
        Disjoint H D ∧ ∀ j : Fin m, (∑ i ∈ H, C i j) = 0)).sum (fun H =>
          16^D.card * 15^(s-D.card-H.card))
    let Ask := Fin h → ℕ → (W →ₗ[F] F)
    let Out := ℕ → Fin m → W → F
    let hit := fun (ask : Ask) (out : Out) (w : W) =>
      let t := (List.finRange h).foldl (fun n a => 2*n + (if ask a n w = 0 then 0 else 1)) (0 : ℕ)
      ∀ j, value w j = out t j w
    (∀ (base : W) (t : ℕ), (∃ (ask : Ask) (out : Out), (∀ n j, cubic (out n j)) ∧
      t ≤ Nat.card {z : U // hit ask out (face base z)}) ↔
      ∃ D : Finset (Fin s), D.card ≤ h ∧ t ≤ score D) ∧
    (∀ (ask : Ask) (out : Out), (∀ n j, cubic (out n j)) →
      ∃ D : Finset (Fin s), D.card ≤ h ∧
        16^s * Nat.card {w : W // hit ask out w} ≤ 2^k * score D) ∧
    ((∀ H : Finset (Fin s), (∀ j : Fin m, (∑ i ∈ H, C i j) = 0) → H = ∅) →
      ∀ (ask : Ask) (out : Out), (∀ n j, cubic (out n j)) →
        16^(s-h) * Nat.card {w : W // hit ask out w} ≤ 15^(s-h) * 2^k) := by
  intro k s m h hk h21
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  dsimp only
  intro u v r1 r2 c1 c2 A B pick hp sep
  let ell := fun p : Fin s × Fin 4 => PrivateTask346SeparatedLocations.loc hk pick p.1 p.2
  let C := fun i : Fin s => fun j : Fin m => if B j (pick i) then (1 : ZMod 2) else 0
  let g := PrivateTask346ObservationDecomposition.value hk u v r1 r2 c1 c2 A B
  change
    (∀ (base : Fin k → ZMod 2) (t : ℕ),
      (∃ (ask : Fin h → ℕ → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
          (out : ℕ → Fin m → (Fin k → ZMod 2) → ZMod 2),
        (∀ n j, PrivateTask346AffineCubic.DegreeThree (out n j)) ∧
          t≤Nat.card {z : Fin s → Fin 4 → ZMod 2 //
            PrivateTask346ProtocolUpper.rawHit g ask out (PrivateTask346FaceSpace.face ell base z)}) ↔
        ∃ D : Finset (Fin s), D.card≤h ∧ t≤PrivateTask346IndependentPrice.score C D) ∧
    (∀ (ask : Fin h → ℕ → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (out : ℕ → Fin m → (Fin k → ZMod 2) → ZMod 2),
      (∀ n j, PrivateTask346AffineCubic.DegreeThree (out n j)) →
        ∃ D : Finset (Fin s), D.card≤h ∧
          16^s*Nat.card {w : Fin k → ZMod 2 // PrivateTask346ProtocolUpper.rawHit g ask out w}≤
            2^k*PrivateTask346IndependentPrice.score C D) ∧
    ((∀ H : Finset (Fin s), (∀ j : Fin m, (∑ i ∈ H, C i j)=0) → H=∅) →
      ∀ (ask : Fin h → ℕ → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (out : ℕ → Fin m → (Fin k → ZMod 2) → ZMod 2),
      (∀ n j, PrivateTask346AffineCubic.DegreeThree (out n j)) →
        16^(s-h)*Nat.card {w : Fin k → ZMod 2 // PrivateTask346ProtocolUpper.rawHit g ask out w}≤
          15^(s-h)*2^k)
  have hlocal (base : Fin k → ZMod 2)
      (ask : Fin h → ℕ → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (out : ℕ → Fin m → (Fin k → ZMod 2) → ZMod 2)
      (hout : ∀ n j, PrivateTask346AffineCubic.DegreeThree (out n j)) :
      ∃ D : Finset (Fin s), D.card≤h ∧
        Nat.card {z : Fin s → Fin 4 → ZMod 2 //
          PrivateTask346ProtocolUpper.rawHit g ask out (PrivateTask346FaceSpace.face ell base z)}≤
          PrivateTask346IndependentPrice.score C D := by
    obtain ⟨q,hq,he⟩ := PrivateTask346ObservationDecomposition.face_decomposition
      hk h21 u v r1 r2 c1 c2 A B pick hp sep base
    exact PrivateTask346ProtocolUpper.local_upper ell base g C q hq he ask out hout
  have hell : Function.Injective ell := PrivateTask346SeparatedLocations.loc_injective hk h21 pick sep
  refine ⟨?_,?_,?_⟩
  · intro base t
    constructor
    · rintro ⟨ask,out,hout,ht⟩
      obtain ⟨D,hd,hD⟩ := hlocal base ask out hout
      exact ⟨D,hd,ht.trans hD⟩
    · rintro ⟨D,hd,ht⟩
      obtain ⟨ask,out,hout,hcard⟩ := PrivateTask346ActualAttainment.attain_actual_score
        hk h21 u v r1 r2 c1 c2 A B pick hp sep base D hd
      refine ⟨ask,out,hout,?_⟩
      change t≤Nat.card {z : Fin s → Fin 4 → ZMod 2 //
        PrivateTask346ProtocolUpper.rawHit g ask out (PrivateTask346FaceSpace.face ell base z)}
      change Nat.card {z : Fin s → Fin 4 → ZMod 2 //
        PrivateTask346ProtocolUpper.rawHit g ask out (PrivateTask346FaceSpace.face ell base z)}=
          PrivateTask346IndependentPrice.score C D at hcard
      rw [hcard]
      exact ht
  · intro ask out hout
    exact PrivateTask346Averaging.coded_whole_bound ell hell C
      (PrivateTask346ProtocolUpper.rawHit g ask out) (fun base => hlocal base ask out hout)
  · intro hC ask out hout
    exact PrivateTask346Averaging.independent_from_local ell hell C
      (PrivateTask346ProtocolUpper.rawHit g ask out) hC (fun base => hlocal base ask out hout)
