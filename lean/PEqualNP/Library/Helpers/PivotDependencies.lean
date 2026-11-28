import Mathlib

namespace PEqualNP.PivotDependencies

abbrev Bit := ZMod 2
abbrev Word (n : Nat) := Fin n → Bit
abbrev Tail (n : Nat) := Fin n → Word n → Bit

def Local {n : Nat} (D : Fin n → Finset (Fin n)) (T : Tail n) : Prop :=
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

def output {n : Nat} (T : Tail n) (x : Word n) (i : Fin n) : Bit := x i + T i x

def parity {n : Nat} (S : Finset (Fin n)) (x : Word n) : Bit := ∑ i : S, x i

def Covered {n : Nat} (D : Fin n → Finset (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ j ∈ S, ∃ i ∈ S, j ∈ D i

private theorem double (a : Bit) : a+a=0 := by
  fin_cases a <;> decide

private def flip {n : Nat} (j : Fin n) (x : Word n) : Word n :=
  fun i => x i + if i=j then 1 else 0

private theorem twice {n : Nat} (j : Fin n) (x : Word n) : flip j (flip j x) = x := by
  funext i
  by_cases h : i=j <;> simp [flip,h,add_assoc,double]

theorem balanced {n : Nat} {D : Fin n → Finset (Fin n)} {S : Finset (Fin n)}
    (miss : ¬ Covered D S) (T : Tail n) (hT : Local D T) :
    Nat.card {x : Word n // parity S (output T x) = 0} =
    Nat.card {x : Word n // parity S (output T x) = 1} := by
  classical
  unfold Covered at miss
  push_neg at miss
  obtain ⟨j,hj,hmiss⟩ := miss
  let jS : S := ⟨j,hj⟩
  have changeBit (x : Word n) : parity S (output T (flip j x)) = parity S (output T x)+1 := by
    have term (i : S) : output T (flip j x) i = output T x i + if i=jS then 1 else 0 := by
      have tail := hT i (flip j x) x (fun k hk => by
        have ne : k ≠ j := fun eq => hmiss i i.property (eq ▸ hk)
        simp [flip,ne])
      rw [output,output,tail]
      have eqv : (i : Fin n) = j ↔ i=jS := ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simp only [flip,eqv]
      ac_rfl
    simp [parity,term,Finset.sum_add_distrib]
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨flip j x.1, by rw [changeBit,x.2,zero_add]⟩
    invFun := fun x => ⟨flip j x.1, by rw [changeBit,x.2,double]⟩
    left_inv := fun x => Subtype.ext (twice j x.1)
    right_inv := fun x => Subtype.ext (twice j x.1) }

theorem lock {n : Nat} {D : Fin n → Finset (Fin n)} {S : Finset (Fin n)}
    (cover : Covered D S) (v : Word n) :
    ∃ T : Tail n, Local D T ∧ output T 0 = v ∧
      ∀ x : Word n, parity S (output T x) = parity S v := by
  classical
  have chooseOwner (j : S) : ∃ i : S, j.val ∈ D i := by
    obtain ⟨i,hi,hj⟩ := cover j j.property
    exact ⟨⟨i,hi⟩,hj⟩
  choose owner reads using chooseOwner
  let T : Tail n := fun i x => v i + ∑ j : S, if (owner j).val=i then x j else 0
  refine ⟨T,?_,?_,?_⟩
  · intro i x y same
    apply congrArg (v i + ·)
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · exact same j (h ▸ reads j)
    · rfl
  · funext i
    simp [output,T]
  · intro x
    have sum : (∑ i : S, ∑ j : S, if (owner j).val=i.val then x j else 0) = parity S x := by
      rw [Finset.sum_comm]
      simp [parity,Subtype.val_inj]
    simp only [parity,output,T,Finset.sum_add_distrib]
    rw [sum]
    unfold parity
    rw [add_left_comm,double,add_zero]


def sign (b : Bit) : ℤ := if b=0 then 1 else -1

theorem sign_add (a b : Bit) : sign (a+b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> decide

private theorem productSign {n : Nat} (S : Finset (Fin n)) (x : Word n) :
    (∏ i ∈ S, sign (x i)) = sign (parity S x) := by
  classical
  unfold parity
  rw [Finset.sum_coe_sort]
  induction S using Finset.induction_on with
  | empty => simp [sign]
  | insert i S hi ih => simp [hi,ih,sign_add]

theorem characterCount {n : Nat} (S : Finset (Fin n)) (T : Tail n) :
    ∑ x : Word n, sign (parity S (output T x)) =
      (Nat.card {x : Word n // parity S (output T x)=0} : ℤ) -
      (Nat.card {x : Word n // parity S (output T x)=1} : ℤ) := by
  classical
  have bit (b : Bit) : sign b = (if b=0 then (1:ℤ) else 0) - (if b=1 then 1 else 0) := by
    fin_cases b <;> decide
  simp_rw [bit]
  rw [Finset.sum_sub_distrib]
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem point {n : Nat} (x v : Word n) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, sign (parity S x) * sign (parity S v) =
      if x=v then (2:ℤ)^n else 0 := by
  classical
  have expand : (∏ i : Fin n, (sign (x i) * sign (v i) + 1)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, sign (parity S x) * sign (parity S v) := by
    rw [Finset.prod_add]
    simp [Finset.prod_mul_distrib,productSign]
  rw [← expand]
  by_cases h : x=v
  · subst v
    have two (b : Bit) : sign b * sign b + 1 = 2 := by fin_cases b <;> decide
    simp [two]
  · obtain ⟨i,ne⟩ : ∃ i, x i ≠ v i := Function.ne_iff.mp h
    have opp (a b : Bit) (ab : a≠b) : sign a * sign b + 1 = 0 := by
      fin_cases a <;> fin_cases b <;> first | rfl | contradiction
    simp only [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (opp _ _ ne)

noncomputable def fiber {n : Nat} (T : Tail n) (v : Word n) := Nat.card {x : Word n // output T x=v}

private theorem inversion {n : Nat} (T : Tail n) (v : Word n) :
    (2:ℤ)^n * fiber T v =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∑ x : Word n, sign (parity S (output T x))) * sign (parity S v) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [point]
  simp [fiber,Nat.card_eq_fintype_card,Fintype.card_subtype,mul_comm]
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem distinguish {n : Nat} (D : Fin n → Finset (Fin n)) (v w : Word n) :
    (∀ T, Local D T → fiber T v = fiber T w) ↔
      ∀ S, Covered D S → parity S v = parity S w := by
  classical
  constructor
  · intro same S hS
    by_contra different
    obtain ⟨T,localT,origin,constant⟩ := lock hS v
    letI inhabited : Nonempty {x : Word n // output T x=v} := ⟨⟨0,origin⟩⟩
    letI empty : IsEmpty {x : Word n // output T x=w} := ⟨fun ⟨x,hx⟩ =>
      different ((constant x).symm.trans (congrArg (parity S) hx))⟩
    have h := same T localT
    unfold fiber at h
    have zero : Nat.card {x : Word n // output T x=w} = 0 := by simp [Nat.card_eq_fintype_card]
    exact Nat.card_pos.ne' (h.trans zero)
  · intro agree T localT
    have sums : (2:ℤ)^n * fiber T v = (2:ℤ)^n * fiber T w := by
      rw [inversion,inversion]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : Covered D S
      · rw [agree S hS]
      · rw [characterCount,balanced hS T localT,sub_self,zero_mul,zero_mul]
    exact_mod_cast (mul_left_cancel₀ (show (2:ℤ)^n ≠ 0 by positivity) sums)


/-- Every permitted update permutes the raw words exactly when no nonempty covered mask exists. -/
theorem permutationCriterion {n : Nat} (D : Fin n → Finset (Fin n)) :
    (∀ T, Local D T → Function.Bijective (output T)) ↔
      ∀ S, Covered D S → S = ∅ := by
  classical
  constructor
  · intro permutes S cover
    by_contra ne
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr ne
    obtain ⟨T,allowed,_,constant⟩ := lock cover (0 : Word n)
    let one : Word n := fun j => if j=i then 1 else 0
    obtain ⟨x,hx⟩ := (permutes T allowed).surjective one
    have bad := constant x
    rw [hx] at bad
    unfold parity at bad
    rw [Finset.sum_coe_sort,Finset.sum_coe_sort] at bad
    simpa [one,hi] using bad
  · intro closedMasks T allowed
    suffices onto : Function.Surjective (output T) from
      ⟨(Finite.injective_iff_surjective).mpr onto,onto⟩
    intro v
    let w := output T 0
    have counts := (distinguish D w v).2 (fun S hS => by rw [closedMasks S hS]; simp [parity]) T allowed
    letI : Nonempty {x : Word n // output T x=w} := ⟨⟨0,rfl⟩⟩
    have positive : 0 < fiber T w := Nat.card_pos
    rw [counts] at positive
    have someInput : Nonempty {x : Word n // output T x=v} := Nat.card_pos_iff.mp positive |>.1
    obtain ⟨x,hx⟩ := someInput
    exact ⟨x,hx⟩

end PEqualNP.PivotDependencies

theorem PEqualNP.PivotDependencies.complete : (
∀ (n : Nat) (D : Fin n → Finset (Fin n)),
  let W := Fin n → ZMod 2
  let localT := fun (T : Fin n → W → ZMod 2) =>
    ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
  let out := fun (T : Fin n → W → ZMod 2) (x : W) (i : Fin n) => x i + T i x
  let parity := fun (S : Finset (Fin n)) (x : W) => ∑ i : S, x i
  let covered := fun (S : Finset (Fin n)) => ∀ j ∈ S, ∃ i ∈ S, j ∈ D i
  let fiber := fun (T : Fin n → W → ZMod 2) (v : W) => Nat.card {x : W // out T x = v}
  (∀ S : Finset (Fin n),
    (¬ covered S → ∀ T, localT T →
      Nat.card {x : W // parity S (out T x) = 0} =
      Nat.card {x : W // parity S (out T x) = 1}) ∧
    (covered S → ∀ v : W, ∃ T, localT T ∧ out T 0 = v ∧
      ∀ x : W, parity S (out T x) = parity S v)) ∧
  (∀ v w : W, (∀ T, localT T → fiber T v = fiber T w) ↔
    ∀ S, covered S → parity S v = parity S w)
) := by
  intro n D
  dsimp only
  exact ⟨fun S => ⟨fun h T ht => PEqualNP.PivotDependencies.balanced h T ht,
    fun h v => PEqualNP.PivotDependencies.lock h v⟩, PEqualNP.PivotDependencies.distinguish D⟩
