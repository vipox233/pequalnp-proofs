import PEqualNP.Library.Helpers.PivotReports

namespace PEqualNP.PivotSlices

open PivotDependencies PivotReports
variable {n m : Nat}

def exposed (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (S : Finset (Fin m)) :=
  (pull Q S).filter (fun j => ∀ i ∈ pull Q S, j ∉ D i)

def splice (U : Finset (Fin n)) (b : Word n) (z : U → Bit) : Word n :=
  fun i => if h : i ∈ U then z ⟨i,h⟩ else b i

def extended (D : Fin n → Finset (Fin n)) (U : Finset (Fin n)) (i : Fin n) := D i ∪ Uᶜ

private theorem uncovered (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) (S : Finset (Fin m)) :
    ¬Covered (extended D U) (pull Q S) ↔ ∃ j ∈ U, j ∈ exposed D Q S := by
  classical
  unfold Covered exposed extended
  simp only [Finset.mem_union,Finset.mem_compl,Finset.mem_filter]
  push_neg
  constructor
  · rintro ⟨j,hj,h⟩
    exact ⟨j,(h j hj).2,hj,fun i hi => (h i hi).1⟩
  · rintro ⟨j,hU,hj,h⟩
    exact ⟨j,hj,fun i hi => ⟨h i hi,hU⟩⟩

private def fullEquiv (U : Finset (Fin n)) : Word n ≃ (U → Bit) × (↥(Uᶜ) → Bit) where
  toFun x := (fun i => x i,fun i => x i)
  invFun z := fun i => if h : i ∈ U then z.1 ⟨i,h⟩ else z.2 ⟨i,Finset.mem_compl.mpr h⟩
  left_inv x := by
    funext i
    by_cases hi : i ∈ U <;> simp [hi]
  right_inv z := by
    apply Prod.ext <;> funext i
    · simp [i.property]
    · simp [Finset.mem_compl.mp i.property]

private theorem sliceCard (U : Finset (Fin n)) (f : (U → Bit) → Word m) (v : Word m) :
    Nat.card {x : Word n // f (fun i => x i) = v} =
    Nat.card {z : U → Bit // f z = v} * 2^(Uᶜ.card) := by
  classical
  let e : {x : Word n // f (fun i => x i) = v} ≃
      {z : U → Bit // f z = v} × (↥(Uᶜ) → Bit) :=
    { toFun := fun x => (⟨(fullEquiv U x.val).1,x.property⟩,(fullEquiv U x.val).2)
      invFun := fun y => ⟨(fullEquiv U).symm (y.1.val,y.2),by
        change f ((fullEquiv U ((fullEquiv U).symm (y.1.val,y.2))).1) = v
        simpa using y.1.property⟩
      left_inv := fun x => Subtype.ext ((fullEquiv U).symm_apply_apply x.val)
      right_inv := fun y => by
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst ((fullEquiv U).apply_symm_apply (y.1.val,y.2))
        · exact congrArg (fun t : (U → Bit) × (↥(Uᶜ) → Bit) => t.2) ((fullEquiv U).apply_symm_apply (y.1.val,y.2)) }
  rw [Nat.card_congr e,Nat.card_prod]
  simp [Nat.card_eq_fintype_card,Finset.card_compl]

theorem sliceCriterion (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (U : Finset (Fin n)) :
    let hit := ∀ S : Finset (Fin m), S.Nonempty → ∃ j ∈ U, j ∈ exposed D Q S
    let F := fun (T : Tail n) (b : Word n) (z : U → Bit) => report Q (output T (splice U b z))
    ((∀ T, Local D T → ∀ b v, 2^m * Nat.card {z : U → Bit // F T b z = v} = 2^U.card) ↔ hit) ∧
    ((∀ T, Local D T → ∀ b, Function.Surjective (F T b)) ↔ hit) := by
  classical
  dsimp only
  let DU := extended D U
  have ordinary := criterion DU Q
  have eqCount (hit : ∀ S : Finset (Fin m), S.Nonempty → ∃ j ∈ U, j ∈ exposed D Q S)
      (T : Tail n) (ltail : Local D T) (b : Word n) (v : Word m) := by
    let c (x : Word n) := splice U b (fun i => x i)
    let E : Tail n := fun i x => T i (c x) + (c x i + x i)
    have loc : Local DU E := by
      intro i x y xy
      have tails : T i (c x) = T i (c y) := ltail i _ _ (fun j hj => by
        by_cases hu : j ∈ U
        · exact (by simpa [c,splice,hu] using xy j (Finset.mem_union_left _ hj))
        · simp [c,splice,hu])
      simp only [E,tails]
      by_cases hi : i ∈ U
      · simp [c,splice,hi,CharTwo.add_self_eq_zero]
      · have e := xy i (Finset.mem_union_right _ (Finset.mem_compl.mpr hi))
        simp [c,splice,hi,e]
    have out (x : Word n) : output E x = output T (c x) := by
      funext i
      simp only [E,output]
      rw [show x i + (T i (c x) + (c x i + x i)) =
        c x i + T i (c x) + (x i + x i) by ac_rfl,CharTwo.add_self_eq_zero,add_zero]
    have hz := ordinary.1.mpr (fun S hn => (uncovered D Q U S).2 (hit S hn)) E loc v
    simp_rw [out] at hz
    let f := fun z : U → Bit => report Q (output T (splice U b z))
    change 2^m * Nat.card {x : Word n // f (fun i => x i) = v} = 2^n at hz
    rw [sliceCard] at hz
    have size : U.card + Uᶜ.card = n := by simpa [add_comm] using Finset.card_compl_add_card U
    have powers : (2:Nat)^n = 2^U.card * 2^Uᶜ.card := (congrArg (fun t : Nat => 2^t) size.symm).trans (pow_add _ _ _)
    rw [powers,← Nat.mul_assoc] at hz
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^Uᶜ.card) hz
  have ontoOfCount (T : Tail n) (b : Word n)
      (good : ∀ v, 2^m * Nat.card {z : U → Bit // report Q (output T (splice U b z)) = v} = 2^U.card) :
      Function.Surjective (fun z => report Q (output T (splice U b z))) := by
    intro v
    have pos : 0 < Nat.card {z : U → Bit // report Q (output T (splice U b z)) = v} := by
      by_contra! hn
      have h := good v
      rw [Nat.eq_zero_of_le_zero hn,mul_zero] at h
      exact (by positivity : 0 < 2^U.card).ne h
    obtain ⟨z,h⟩ := (Nat.card_pos_iff.mp pos).1
    exact ⟨z,h⟩
  have hitOfOnto (onto : ∀ T, Local D T → ∀ b : Word n,
      Function.Surjective (fun z : U → Bit => report Q (output T (splice U b z)))) :
      ∀ S : Finset (Fin m), S.Nonempty → ∃ j ∈ U, j ∈ exposed D Q S := by
    have all : ∀ E, Local DU E → Function.Surjective (fun x => report Q (output E x)) := by
      intro E eloc v
      let T : Tail n := fun i x => E i (splice U 0 (fun j => x j))
      have loc : Local D T := by
        intro i x y xy
        apply eloc
        intro j hj
        by_cases hu : j ∈ U
        · have hd : j ∈ D i := (Finset.mem_union.mp hj).resolve_right (by simpa using hu)
          simpa [splice,hu] using xy j hd
        · simp [splice,hu]
      obtain ⟨z,hz⟩ := onto T loc 0 v
      refine ⟨splice U 0 z,?_⟩
      have sp : splice U 0 (fun j : U => splice U 0 z j) = splice U 0 z := by
        congr 1
        funext i
        simp [splice,i.property]
      have out : output T (splice U 0 z) = output E (splice U 0 z) := by
        funext i
        simp [output,T,sp]
      exact (congrArg (report Q) out).symm.trans hz
    exact fun S hn => (uncovered D Q U S).1 (ordinary.2.mp all S hn)
  exact ⟨⟨fun h => hitOfOnto (fun T ht b => ontoOfCount T b (h T ht b)),eqCount⟩,
    ⟨hitOfOnto,fun h T ht b => ontoOfCount T b (eqCount h T ht b)⟩⟩

end PEqualNP.PivotSlices
