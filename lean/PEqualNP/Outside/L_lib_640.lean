import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_481

namespace PEqualNP.Outside.L_lib_640

abbrev K := ZMod 2

def supp {m : ℕ} (v : Fin m → K) : Finset (Fin m) := Finset.univ.filter (fun i => v i = 1)
def ind {m : ℕ} (s : Finset (Fin m)) (i : Fin m) : K := if i ∈ s then 1 else 0
def witness {n m : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (v : Fin m → K) :=
  A.vecMul v = 0 ∧ dotProduct v b = 1
def dualSets {n m : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun D => (∀ j, D.sum (fun e => A e j) = 0) ∧ D.sum b = 1)
def flaws {n m : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K) := Finset.univ.filter (fun e => (∑ j, A e j * x j) ≠ b e)

theorem twoValues (x : K) : x=0 ∨ x=1 := by fin_cases x; exact Or.inl rfl; exact Or.inr rfl

theorem indSupp {m : ℕ} (v : Fin m → K) : ind (supp v) = v := by
  funext i
  rcases twoValues (v i) with h|h <;> simp [ind,supp,h]

theorem suppInd {m : ℕ} (s : Finset (Fin m)) : supp (ind s) = s := by
  ext i
  by_cases h : i∈s <;> simp [ind,supp,h]

theorem dotInd {m : ℕ} (s : Finset (Fin m)) (v : Fin m → K) : dotProduct (ind s) v = s.sum v := by
  simp [dotProduct,ind,ite_mul,Finset.sum_ite]

theorem setsWitness {n m : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (s : Finset (Fin m)) :
    s ∈ dualSets A b ↔ witness A b (ind s) := by
  simp only [dualSets,Finset.mem_filter,Finset.mem_univ,true_and,witness,dotInd]
  refine and_congr_left (fun _ => ?_)
  constructor
  · intro h; funext j; exact (dotInd s (fun i => A i j)).trans (h j)
  · intro h j
    exact (dotInd s (fun i => A i j)).symm.trans (congrFun h j)

theorem failsIff {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K) (s : Finset (Fin m)) :
    flaws A b x = s ↔ A.mulVec x = b + ind s := by
  have equiv (e : Fin m) : (A.mulVec x e ≠ b e ↔ e ∈ s) ↔ A.mulVec x e = b e + ind s e := by
    rcases twoValues (A.mulVec x e) with h|h <;> rcases twoValues (b e) with k|k <;>
      by_cases he : e∈s <;> simp [h,k,ind,he] <;> decide
  constructor
  · intro h; funext e
    apply (equiv e).mp
    have hm : e ∈ flaws A b x ↔ e ∈ s := by rw [h]
    simpa [flaws,Matrix.mulVec,dotProduct] using hm
  · intro h
    ext e
    simp only [flaws,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (equiv e).mpr (congrFun h e)

theorem nonemptyDual {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (bad : ∀ x, (flaws A b x).Nonempty) : (dualSets A b).Nonempty := by
  obtain ⟨v,hv⟩ := (PEqualNP.Outside.L_lib_481 m n A b).mp (by
    rintro ⟨x,hx⟩
    obtain ⟨e,he⟩ := bad x
    have ne : A.mulVec x e ≠ b e := (Finset.mem_filter.mp he).2
    exact ne (congrFun hx e))
  exact ⟨supp v, (setsWitness A b _).mpr (by rwa [indSupp])⟩

theorem toggles {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b t : Fin m → K)
    (hex : ∃ v, witness A b v) :
    (∃ x, A.mulVec x = b+t) ↔ ∀ v, witness A b v → dotProduct v t = 1 := by
  constructor
  · rintro ⟨x,hx⟩ v ⟨hv,hd⟩
    have h : dotProduct v (b+t) = 0 := by
      rw [←hx, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
    rw [dotProduct_add,hd] at h
    rcases twoValues (dotProduct v t) with k|k
    · simp [k] at h
    · exact k
  · intro h
    by_contra hn
    obtain ⟨v,hv,hd⟩ := (PEqualNP.Outside.L_lib_481 m n A (b+t)).mp hn
    rw [dotProduct_add] at hd
    obtain ⟨u,hu⟩ := hex
    rcases twoValues (dotProduct v b) with h0|h1
    · have hb : witness A b (v+u) := by
        exact ⟨by rw [Matrix.add_vecMul, hv,hu.1,add_zero],by rw [add_dotProduct,h0,hu.2,zero_add]⟩
      have hvu := h _ hb
      rw [add_dotProduct,h u hu] at hvu
      rw [h0,zero_add] at hd
      rw [hd] at hvu
      exact (by decide : (1:K)+1 ≠ 1) hvu
    · rw [h1,h v ⟨hv,h1⟩] at hd
      exact (by decide : (1:K)+1 ≠ 1) hd

theorem realizable {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (hex : (dualSets A b).Nonempty) (s : Finset (Fin m)) :
    (∃ x, flaws A b x = s) ↔ ∀ D ∈ dualSets A b, dotProduct (ind D) (ind s) = 1 := by
  obtain ⟨D,hD⟩ := hex
  have ex : ∃ v, witness A b v := ⟨ind D,(setsWitness A b D).mp hD⟩
  constructor
  · rintro ⟨x,h⟩ E hE
    exact (toggles A b (ind s) ex).mp ⟨x,(failsIff A b x s).mp h⟩ _ ((setsWitness A b _).mp hE)
  · intro h
    obtain ⟨x,hx⟩ := (toggles A b (ind s) ex).mpr (by
      intro v hv
      have hS := (setsWitness A b (supp v)).mpr (by rwa [indSupp])
      simpa [indSupp] using h _ hS)
    exact ⟨x,(failsIff A b x s).mpr hx⟩

theorem oneTest {m : ℕ} (e : Fin m) : ind {e} = Pi.single e 1 := by
  funext i
  by_cases h : i=e
  · subst i; simp [ind]
  · simp [ind,h,Pi.single_eq_of_ne h]

theorem pairTest {m : ℕ} (e f : Fin m) (ne : e≠f) : ind {e,f} = Pi.single e 1 + Pi.single f 1 := by
  funext i
  by_cases he : i=e
  · subst i; simp [ind,Pi.single_eq_of_ne ne]
  by_cases hf : i=f
  · subst i; simp [ind,Pi.single_eq_of_ne he]
  simp [ind,he,hf,Pi.single_eq_of_ne he,Pi.single_eq_of_ne hf]

theorem pairFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (ex : (dualSets A b).Nonempty) (e f : Fin m) (ne : e≠f) :
    (∃ x, flaws A b x = {e,f}) ↔ ∀ D ∈ dualSets A b, (e∈D ↔ f∉D) := by
  rw [realizable A b ex]
  apply forall_congr'; intro D
  apply forall_congr'; intro _
  rw [pairTest e f ne,dotProduct_add,dotProduct_single_one,dotProduct_single_one]
  by_cases he : e∈D <;> by_cases hf : f∈D <;> simp [ind,he,hf] <;> decide

theorem noAlwaysOne {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (ex : (dualSets A b).Nonempty) (none : ∀ i, ∀ x, ∃ j ∈ flaws A b x, j≠i) :
    ∀ i, ∃ D ∈ dualSets A b, i∉D := by
  intro i
  by_contra hn
  push_neg at hn
  obtain ⟨x,hx⟩ := (realizable A b ex {i}).mpr (by
    intro D hD
    rw [oneTest,dotProduct_single_one]
    simp [ind,hn _ hD])
  obtain ⟨j,hj,ne⟩ := none i x
  rw [hx,Finset.mem_singleton] at hj
  contradiction

theorem parametrize {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (ex : (dualSets A b).Nonempty) :
    ∃ (d : ℕ) (e : (Fin d → K) ≃ ↥(dualSets A b)) (row : Fin m → Fin d → K) (off : Fin m → K),
      ∀ x i, i ∈ (e x).val ↔ dotProduct (row i) x + off i = 1 := by
  classical
  obtain ⟨D,hD⟩ := ex
  let v := ind D
  have hv : witness A b v := (setsWitness A b D).mp hD
  let U : Submodule K (Fin m → K) :=
    { carrier := {u | A.vecMul u = 0 ∧ dotProduct u b = 0}
      zero_mem' := by simp, add_mem' := by
        rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
        exact ⟨by rw [Matrix.add_vecMul,hx,hy,add_zero],by rw [add_dotProduct,hx',hy',add_zero]⟩
      smul_mem' := by
        intro a x hx
        rcases twoValues a with rfl|rfl
        · simp
        · simpa using hx }
  have neg1 : (1:K)+1=0 := by decide
  let tr : U ≃ ↥(dualSets A b) :=
    { toFun := fun u => ⟨supp (u.val + v), (setsWitness A b _).mpr (by
        rw [indSupp]
        have hu : A.vecMul u.val = 0 ∧ dotProduct u.val b = 0 := u.property
        exact ⟨by rw [Matrix.add_vecMul,hu.1,hv.1,add_zero],by rw [add_dotProduct,hu.2,hv.2,zero_add]⟩)⟩
      invFun := fun s => ⟨ind s.val + v, by
        have hs := (setsWitness A b s.val).mp s.property
        exact ⟨by rw [Matrix.add_vecMul,hs.1,hv.1,add_zero],by rw [add_dotProduct,hs.2,hv.2,neg1]⟩⟩
      left_inv := by
        intro u
        apply Subtype.ext
        simp only [indSupp]
        funext i
        simp only [Pi.add_apply]
        rcases twoValues (v i) with hc|hc <;> rw [add_assoc,hc] <;> simp [neg1]
      right_inv := by
        intro s
        apply Subtype.ext
        have he : ind s.val + v + v = ind s.val := by
          funext i
          simp only [Pi.add_apply]
          rcases twoValues (v i) with hc|hc <;> rw [add_assoc,hc] <;> simp [neg1]
        simp [he,suppInd] }
  let d := Module.finrank K U
  let base : (Fin d → K) ≃ₗ[K] U := (Module.finBasis K U).equivFun.symm
  let coord (i : Fin m) : (Fin d → K) →ₗ[K] K :=
    (LinearMap.proj i).comp (U.subtype.comp base.toLinearMap)
  let row (i : Fin m) (j : Fin d) := coord i (Pi.single j 1)
  refine ⟨d,base.toEquiv.trans tr,row,v,?_⟩
  intro x i
  have dot : dotProduct (row i) x = coord i x := by
    conv_rhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    have he : (Pi.single j (x j) : Fin d → K) = x j • Pi.single j 1 := by
      rw [← Pi.single_smul,smul_eq_mul,mul_one]
    rw [he,map_smul,smul_eq_mul,mul_comm]
  rw [dot]
  change i ∈ supp ((base x).val + v) ↔ (base x).val i + v i = 1
  simp [supp]


theorem zeroOffsets {m n d : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (e : (Fin d → K) ≃ ↥(dualSets A b)) (row : Fin m → Fin d → K) (off : Fin m → K)
    (eval : ∀ x i, i ∈ (e x).val ↔ dotProduct (row i) x + off i = 1)
    (omitted : ∀ i, ∃ D ∈ dualSets A b, i∉D) :
    ∀ i, row i=0 → off i=0 := by
  intro i hr
  obtain ⟨D,hD,hi⟩ := omitted i
  obtain ⟨x,hx⟩ := e.surjective ⟨D,hD⟩
  rcases twoValues (off i) with h|h
  · exact h
  · exfalso
    have hmem : i∈(e x).val := (eval x i).mpr (by simp [hr,h])
    exact hi (by simpa [hx] using hmem)

theorem unusedRow {m n d : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (e : (Fin d → K) ≃ ↥(dualSets A b)) (row : Fin m → Fin d → K) (off : Fin m → K)
    (eval : ∀ x i, i ∈ (e x).val ↔ dotProduct (row i) x + off i = 1)
    (zeros : ∀ i, row i=0 → off i=0) :
    ∀ i, i ∉ (dualSets A b).biUnion id ↔ row i=0 := by
  intro i
  constructor
  · intro hi
    have test (x : Fin d → K) : dotProduct (row i) x + off i ≠ 1 := by
      intro h
      exact hi (Finset.mem_biUnion.mpr ⟨_,(e x).property,(eval x i).mpr h⟩)
    have off0 : off i=0 := by
      rcases twoValues (off i) with h|h
      · exact h
      · exact False.elim ((test 0) (by simp [h]))
    funext j
    rcases twoValues (row i j) with h|h
    · exact h
    · exact False.elim ((test (Pi.single j 1)) (by simp [dotProduct_single_one,h,off0]))
  · intro h
    intro hi
    obtain ⟨D,hD,hI⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨x,hx⟩ := e.surjective ⟨D,hD⟩
    have hmem : i∈(e x).val := by simpa [hx] using hI
    have := (eval x i).mp hmem
    simp [h,zeros i h] at this

section Matching
variable {X T : Type*} [Fintype X] [DecidableEq X] [Fintype T] [DecidableEq T]

def fixedRows (f : X → X) : Finset X := Finset.univ.filter (fun x => f x = x)
def colorRows (s : X → T) (c : X → Bool) (t : T) (b : Bool) : Finset X :=
  Finset.univ.filter (fun x => s x = t ∧ c x = b)
def legalPairing (s : X → T) (c : X → Bool) (f : X → X) : Prop :=
  Function.Involutive f ∧ ∀ x, f x ≠ x → s (f x) = s x ∧ c (f x) ≠ c x

theorem minimalPairing (s : X → T) (c : X → Bool) :
    ∃ f : X → X, legalPairing s c f ∧
    (∀ g, legalPairing s c g → (fixedRows f).card ≤ (fixedRows g).card) ∧
    ∀ a ∈ fixedRows f, ∀ b ∈ fixedRows f, s a = s b → c a = c b := by
  classical
  have ex : ∃ n, ∃ f : X → X, legalPairing s c f ∧ (fixedRows f).card = n :=
    ⟨_,id,⟨fun _ => rfl, fun x h => False.elim (h rfl)⟩,rfl⟩
  obtain ⟨f,hf,hcard⟩ := Nat.find_spec ex
  have minimal (g) (hg : legalPairing s c g) : (fixedRows f).card ≤ (fixedRows g).card := by
    rw [hcard]; exact Nat.find_min' ex ⟨g,hg,rfl⟩
  refine ⟨f,hf,minimal,?_⟩
  intro a ha b hb hs
  by_contra hdiff
  have ne : a ≠ b := fun h => hdiff (congrArg c h)
  have fa : f a = a := (Finset.mem_filter.mp ha).2
  have fb : f b = b := (Finset.mem_filter.mp hb).2
  let g (x : X) := if x=a then b else if x=b then a else f x
  have ga : g a = b := by simp [g]
  have gb : g b = a := by simp [g,ne.symm]
  have hg : legalPairing s c g := by
    constructor
    · intro x
      by_cases hxa : x=a
      · rw [hxa,ga,gb]
      by_cases hxb : x=b
      · rw [hxb,gb,ga]
      have nfa : f x ≠ a := fun h => hxa (hf.1.injective (h.trans fa.symm))
      have nfb : f x ≠ b := fun h => hxb (hf.1.injective (h.trans fb.symm))
      simp [g,hxa,hxb,nfa,nfb,hf.1 x]
    · intro x hx
      by_cases hxa : x=a
      · subst x; rw [ga]; exact ⟨hs.symm,Ne.symm hdiff⟩
      by_cases hxb : x=b
      · subst x; rw [gb]; exact ⟨hs,hdiff⟩
      simp only [g,if_neg hxa,if_neg hxb] at hx ⊢
      exact hf.2 x hx
  have sub : fixedRows g ⊂ fixedRows f := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      have gx : g x=x := (Finset.mem_filter.mp hx).2
      by_cases hxa : x=a
      · rwa [hxa]
      by_cases hxb : x=b
      · rwa [hxb]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [g,hxa,hxb] using gx⟩
    · intro h
      have hmem : a ∈ fixedRows g := h.symm ▸ ha
      exact ne ((Finset.mem_filter.mp hmem).2.symm.trans ga)
  exact (Nat.not_le_of_lt (Finset.card_lt_card sub)) (minimal g hg)

def matchDeficit (s : X → T) (c : X → Bool) : ℕ :=
  ∑ t, Nat.dist (colorRows s c t false).card (colorRows s c t true).card

theorem exactPairing (s : X → T) (c : X → Bool) :
    IsLeast {k | ∃ f : X → X, legalPairing s c f ∧ (fixedRows f).card = k}
      (matchDeficit s c) := by
  classical
  obtain ⟨f,hf,hmin,hsat⟩ := minimalPairing s c
  let fixed (t : T) (v : Bool) := (colorRows s c t v).filter (fun x => f x=x)
  let moved (t : T) (v : Bool) := (colorRows s c t v).filter (fun x => f x≠x)
  have split (t : T) (v : Bool) : (fixed t v).card + (moved t v).card = (colorRows s c t v).card :=
    Finset.card_filter_add_card_filter_not _
  have fixedMem (t : T) (v : Bool) (x : X) : x ∈ fixed t v ↔ (s x=t ∧ c x=v) ∧ f x=x := by
    simp [fixed,colorRows]
  have movedMem (t : T) (v : Bool) (x : X) : x ∈ moved t v ↔ (s x=t ∧ c x=v) ∧ f x≠x := by
    simp [moved,colorRows]
  have toggle (t : T) (v : Bool) (x : X) (hx : x ∈ moved t v) : f x ∈ moved t (!v) := by
    obtain ⟨⟨hs,hc⟩,hn⟩ := (movedMem t v x).mp hx
    obtain ⟨es,ec⟩ := hf.2 x hn
    refine (movedMem t (!v) _).mpr ⟨⟨es.trans hs,?_⟩,?_⟩
    · rw [hc] at ec
      cases v <;> cases ee : c (f x) <;> simp_all
    · rw [hf.1]; exact Ne.symm hn
  have movedEq (t : T) : (moved t false).card = (moved t true).card :=
    Finset.card_bij' (fun x _ => f x) (fun x _ => f x) (toggle t false) (toggle t true)
      (fun x _ => hf.1 x) (fun x _ => hf.1 x)
  have emptySide (t : T) : (fixed t false).card=0 ∨ (fixed t true).card=0 := by
    by_contra! h
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h.1)
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h.2)
    obtain ⟨⟨hxs,hxc⟩,hxf⟩ := (fixedMem t false _).mp hx
    obtain ⟨⟨hys,hyc⟩,hyf⟩ := (fixedMem t true _).mp hy
    have he := hsat x (by simp [fixedRows,hxf]) y (by simp [fixedRows,hyf]) (hxs.trans hys.symm)
    simp [hxc,hyc] at he
  have fiber (t : T) : ((fixedRows f).filter (fun x => s x=t)).card =
      (fixed t false).card + (fixed t true).card := by
    let each := (fixedRows f).filter (fun x => s x=t)
    have left : each.filter (fun x => c x=false) = fixed t false := by
      ext x; simp [each,fixed,fixedRows,colorRows]; tauto
    have right : each.filter (fun x => ¬ c x=false) = fixed t true := by
      ext x; cases hc : c x <;> simp [each,fixed,fixedRows,colorRows,hc] <;> tauto
    rw [←left,←right]
    exact (Finset.card_filter_add_card_filter_not _).symm
  have total : (fixedRows f).card = matchDeficit s c := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=s) (t:=Finset.univ) (by simp)]
    apply Finset.sum_congr rfl
    intro t _
    rw [fiber]
    have h0 := split t false
    have h1 := split t true
    have h2 := movedEq t
    rcases emptySide t with he|he <;> unfold Nat.dist <;> omega
  exact ⟨⟨f,hf,total⟩,fun k ⟨g,hg,hkg⟩ => total ▸ hkg ▸ hmin g hg⟩


end Matching

theorem oppositeAffine {d : ℕ} (u v : Fin d → K) (a b : K) :
    (∀ x : Fin d → K, dotProduct u x + a = 1 ↔ dotProduct v x + b ≠ 1) ↔
      v = u ∧ decide (b=1) ≠ decide (a=1) := by
  classical
  constructor
  · intro h
    have hz := h 0
    simp only [dotProduct_zero, zero_add] at hz
    have hg (i : Fin d) := h (Pi.single i 1)
    simp only [dotProduct_single_one] at hg
    constructor
    · funext i
      exact (show ∀ a b c d : K, (a=1 ↔ b≠1) → (c+a=1 ↔ d+b≠1) → d=c by decide) a b (u i) (v i) hz (hg i)
    · rcases twoValues a with ha|ha <;> rcases twoValues b with hb|hb <;> simp_all
  · rintro ⟨rfl,hn⟩ x
    rcases twoValues a with ha|ha <;> rcases twoValues b with hb|hb <;>
      rcases twoValues (dotProduct v x) with hx|hx <;> simp_all (config := {decide := true})

theorem paramMatch {m n d : ℕ} (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (e : (Fin d → K) ≃ ↥(dualSets A b)) (row : Fin m → Fin d → K) (off : Fin m → K)
    (mem : ∀ x i, i ∈ (e x).val ↔ dotProduct (row i) x + off i = 1) :
    IsLeast {k : ℕ | ∃ mate : Fin m → Fin m, Function.Involutive mate ∧
      (Finset.univ.filter (fun i => mate i = i)).card = k ∧
      ∀ i, mate i ≠ i → ∃ word, flaws A b word = {i,mate i}}
      (matchDeficit row (fun i => decide (off i=1))) := by
  classical
  have ex : (dualSets A b).Nonempty := ⟨(e 0).val,(e 0).property⟩
  have opposite (i j : Fin m) : (∀ D ∈ dualSets A b, (i∈D ↔ j∉D)) ↔
      row j = row i ∧ decide (off j=1) ≠ decide (off i=1) := by
    rw [←oppositeAffine]
    constructor
    · intro h x
      exact (mem x i).symm.trans ((h (e x).val (e x).property).trans (not_congr (mem x j)))
    · intro h D hD
      obtain ⟨x,hx⟩ := e.surjective ⟨D,hD⟩
      have hx' : (e x).val = D := congrArg Subtype.val hx
      rw [←hx', mem, mem]
      exact h x
  have eq (f : Fin m → Fin m) : legalPairing row (fun i => decide (off i=1)) f ↔
      Function.Involutive f ∧ ∀ i, f i ≠ i → ∃ word, flaws A b word = {i,f i} := by
    apply and_congr_right; intro _
    apply forall_congr'; intro i
    apply forall_congr'; intro ne
    exact ((pairFeasible A b ex i (f i) (Ne.symm ne)).trans (opposite i (f i))).symm
  convert exactPairing row (fun i => decide (off i=1)) using 1
  ext k
  apply exists_congr; intro f
  rw [eq]
  tauto


namespace Spectral

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


end Spectral


open Spectral

theorem deficitBalances {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) :
    matchDeficit row (fun i => decide (off i = 1)) = ∑ t, (bal row off t).natAbs := by
  classical
  unfold matchDeficit
  apply Finset.sum_congr rfl
  intro t _
  have nz (i : Fin m) : off i ≠ 1 ↔ off i = 0 := by generalize off i = z; revert z; decide
  have c0 : colorRows row (fun i => decide (off i = 1)) t false =
      Finset.univ.filter (fun i => row i = t ∧ off i = 0) := by ext i; simp [colorRows,nz]
  have c1 : colorRows row (fun i => decide (off i = 1)) t true =
      Finset.univ.filter (fun i => row i = t ∧ off i = 1) := by ext i; simp [colorRows]
  rw [c0,c1]
  unfold bal Nat.dist
  omega

theorem paramWeights {m d g : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (hz : ∀ i, row i = 0 → off i = 0) (hm : m=2*g+1) (hg : ∀ x, g ≤ weight row off x) :
    (((Finset.univ.filter (fun i => row i = 0)).card=1) ∧ (∀ x, weight row off x = g) ∧
        matchDeficit row (fun i => decide (off i=1)) = 1) ∨
    ((∀ i, row i ≠ 0) ∧ ∃ r : ℕ, 0<r ∧
      (∀ x, weight row off x = g ∨ weight row off x = g + 2^(r-1)) ∧
      2^r * (Finset.univ.filter (fun x => weight row off x = g+2^(r-1))).card = 2^d ∧
      matchDeficit row (fun i => decide (off i=1)) = 2^r-1) := by
  classical
  let Q := bump (bal row off)
  have ident (x : Cube d) : transform Q x = 2*((weight row off x : ℤ) - g) := by
    rw [show Q=bump (bal row off) from rfl, transform_bump, weight_formula]
    omega
  have nonneg (x : Cube d) : 0 ≤ transform Q x := by rw [ident]; have := hg x; omega
  have mass := inv Q 0
  rw [at_zero] at mass
  have positive : 0 < (2:ℤ)^d := by positivity
  have qpos : 0 ≤ Q 0 := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun (i : Cube d) _ => nonneg i)
    rw [mass] at h
    exact nonneg_of_mul_nonneg_right h positive
  let Z := Finset.univ.filter (fun i => row i = 0)
  have q0 : Q 0 = 1 - (Z.card : ℤ) := by
    have none1 : (Finset.univ.filter (fun i => row i = 0 ∧ off i = 1)) = ∅ := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
      rintro ⟨h,ho⟩; rw [hz i h] at ho; exact zero_ne_one ho
    have all0 : (Finset.univ.filter (fun i => row i = 0 ∧ off i = 0)) = Z := by
      ext i; simp [Z]; exact hz i
    simp [Q,bump,bal,none1,all0]; ring
  by_cases hem : Z.Nonempty
  · left
    have card1 : Z.card=1 := by have := Finset.card_pos.mpr hem; omega
    have qzero : Q 0=0 := by rw [q0,card1]; norm_num
    have vanish := zero_of_sign Q qzero nonneg
    have zeroF : Q=0 := funext vanish
    have cons (x : Cube d) : weight row off x=g := by
      have h := ident x
      rw [zeroF] at h
      simp [transform] at h
      omega
    refine ⟨card1,cons,?_⟩
    rw [deficitBalances]
    have bs (a : Cube d) : (bal row off a).natAbs = if a=0 then 1 else 0 := by
      have z := vanish a
      dsimp only [Q,bump] at z
      by_cases h : a=0 <;> simp [h] at * <;> omega
    simp [bs]
  · right
    have hr (i : Fin m) : row i ≠ 0 := fun e => hem ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩⟩
    obtain ⟨U,z,rp,balance,shape⟩ := odd_profile row off hr hm hg
    let r := Module.finrank (ZMod 2) U
    let H := Finset.univ.filter (fun x => weight row off x = g+2^(r-1))
    have coeff : 2^r=2^(r-1)*2 := by
      conv_lhs => rw [←Nat.sub_add_cancel (show 1≤r from rp)]
      rw [pow_succ]
    have binary (x : Cube d) : weight row off x = g ∨ weight row off x=g+2^(r-1) := by
      rw [shape]; split_ifs <;> simp [r]
    refine ⟨hr,r,rp,binary,?_,?_⟩
    · have q1 : Q 0=1 := by rw [q0, Finset.not_nonempty_iff_eq_empty.mp hem]; simp
      rw [q1,mul_one] at mass
      have point (x : Cube d) : transform Q x = if x∈H then (2:ℤ)^r else 0 := by
        rw [ident]; by_cases hh : x∈H
        · have hx := (Finset.mem_filter.mp hh).2
          rw [if_pos hh,hx, Nat.cast_add, add_sub_cancel_left]; exact_mod_cast coeff.trans (Nat.mul_comm _ _) |>.symm
        · rw [if_neg hh]
          have hx := (binary x).resolve_right (fun e => hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩))
          rw [hx]; ring
      simp_rw [point] at mass
      simp [Finset.sum_ite] at mass
      change 2^r*H.card=2^d
      rw [Nat.mul_comm]; exact_mod_cast mass
    · rw [deficitBalances]
      have num (a : Cube d) : (bal row off a).natAbs = if a∈U ∧ a≠0 then 1 else 0 := by
        rw [balance]; split_ifs <;> simp [ch,sgn] <;> split <;> decide
      simp_rw [num]
      rw [Finset.sum_boole]
      have e : Finset.univ.filter (fun a => a∈U ∧ a≠0) = (Finset.univ.filter (fun a => a∈U)).erase 0 := by
        ext a; simp [and_comm]
      rw [e, Finset.card_erase_of_mem (by simp)]
      have cu : Fintype.card U = 2^r := by simpa [r,ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := U))
      rw [Fintype.card_subtype] at cu
      rw [cu]; norm_cast



open Spectral

theorem transferWeight {m d : ℕ} (W : Finset (Finset (Fin m))) (e : Cube d ≃ ↥W)
    (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (member : ∀ x i, i ∈ (e x).val ↔ dotProduct (row i) x + off i = 1) (x : Cube d) :
    weight row off x = (e x).val.card := by
  unfold weight
  congr 1
  ext i
  simpa using (member x i).symm

theorem transferCard {m d : ℕ} (W : Finset (Finset (Fin m))) (e : Cube d ≃ ↥W) :
    2^d=W.card := by simpa [Cube,Fintype.card_fun,ZMod.card] using Fintype.card_congr e

theorem transferHeavy {m d : ℕ} (W : Finset (Finset (Fin m))) (e : Cube d ≃ ↥W)
    (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (member : ∀ x i, i ∈ (e x).val ↔ dotProduct (row i) x + off i = 1) (k : ℕ) :
    (Finset.univ.filter (fun x => weight row off x=k)).card =
      (W.filter (fun D => D.card=k)).card := by
  classical
  refine Finset.card_bij' (fun x _ => (e x).val)
    (fun D hD => e.symm ⟨D,(Finset.mem_filter.mp hD).1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    refine Finset.mem_filter.mpr ⟨(e x).property,?_⟩
    rw [←transferWeight W e row off member]
    exact (Finset.mem_filter.mp hx).2
  · intro D hD
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [transferWeight W e row off member,Equiv.apply_symm_apply]
    exact (Finset.mem_filter.mp hD).2
  · intro x _
    exact e.symm_apply_apply x
  · intro D hD
    simp




end PEqualNP.Outside.L_lib_640

open PEqualNP.Outside.L_lib_640 in
theorem PEqualNP.Outside.L_lib_640 : (∀ (n m : ℕ) (A : Fin m → Fin n → ZMod 2) (b : Fin m → ZMod 2),
  let faults := fun x : Fin n → ZMod 2 =>
    Finset.univ.filter (fun e => (∑ j, A e j * x j) ≠ b e)
  let W := Finset.univ.filter (fun D : Finset (Fin m) =>
    (∀ j, D.sum (fun e => A e j) = 0) ∧ D.sum b = 1)
  let best := fun loss : ℕ => IsLeast
    {k : ℕ | ∃ mate : Fin m → Fin m, Function.Involutive mate ∧
      (Finset.univ.filter (fun i => mate i = i)).card = k ∧
      ∀ e, mate e ≠ e → ∃ word, faults word = {e, mate e}} loss
  (∀ x, (faults x).Nonempty) → (∀ i, ∀ x, ∃ j ∈ faults x, j ≠ i) →
  ∀ g : ℕ, m = 2*g+1 → (∀ D ∈ W, g ≤ D.card) →
    W.Nonempty ∧
    (((Finset.univ \ W.biUnion id).card = 1 ∧ (∀ D ∈ W, D.card = g) ∧ best 1) ∨
     (W.biUnion id = Finset.univ ∧ ∃ r : ℕ, 0 < r ∧
       (∀ D ∈ W, D.card = g ∨ D.card = g+2^(r-1)) ∧
       2^r * (W.filter (fun D => D.card = g+2^(r-1))).card = W.card ∧
       best (2^r-1)))) := by

  classical
  intro n m A b
  dsimp only
  intro bad each g hm least
  let W := dualSets A b
  have ex := nonemptyDual A b bad
  obtain ⟨d,e,row,off,mem⟩ := parametrize A b ex
  have z := zeroOffsets A b e row off mem (noAlwaysOne A b ex each)
  have unused := unusedRow A b e row off mem z
  have count := transferWeight W e row off mem
  have minw (x) : g ≤ Spectral.weight row off x := by
    rw [count]; exact least _ (e x).property
  have best := paramMatch A b e row off mem
  refine ⟨ex, ?_⟩
  rcases paramWeights row off z hm minw with ⟨hone,allw,loss⟩ | ⟨vary,r,hr,wr,freq,loss⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · change (Finset.univ \ W.biUnion id).card = 1
      rw [←hone]
      congr 1
      ext i
      simpa [W] using unused i
    · intro D hD
      obtain ⟨x,hx⟩ := e.surjective ⟨D,hD⟩
      simpa [count x,hx] using allw x
    · rw [loss] at best
      exact best
  · right
    refine ⟨?_, r, hr, ?_, ?_, ?_⟩
    · apply Finset.eq_univ_iff_forall.mpr
      intro i
      by_contra h
      exact vary i ((unused i).mp h)
    · intro D hD
      obtain ⟨x,hx⟩ := e.surjective ⟨D,hD⟩
      simpa [count x,hx] using wr x
    · rw [transferHeavy W e row off mem, transferCard W e] at freq
      exact freq
    · rw [loss] at best
      exact best
