import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_782_aux

private def comp {I : Type} (a b : I → Bool) : Prop :=
  (∀ j, a j = true → b j = true) ∨ (∀ j, b j = true → a j = true)

private def possible (f : Bool → Bool) (p q a b : Bool) : Prop :=
  (∃ s t : Bool, s ≤ t ∧ f s = a ∧ f t = b) ∨
  ((p = q → a = b) ∧ ((f p ≤ a ∧ f q ≤ b) ∨ (a ≤ f p ∧ b ≤ f q)))

private theorem conflict : ∀ (f : Bool → Bool) (p q : Bool), p ≤ q →
    possible f p q false true → possible f p q true false →
    p = false ∧ q = true ∧ f false = f true := by
  unfold possible
  decide +kernel

private theorem mismatch {I : Type} {a b : I → Bool} (h : ¬ ∀ j, a j = true → b j = true) :
    ∃ j, a j = true ∧ b j = false := by
  classical
  push Not at h
  obtain ⟨j,hj,hb⟩ := h
  exact ⟨j,hj,by cases e : b j <;> simp_all⟩

private theorem imp_le : ∀ a b : Bool, (a = true → b = true) → a ≤ b := by decide

private theorem ins {I : Type} [DecidableEq I] (i : I) (s : Finset I) :
    {i} ∩ s = if i ∈ s then {i} else ∅ := by
  split <;> ext x <;> simp_all

private theorem exs {I : Type} [DecidableEq I] (i r : I) (s : Finset I) :
    (({i} : Finset I) \ s).erase r = if i = r ∨ i ∈ s then ∅ else {i} := by
  split <;> ext x <;> simp_all <;> aesop

private def cell {n m} (A : Fin n → Fin m → Bool) (r : Fin n) (c : Fin m)
    (S : Finset (Fin n)) (T : Finset (Fin m))
    (W : Finset (Fin n) → Finset (Fin m) → Bool)
    (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool) :=
  ∀ i j, A i j = K (if i ∈ S then {i} else ∅) (if j ∈ T then {j} else ∅)
    (W (if i = r ∨ i ∈ S then ∅ else {i}) (if j = c ∨ j ∈ T then ∅ else {j}))

private theorem classify {n m} (A : Fin n → Fin m → Bool) (r u : Fin n) (c : Fin m)
    (S : Finset (Fin n)) (T : Finset (Fin m)) (W : Finset (Fin n) → Finset (Fin m) → Bool)
    (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool) (inj : Function.Injective A)
    (hr : r ∉ S) (hc : c ∉ T) (hu : u ∉ S) (hur : u ≠ r) (hbad : ¬ comp (A r) (A u))
    (hq : ∀ j ∈ T, comp (fun i => A i c) (fun i => A i j))
    (hm : ∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true)
    (rep : cell A r c S T W K) :
    (∀ i, i ∉ S ↔ i = r ∨ i = u) ∧ K ∅ ∅ false = K ∅ ∅ true ∧ W ∅ ∅ = false ∧ W {u} ∅ = true := by
  let f := K ∅ ∅
  let p := W ∅ ∅
  let q := W {u} ∅
  have pq : p ≤ q := imp_le _ _ (hm _ _ _ _ (by simp) (by rfl))
  have ac : A r c = f p := by simpa [f,p,hr,hc] using rep r c
  have bc : A u c = f q := by simpa [f,q,hur,hu,hc] using rep u c
  have poss (j : Fin m) : possible f p q (A r j) (A u j) := by
    by_cases hj : j ∈ T
    · right
      have ar : A r j = K ∅ {j} p := by simpa [hr,hj,p] using rep r j
      have bu : A u j = K ∅ {j} q := by simpa [hu,hur,hj,q] using rep u j
      refine ⟨fun e => by rw [ar,bu,e],?_⟩
      rw [← ac,← bc]
      obtain h | h := hq j hj
      · exact Or.inl ⟨imp_le _ _ (h r),imp_le _ _ (h u)⟩
      · exact Or.inr ⟨imp_le _ _ (h r),imp_le _ _ (h u)⟩
    · left
      let Y : Finset (Fin m) := if j = c then ∅ else {j}
      exact ⟨W ∅ Y,W {u} Y,imp_le _ _ (hm _ _ _ _ (by simp) (by rfl)),
        by simpa [hr,hj,f,Y] using (rep r j).symm,by simpa [hu,hur,hj,f,Y] using (rep u j).symm⟩
  obtain ⟨j,hj,hj'⟩ := mismatch (fun h => hbad (.inl h))
  obtain ⟨k,hk,hk'⟩ := mismatch (fun h => hbad (.inr h))
  obtain ⟨pf,qt,constant⟩ := conflict f p q pq (by simpa [hk,hk'] using poss k) (by simpa [hj,hj'] using poss j)
  refine ⟨?_,constant,pf,qt⟩
  intro i
  refine ⟨fun hi => ?_,by rintro (rfl|rfl) <;> assumption⟩
  by_cases ir : i = r
  · exact .inl ir
  have allsame (a b : Bool) : f a = f b := by cases a <;> cases b <;> simp_all
  cases h : W {i} ∅ with
  | false =>
    left
    apply inj
    funext j
    by_cases jt : j ∈ T
    · simpa [rep i j,rep r j,hi,hr,ir,jt,h] using congrArg (K ∅ {j}) pf.symm
    · simpa [rep i j,rep r j,hi,hr,ir,jt,f] using allsame (W {i} (if j = c then ∅ else {j})) (W ∅ (if j = c then ∅ else {j}))
  | true =>
    right
    apply inj
    funext j
    by_cases jt : j ∈ T
    · simpa [rep i j,rep u j,hi,hu,ir,hur,jt,h] using congrArg (K ∅ {j}) qt.symm
    · simpa [rep i j,rep u j,hi,hu,ir,hur,jt,f] using allsame (W {i} (if j = c then ∅ else {j})) (W {u} (if j = c then ∅ else {j}))

end PEqualNP.Outside.L_lib_782_aux

open PEqualNP.Outside.L_lib_782_aux

theorem PEqualNP.Outside.L_lib_782 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool)
    (r : Fin n) (c : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (W : Finset (Fin n) → Finset (Fin m) → Bool)
    (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool),
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  r ∉ S → c ∉ T → (∀ i ∈ S, rc r i) → (∀ j ∈ T, cc c j) →
  (∃ u, ¬ rc r u) → (∃ v, ¬ cc c v) →
  (∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true) →
  (∀ i j, let x : Finset (Fin n) := {i}
          let y : Finset (Fin m) := {j}
          A i j = K (x ∩ S) (y ∩ T) (W ((x \ S).erase r) ((y \ T).erase c))) →
  ∃ (u : Fin n) (v : Fin m), ¬ rc r u ∧ ¬ cc c v ∧
    (∀ i, i ∉ S ↔ i = r ∨ i = u) ∧ (∀ j, j ∉ T ↔ j = c ∨ j = v) ∧
    K ∅ ∅ false = K ∅ ∅ true ∧ W ∅ ∅ = false ∧ W {u} ∅ = true ∧
    W ∅ {v} = true ∧ W {u} {v} = true := by
  intro n m A r c S T W K
  dsimp only
  intro hinj cinj hr hc hS hT exr exc hm hrep
  obtain ⟨u,hu⟩ := exr
  obtain ⟨v,hv⟩ := exc
  have hus : u ∉ S := fun h => hu (hS u h)
  have hvt : v ∉ T := fun h => hv (hT v h)
  have ur : u ≠ r := by rintro rfl; exact hu (.inl (fun _ x => x))
  have vc : v ≠ c := by rintro rfl; exact hv (.inl (fun _ x => x))
  have rep : cell A r c S T W K := by
    intro i j
    simpa only [ins,exs] using hrep i j
  obtain ⟨rows,co,w0,wu⟩ := classify A r u c S T W K hinj hr hc hus ur hu hT hm rep
  obtain ⟨cols,_,_,wv⟩ := classify (fun j i => A i j) c v r T S (fun y x => W x y)
    (fun y x => K x y) cinj hc hr hvt vc hv hS
    (fun _ _ _ _ h1 h2 => hm _ _ _ _ h2 h1) (fun j i => rep i j)
  exact ⟨u,v,hu,hv,rows,cols,co,w0,wu,wv,hm _ _ _ _ (by simp) (by rfl) wv⟩
