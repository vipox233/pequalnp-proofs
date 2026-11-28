import PEqualNP.Library.Helpers.GraphInversionSeeds

namespace PEqualNP.GraphPriceCalibration

noncomputable section

open Classical GraphInversionSeeds CircuitLowerBounds MetaComplexity

abbrev Rows (m n : Nat) := Fin m → Fin n → Bool
abbrev Trace (m : Nat) := Fin m → Bool
abbrev proj (x : Rows m n) (f : F n) : Trace m := fun k => f (x k)
abbrev R (x : Rows m n) (E : Finset (Edge n)) := (raw E).image (proj x)
abbrev T (x : Rows m n) (E : Finset (Edge n)) := (target E).image (proj x)
abbrev N (x : Rows m n) (S : Finset (Fin n)) := S.image fun i => proj x (neg i)
abbrev bank (x : Rows m n) (E : Finset (Edge n)) (S : Finset (Fin n)) := R x E ∪ N x S
abbrev price (x : Rows m n) (E : Finset (Edge n)) (S : Finset (Fin n)) :=
  ((T x E) \ bank x E S).card
def serves (color : Fin n → Fin c) (S : Finset (Fin n)) := ∀ j, ∃ i∈S, color i=j
def classes (E : Finset (Edge n)) (color : Fin n → Fin c) := ∀ V : Finset (Fin n),
  (∀ e∈E, e.1∈V ↔ e.2∈V) ↔ ∀ i k, color i=color k → (i∈V ↔ k∈V)
def pure (x : Rows m n) (color : Fin n → Fin c) := ∀ j, ∃ a b,
  (∀ i, color i=j → x a i=false ∧ x b i=true) ∧ (∀ i, color i≠j → x a i=x b i)

private theorem reach (part : classes E color) (h : serves color S) : hits E S := by
  intro V hv closed
  obtain ⟨i,hi⟩ := hv
  obtain ⟨k,hk,eq⟩ := h (color i)
  exact ⟨k,((part _).mp closed i k eq.symm).mp hi,hk⟩

private theorem build (x : Rows m n) (E : Finset (Edge n)) (S : Finset (Fin n))
    (L : List (Trace m)) (inputs : L.toFinset=bank x E S) (h : hits E S) :
    sampleFits L (T x E) (price x E S) := by
  classical
  have occupied : (bank x E S).Nonempty := ⟨_,Finset.mem_union_left _
    (Finset.mem_image_of_mem (proj x) (show (fun _ => false)∈raw E by simp [raw]))⟩
  have len : 0<L.length := by
    rw [←inputs] at occupied
    obtain ⟨f,hf⟩ := occupied
    exact List.length_pos_of_mem (List.mem_toFinset.mp hf)
  apply (by simpa only [inputs] using tightBuild L (T x E) len)
  intro U known stable
  let V := (raw E ∪ target E).filter (fun f => proj x f∈U)
  have base : raw E ⊆ V := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf,
      known (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf))⟩
  have seeds : ∀ i∈S, neg i∈V := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (by simp [target]),
      known (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))⟩
  have doneT := grow E S (target E) V h base (by rfl) seeds (by
    rintro f hf ⟨a,ha,b,hb,op⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hf,
      stable _ (Finset.mem_image_of_mem _ hf) ⟨proj x a,(Finset.mem_filter.mp ha).2,
        proj x b,(Finset.mem_filter.mp hb).2,?_⟩⟩
    rcases op with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl)
  intro g hg
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
  exact (Finset.mem_filter.mp (doneT hf)).2

private theorem pureOrder (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (part : classes E color) (j : Fin c) {a b : Fin m}
    (flips : ∀ i, color i=j → x a i=false ∧ x b i=true)
    (fixed : ∀ i, color i≠j → x a i=x b i) :
    ∀ f∈R x E, f a=true → f b=true := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
  have edge (e) (he : e∈E) : color e.1=color e.2 := by
    let V := Finset.univ.filter (fun i => color i=color e.2)
    have closed := (part V).mpr (by intro i k eq; simp [V,eq])
    simpa [V] using (closed e he).mpr (by simp [V])
  simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.mem_image,Finset.mem_univ,true_and] at hg
  rcases hg with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
  · exact id
  · exact id
  · by_cases h : color i=j
    · simp [proj,pos,(flips i h).1]
    · simp [proj,pos,fixed i h]
  · by_cases h : color e.2=j
    · have k := (edge e he).trans h
      simp [proj,eqBit,(flips e.1 k).1,(flips e.1 k).2,(flips e.2 h).1,(flips e.2 h).2]
    · have k : color e.1≠j := by simpa [edge e he] using h
      simp [proj,eqBit,fixed e.1 k,fixed e.2 h]
  · by_cases h : color e.2=j
    · have k := (edge e he).trans h
      simp [proj,xorBit,(flips e.1 k).1,(flips e.2 h).1]
    · have k : color e.1≠j := by simpa [edge e he] using h
      simp [proj,xorBit,fixed e.1 k,fixed e.2 h]

private theorem physical (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (onto : Function.Surjective color) (part : classes E color) (w : pure x color)
    (S : Finset (Fin n)) (L : List (Trace m)) (inputs : L.toFinset=bank x E S) (p : Nat) :
    sampleFits L (T x E) p ↔ serves color S ∧ price x E S≤p := by
  constructor
  · intro fit
    refine ⟨?_,by simpa only [inputs] using countMissing L (T x E) fit⟩
    intro j
    by_contra! missed
    obtain ⟨a,b,flip,fixed⟩ := w j
    have rawOrd := pureOrder x color E part j flip fixed
    obtain ⟨C,mono,_,_,_,all⟩ := fit
    have ord : LowMergeProof.LeL (sampleRow L a) (sampleRow L b) := by
      intro k
      by_cases hk : k<L.length
      · rw [List.getD_eq_getElem _ _ (by simpa [sampleRow] using hk : k<(sampleRow L a).length),
            List.getD_eq_getElem _ _ (by simpa [sampleRow] using hk : k<(sampleRow L b).length)]
        simp only [sampleRow,List.getElem_map]
        have mem : L[k]∈bank x E S := inputs ▸ List.mem_toFinset.mpr (List.getElem_mem hk)
        rcases Finset.mem_union.mp mem with hr|hs
        · exact rawOrd _ hr
        · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp hs
          rw [←eq]; simp [proj,neg,fixed i (missed i hi)]
      · simp [sampleRow,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt hk)]
    obtain ⟨i,hi⟩ := onto j
    obtain ⟨k,_,read⟩ := all (proj x (neg i)) (Finset.mem_image_of_mem _ (by simp [target]))
    have imp := LowMergeProof.wires_mono C (fun g hg => (mono g hg).1) _ _
      (by simp [sampleRow]) ord k
    rw [read a,read b] at imp
    simp [proj,neg,(flip i hi).1,(flip i hi).2] at imp
  · rintro ⟨cover,le⟩
    obtain ⟨C,hm,hr,ho,sz,hf⟩ := build x E S L inputs (reach part cover)
    exact ⟨C,hm,hr,ho,sz.trans le,hf⟩

private theorem ordinary (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (part : classes E color) (w : pure x color) (i : Fin n) : proj x (neg i)∉R x E := by
  intro rawMem
  obtain ⟨a,b,flip,fixed⟩ := w (color i)
  have imp := pureOrder x color E part (color i) flip fixed _ rawMem
  simp [proj,neg,(flip i rfl).1,(flip i rfl).2] at imp

private theorem traceSum (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (part : classes E color) (w : pure x color) (S : Finset (Fin n)) :
    price x E S + (N x S).card = ((T x E)\R x E).card := by
  let P := (T x E)\R x E
  have sub : N x S ⊆ P := by
    rintro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ (by simp [target]),ordinary x color E part w i⟩
  have eq : ((T x E)\bank x E S) = P\N x S := by
    ext f
    simp only [P,bank,Finset.mem_sdiff,Finset.mem_union]; tauto
  unfold price
  rw [eq,Finset.card_sdiff_of_subset sub]
  exact Nat.sub_add_cancel (Finset.card_le_card sub)

private theorem seedCard (x : Rows m n) (color : Fin n → Fin c) (w : pure x color)
    (K : Finset (Fin n)) (inj : Set.InjOn color K) : (N x K).card=K.card := by
  apply Finset.card_image_of_injOn
  intro i hi k hk eq
  apply inj hi hk
  by_contra ne
  obtain ⟨a,b,flip,fixed⟩ := w (color i)
  have v := fixed k (Ne.symm ne)
  have aeq := congrFun eq a
  have beq := congrFun eq b
  simp only [proj,neg,(flip i rfl).1,(flip i rfl).2,Bool.not_false,Bool.not_true,v] at aeq beq
  grind

private theorem fullBound (x : Rows m n) (E : Finset (Edge n)) (sorted : ∀ e∈E,e.1<e.2)
    (S : Finset (Fin n)) : price x E S≤n+3*E.card-S.card := by
  let full := target E \ (raw E ∪ S.image neg)
  have inc : T x E \ bank x E S ⊆ full.image (proj x) := by
    intro f hf
    obtain ⟨ht,absent⟩ := Finset.mem_sdiff.mp hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_image_of_mem
    refine Finset.mem_sdiff.mpr ⟨hg,?_⟩
    intro present
    apply absent
    rcases Finset.mem_union.mp present with hr|hs
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
  exact (Finset.card_le_card inc).trans (Finset.card_image_le.trans
    (le_of_eq (countTargets E sorted S)))

private theorem calibrate (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (sorted : ∀ e∈E,e.1<e.2) (part : classes E color) (w : pure x color)
    (K : Finset (Fin n)) (one : ∀ j, ∃! i, i∈K ∧ color i=j)
    (L : Finset (Fin n) → List (Trace m)) (inputs : ∀ S, (L S).toFinset=bank x E S) :
    (∀ S p, sampleFits (L S) (T x E) p ↔ serves color S ∧ price x E S≤p) ∧
    (∀ S, price x E S+(N x S).card=price x E K+K.card) ∧
    ((∀ p, sampleFits (L K) (T x E) p ↔ n+3*E.card-K.card≤p) ↔
     ∀ S p, sampleFits (L S) (T x E) p ↔ serves color S ∧ n+3*E.card-S.card≤p) := by
  have cov : serves color K := fun j => by
    obtain ⟨i,hi,_⟩ := one j
    exact ⟨i,hi⟩
  have onto : Function.Surjective color := fun j => by
    obtain ⟨i,_,eq⟩ := cov j
    exact ⟨i,eq⟩
  have inj : Set.InjOn color K := by
    intro i hi k hk eq
    exact (one (color k)).unique ⟨hi,eq⟩ ⟨hk,rfl⟩
  have phys := fun S => physical x color E onto part w S (L S) (inputs S)
  have identity (S) : price x E S+(N x S).card=price x E K+K.card := by
    rw [←seedCard x color w K inj,traceSum x color E part w,traceSum x color E part w]
  refine ⟨phys,identity,?_⟩
  constructor
  · intro anchor S p
    have lb := (anchor (price x E K)).mp ((phys K _).mpr ⟨cov,le_rfl⟩)
    have kb : K.card≤n := Finset.card_le_univ K |>.trans (by simp)
    have ub := fullBound x E sorted S
    have cnt : (N x S).card≤S.card := Finset.card_image_le
    have eq := identity S
    have exactPrice : price x E S=n+3*E.card-S.card := by omega
    rw [phys,exactPrice]
  · intro all p
    simpa [cov] using all K p

theorem criterion :
∀ (n m c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c) (x : Fin m → Fin n → Bool),
  (∀ e∈E, e.1<e.2) →
  (∀ V : Finset (Fin n), (∀ e∈E, e.1∈V ↔ e.2∈V) ↔
    ∀ i k, color i=color k → (i∈V ↔ k∈V)) →
  (∀ j, ∃ a b, (∀ i, color i=j → x a i=false ∧ x b i=true) ∧
    (∀ i, color i≠j → x a i=x b i)) →
  ∀ K : Finset (Fin n), (∀ j, ∃! i, i∈K ∧ color i=j) →
  let F := (Fin n → Bool) → Bool
  let inv := fun (i : Fin n) (v : Fin n → Bool) => !(v i)
  let project := fun (f : F) (k : Fin m) => f (x k)
  let raw : Finset F := {fun _ => false,fun _ => true} ∪ Finset.univ.image (fun i v => v i) ∪
    E.image (fun e v => v e.1 == v e.2) ∪ E.image (fun e v => xor (v e.1) (v e.2))
  let targets : Finset F := Finset.univ.image inv ∪ E.image (fun e v => !(v e.1) && !(v e.2)) ∪
    E.image (fun e v => v e.1 && !(v e.2)) ∪ E.image (fun e v => !(v e.1) && v e.2)
  let demand := targets.image project
  let seeds := fun S : Finset (Fin n) => S.image (fun i => project (inv i))
  let bank := fun S => raw.image project ∪ seeds S
  let cost := fun S => (demand \ bank S).card
  let cover := fun (S : Finset (Fin n)) => ∀ j, ∃ i∈S, color i=j
  ∀ (inputs : Finset (Fin n) → List (Fin m → Bool)), (∀ S, (inputs S).toFinset=bank S) →
  let fits := fun S p =>
    let L := inputs S
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length D ∧ D.output<L.length+D.size ∧ D.size≤p ∧
      ∀ f∈demand, ∃ i<L.length+D.size, ∀ k, (D.wires (L.map (fun g => g k))).getD i false=f k
  (∀ S p, fits S p ↔ cover S ∧ cost S≤p) ∧
  (∀ S, cost S+(seeds S).card=cost K+K.card) ∧
  ((∀ p, fits K p ↔ n+3*E.card-K.card≤p) ↔ ∀ S p, fits S p ↔ cover S ∧ n+3*E.card-S.card≤p)
:= by
  intro n m c E color x sorted part pairs K one
  dsimp only
  intro inputs bankEq
  exact calibrate x color E sorted part pairs K one inputs bankEq

end

end PEqualNP.GraphPriceCalibration
