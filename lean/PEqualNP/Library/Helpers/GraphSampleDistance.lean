import PEqualNP.Library.Helpers.GraphPriceCalibration
import PEqualNP.Library.Helpers.GraphSeedSamples

namespace PEqualNP.GraphSampleDistance

noncomputable section
open Classical GraphInversionSeeds GraphPriceCalibration CircuitLowerBounds MetaComplexity

abbrev W (n : Nat) := Finset (Fin n)
abbrev asWord (f : F n) (u : W n) := f (fun i => decide (i ∈ u))
abbrev req (E : Finset (Edge n)) := (target E).image asWord
abbrev wire (E : Finset (Edge n)) (S : W n) := (GraphSeedSamples.bank E S).toList

def fitsAt (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) (p : Nat) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack (wire E S).length C ∧
    C.output < (wire E S).length+C.size ∧ C.size≤p ∧ ∀ f∈req E, ∃ j<(wire E S).length+C.size,
      ∀ u∈A, (C.wires ((wire E S).map (fun g => g u))).getD j false=f u

def keeps (A : Finset (W n)) (E : Finset (Edge n)) (color : Fin n → Fin c) :=
  ∀ S p, fitsAt A E S p ↔ GraphSeedSamples.cover color S ∧ n+3*E.card-S.card≤p

private theorem unbounded (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) :
    GraphSeedSamples.fits A (wire E S) (req E) ↔ ∃ p, fitsAt A E S p := by
  constructor
  · rintro ⟨C,hm,hr,ho,hw⟩
    exact ⟨C.size,C,hm,hr,ho,le_rfl,hw⟩
  · rintro ⟨_,C,hm,hr,ho,_,hw⟩
    exact ⟨C,hm,hr,ho,hw⟩

private theorem asNeg (i : Fin n) : asWord (neg i) = GraphSeedSamples.inv i := by
  funext u
  simp [asWord,neg,GraphSeedSamples.inv]
private theorem asEq (e : Edge n) : asWord (eqBit e) = GraphSeedSamples.same e := by
  funext u
  by_cases a : e.1∈u <;> by_cases b : e.2∈u <;> simp [asWord,eqBit,GraphSeedSamples.same,a,b]
private theorem asXor (e : Edge n) : asWord (xorBit e) = GraphSeedSamples.cross e := by
  funext u
  by_cases a : e.1∈u <;> by_cases b : e.2∈u <;> simp [asWord,xorBit,GraphSeedSamples.cross,GraphSeedSamples.same,a,b]

private theorem wordBank (E : Finset (Edge n)) (S : W n) :
    GraphSeedSamples.bank E S = (raw E ∪ S.image neg).image asWord := by
  classical
  simp [GraphSeedSamples.bank,raw,Finset.image_union,Finset.image_image,Function.comp_def,
    asNeg,asEq,asXor]
  rfl

private theorem shape (E : Finset (Edge n)) (sorted : ∀ e∈E, e.1<e.2) :
    (target E).card = n+3*E.card := by
  classical
  have upper (X Y : Finset (F n)) := Finset.card_union_le X Y
  have a := upper (Finset.univ.image neg) (E.image zz)
  have b := upper (Finset.univ.image neg ∪ E.image zz) (E.image oz)
  have d := upper (Finset.univ.image neg ∪ E.image zz ∪ E.image oz) (E.image zo)
  have h1 := Finset.card_image_le (s:=E) (f:=zz)
  have h2 := Finset.card_image_le (s:=E) (f:=oz)
  have h3 := Finset.card_image_le (s:=E) (f:=zo)
  have hi := Finset.card_image_le (s:=(Finset.univ : Finset (Fin n))) (f:=neg)
  simp only [Finset.card_univ,Fintype.card_fin] at hi
  have lo := Finset.card_le_card (show target E \ raw E ⊆ target E from Finset.sdiff_subset)
  have eq := countTargets E sorted ∅
  simp only [Finset.image_empty,Finset.union_empty,Finset.card_empty,Nat.sub_zero] at eq
  unfold target at lo eq ⊢
  omega

private def enum (A : Finset (W n)) : Fin A.card ≃ A :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card A = A.card)).symm
private abbrev words (A : Finset (W n)) (k : Fin A.card) := (enum A k).val
private abbrev xrow (A : Finset (W n)) (k : Fin A.card) (i : Fin n) := decide (i∈words A k)
private abbrev readWord (A : Finset (W n)) (f : W n → Bool) (k : Fin A.card) := f (words A k)
private abbrev lines (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) :=
  (wire E S).map (readWord A)

private theorem inputs (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) :
    (lines A E S).toFinset = GraphPriceCalibration.bank (xrow A) E S := by
  classical
  ext v
  simp only [lines,wire,List.mem_toFinset,List.mem_map,Finset.mem_toList,wordBank,
    Finset.mem_image,Finset.mem_union,GraphPriceCalibration.bank]
  constructor
  · rintro ⟨h,⟨f,hf,rfl⟩,rfl⟩
    rcases hf with hr|⟨i,hi,rfl⟩
    · exact Or.inl ⟨f,hr,rfl⟩
    · exact Or.inr ⟨i,hi,rfl⟩
  · rintro (⟨f,hr,rfl⟩|⟨i,hi,rfl⟩)
    · exact ⟨asWord f,⟨f,Or.inl hr,rfl⟩,rfl⟩
    · exact ⟨asWord (neg i),⟨_,Or.inr ⟨i,hi,rfl⟩,rfl⟩,rfl⟩

private theorem fitEq (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) (p : Nat) :
    fitsAt A E S p ↔ sampleFits (lines A E S) (T (xrow A) E) p := by
  classical
  simp only [fitsAt,sampleFits,lines,List.length_map,sampleRow,List.map_map,Function.comp_def]
  constructor
  · rintro ⟨C,hm,hr,ho,hs,h⟩
    refine ⟨C,hm,hr,ho,hs,?_⟩
    rintro g hg
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨j,hj,v⟩ := h _ (Finset.mem_image_of_mem asWord hf)
    exact ⟨j,hj,fun k => v _ (enum A k).property⟩
  · rintro ⟨C,hm,hr,ho,hs,h⟩
    refine ⟨C,hm,hr,ho,hs,?_⟩
    rintro g hg
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨j,hj,v⟩ := h _ (Finset.mem_image_of_mem (proj (xrow A)) hf)
    refine ⟨j,hj,?_⟩
    intro u hu
    obtain ⟨k,hk⟩ := (enum A).surjective ⟨u,hu⟩
    have val := v k
    change (C.wires ((wire E S).map (fun g => g (enum A k).val))).getD j false =
      asWord f (enum A k).val at val
    simpa only [hk] using val

private theorem pureOfTested (A : Finset (W n)) (color : Fin n → Fin c)
    (h : GraphSeedSamples.tested A color) : pure (xrow A) color := by
  intro j
  obtain ⟨u,hu,dis,high⟩ := h j
  obtain ⟨a,ha⟩ := (enum A).surjective ⟨u,hu⟩
  obtain ⟨b,hb⟩ := (enum A).surjective ⟨u∪GraphSeedSamples.block color j,high⟩
  refine ⟨a,b,?_,?_⟩
  · intro i hi
    have mem : i∈GraphSeedSamples.block color j := by simp [GraphSeedSamples.block,hi]
    have missing : i∉u := fun hz => Finset.disjoint_left.mp dis hz mem
    simp [xrow,words,ha,hb,mem,missing]
  · intro i hi
    simp [xrow,words,ha,hb,GraphSeedSamples.block,hi]

def separates (A : Finset (W n)) (E : Finset (Edge n)) :=
  (∀ f∈target E, ∀ g∈target E, f≠g → ∃ u∈A, asWord f u≠asWord g u) ∧
  ∀ f∈target E, ∀ g∈raw E, ∃ u∈A, asWord f u≠asWord g u

private theorem rankTest (A : Finset (W n)) (E : Finset (Edge n)) :
    ((T (xrow A) E) \ R (xrow A) E).card = (target E).card ↔ separates A E := by
  classical
  let p := proj (xrow A)
  have agree (f g : F n) : p f = p g ↔ ∀ u∈A, asWord f u=asWord g u := by
    constructor
    · intro h u hu
      obtain ⟨k,hk⟩ := (enum A).surjective ⟨u,hu⟩
      have val := congrFun h k
      change asWord f (enum A k).val = asWord g (enum A k).val at val
      simpa only [hk] using val
    · intro h
      exact funext (fun k => h _ (enum A k).property)
  have alg : ((target E).image p \ (raw E).image p).card = (target E).card ↔
      Set.InjOn p (target E) ∧ Disjoint ((target E).image p) ((raw E).image p) := by
    constructor
    · intro h
      have small : (target E).image p \ (raw E).image p ⊆ (target E).image p := Finset.sdiff_subset
      have le := Finset.card_le_card small
      have upper := Finset.card_image_le (s:=target E) (f:=p)
      exact ⟨Finset.card_image_iff.mp (by omega), Finset.sdiff_eq_self_iff_disjoint.mp
        (Finset.eq_of_subset_of_card_le small (by omega))⟩
    · rintro ⟨inj,dis⟩
      rw [Finset.sdiff_eq_self_of_disjoint dis,Finset.card_image_of_injOn inj]
  change ((target E).image p \ (raw E).image p).card = (target E).card ↔ _
  rw [alg]
  constructor
  · rintro ⟨inj, dis⟩
    constructor
    · intro f hf g hg ne
      by_contra! h
      exact ne (inj hf hg ((agree _ _).mpr h))
    · intro f hf g hg
      by_contra! h
      exact Finset.disjoint_left.mp dis (Finset.mem_image_of_mem p hf)
        ((agree _ _).mpr h ▸ Finset.mem_image_of_mem p hg)
  · rintro ⟨diff,rawDiff⟩
    constructor
    · intro f hf g hg eq
      by_contra ne
      obtain ⟨u,hu,h⟩ := diff f hf g hg ne
      exact h ((agree _ _).mp eq u hu)
    · apply Finset.disjoint_left.mpr
      intro v ht hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨g,hg,eq⟩ := Finset.mem_image.mp hr
      obtain ⟨u,hu,h⟩ := rawDiff f hf g hg
      exact h ((agree _ _).mp eq.symm u hu)

private theorem localTest (A : Finset (W n)) (E : Finset (Edge n)) (color : Fin n → Fin c)
    (onto : Function.Surjective color) (sorted : ∀ e∈E, e.1<e.2) (part : classes E color) :
    keeps A E color ↔ GraphSeedSamples.tested A color ∧ separates A E := by
  classical
  have testedOf (h : keeps A E color) : GraphSeedSamples.tested A color := by
    have reqInv (i : Fin n) : GraphSeedSamples.inv i ∈ req E := by
      rw [←asNeg]; exact Finset.mem_image_of_mem _ (by simp [target])
    apply ((GraphSeedSamples.criterion n c E color onto part (req E) reqInv).1 A).mp
    intro S
    change GraphSeedSamples.fits A (wire E S) (req E) ↔ GraphSeedSamples.cover color S
    rw [unbounded]
    constructor
    · rintro ⟨p,hp⟩
      exact ((h S p).mp hp).1
    · intro cov
      exact ⟨_,(h S _).mpr ⟨cov,le_rfl⟩⟩
  let rep (j : Fin c) := (onto j).choose
  have right (j : Fin c) : color (rep j)=j := (onto j).choose_spec
  let K := Finset.univ.image rep
  have transv (j : Fin c) : ∃! i, i∈K ∧ color i=j := by
    refine ⟨rep j,⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),right j⟩,?_⟩
    rintro v ⟨hv,hj⟩
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hv
    rw [right] at hj
    rw [hj]
  have cov : serves color K := fun j => ⟨_,(transv j).exists.choose_spec⟩
  have kc : K.card≤n := (Finset.card_le_univ K).trans (by simp)
  suffices work : ∀ t : GraphSeedSamples.tested A color, keeps A E color ↔ separates A E by
    exact ⟨fun h => ⟨testedOf h,(work (testedOf h)).mp h⟩,fun ⟨t,h⟩ => (work t).mpr h⟩
  intro test
  have cal := GraphPriceCalibration.criterion n A.card c E color (xrow A) sorted part
    (pureOfTested A color test) K transv (lines A E) (inputs A E)
  have pk (p : Nat) : sampleFits (lines A E K) (T (xrow A) E) p ↔
      price (xrow A) E K ≤ p := by
    exact (cal.1 K p).trans (and_iff_right cov)
  have rank := cal.2.1 ∅
  change price (xrow A) E ∅ + (N (xrow A) ∅).card = price (xrow A) E K + K.card at rank
  simp only [price,GraphPriceCalibration.bank,N,Finset.image_empty,Finset.union_empty,
    Finset.card_empty,Nat.add_zero] at rank
  rw [←rankTest,shape E sorted]
  constructor
  · intro h
    have small := (pk _).mpr le_rfl
    have lb := ((h K _).mp ((fitEq _ _ _ _).mpr small)).2
    have ub := (pk _).mp ((fitEq _ _ _ _).mp ((h K _).mpr ⟨cov,le_rfl⟩))
    change _ ≤ price (xrow A) E K at lb
    change price (xrow A) E K ≤ _ at ub
    change _ = price (xrow A) E K + K.card at rank
    omega
  · intro card
    have cost : price (xrow A) E K=n+3*E.card-K.card := by
      change _ = price (xrow A) E K + K.card at rank
      omega
    have all := cal.2.2.mp (fun p => (pk p).trans (by rw [cost]))
    intro S p
    exact (fitEq _ _ _ _).trans (all S p)

abbrev lows (A : Finset (W n)) (B : W n) :=
  A.filter (fun u => Disjoint u B ∧ u∪B∈A)

private theorem pairLoss (A : Finset (W n)) (B : W n) (w : W n → Nat) (d : Nat) :
    (∀ Z ⊆ A, Z.sum w ≤ d → ∃ u∈A\Z, Disjoint u B ∧ u∪B∈A\Z) ↔
    d < (lows A B).sum (fun u => min (w u) (w (u∪B))) := by
  classical
  let L := lows A B
  let pick (sel : W n → Bool) (u : W n) := if sel u then u else u∪B
  have info (u) (hu : u∈L) := Finset.mem_filter.mp hu
  have side (sel) (u) (hu : u∈L) : pick sel u ∈ A := by
    dsimp [pick]; split
    · exact (info u hu).1
    · exact (info u hu).2.2
  have recovers (sel) (u) (hu : u∈L) : pick sel u \ B = u := by
    dsimp [pick]; split
    · exact Finset.sdiff_eq_self_of_disjoint (info u hu).2.1
    · exact Finset.union_sdiff_cancel_right (info u hu).2.1
  have inj (sel) : Set.InjOn (pick sel) L := by
    intro u hu v hv eq
    exact (recovers sel u hu).symm.trans ((congrArg (fun z => z \ B) eq).trans (recovers sel v hv))
  constructor
  · intro robust
    by_contra! cheap
    let sel (u : W n) := decide (w u ≤ w (u∪B))
    let Z := L.image (pick sel)
    have sub : Z ⊆ A := by
      rintro _ hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz; exact side sel u hu
    have bill : Z.sum w = L.sum (fun u => min (w u) (w (u∪B))) := by
      rw [Finset.sum_image (inj sel)]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : w u ≤ w (u∪B)
      · simp [pick,sel,h,min_eq_left h]
      · simp [pick,sel,h,min_eq_right (le_of_not_ge h)]
    obtain ⟨u,hu,dis,hv⟩ := robust Z sub (bill.trans_le cheap)
    have low : u∈L := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hu).1,dis,(Finset.mem_sdiff.mp hv).1⟩
    have killed := Finset.mem_image_of_mem (pick sel) low
    change pick sel u ∈ Z at killed
    unfold pick at killed
    split at killed
    · exact (Finset.mem_sdiff.mp hu).2 killed
    · exact (Finset.mem_sdiff.mp hv).2 killed
  · intro large Z _ budget
    by_contra fail
    let sel (u : W n) := decide (u∈Z)
    have killed : L.image (pick sel) ⊆ Z := by
      rintro v hv
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
      by_cases h : u∈Z
      · simpa [pick,sel,h] using h
      · have h' : u∪B∈Z := by
          by_contra high
          exact fail ⟨u,Finset.mem_sdiff.mpr ⟨(info u hu).1,h⟩,(info u hu).2.1,
            Finset.mem_sdiff.mpr ⟨(info u hu).2.2,high⟩⟩
        simpa [pick,sel,h] using h'
    have count : L.sum (fun u => min (w u) (w (u∪B))) ≤ (L.image (pick sel)).sum w := by
      rw [Finset.sum_image (inj sel)]
      apply Finset.sum_le_sum
      intro u _
      dsimp [pick]; split
      · exact min_le_left _ _
      · exact min_le_right _ _
    exact (not_le_of_gt large) (count.trans ((Finset.sum_le_sum_of_subset killed).trans budget))

private theorem traceLoss {α : Type} [DecidableEq α] (A : Finset α) (w : α → Nat)
    (P : α → Prop) [DecidablePred P] (d : Nat) :
    (∀ Z ⊆ A, Z.sum w ≤ d → ∃ u∈A\Z, P u) ↔ d < (A.filter P).sum w := by
  constructor
  · intro robust
    by_contra! h
    obtain ⟨u,hu,yes⟩ := robust (A.filter P) (Finset.filter_subset _ _) h
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hu).1,yes⟩)
  · intro gap Z _ budget
    by_contra fail
    have sub : A.filter P ⊆ Z := by
      intro u hu
      by_contra absent
      exact fail ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hu).1,absent⟩,(Finset.mem_filter.mp hu).2⟩
    exact (not_le_of_gt gap) ((Finset.sum_le_sum_of_subset sub).trans budget)

def margin (A : Finset (W n)) (w : W n → Nat) (f g : F n) :=
  (A.filter (fun u => asWord f u≠asWord g u)).sum w

private theorem byType (A : Finset (W n)) (E : Finset (Edge n)) (color : Fin n → Fin c)
    (w : W n → Nat) (d : Nat) (onto : Function.Surjective color)
    (sorted : ∀ e∈E, e.1<e.2) (part : classes E color) :
    (∀ Z ⊆ A, Z.sum w ≤ d → keeps (A\Z) E color) ↔
    (∀ j, d < (lows A (GraphSeedSamples.block color j)).sum
      (fun u => min (w u) (w (u∪GraphSeedSamples.block color j)))) ∧
    (∀ f∈target E, ∀ g∈target E, f≠g → d < margin A w f g) ∧
    ∀ f∈target E, ∀ g∈raw E, d < margin A w f g := by
  constructor
  · intro robust
    have ok := fun Z sub budget => (localTest (A\Z) E color onto sorted part).mp (robust Z sub budget)
    exact ⟨fun j => (pairLoss _ _ _ _).mp (fun Z sub h => (ok Z sub h).1 j),
      fun f hf g hg ne => (traceLoss _ _ _ _).mp (fun Z sub h => (ok Z sub h).2.1 f hf g hg ne),
      fun f hf g hg => (traceLoss _ _ _ _).mp (fun Z sub h => (ok Z sub h).2.2 f hf g hg)⟩
  · rintro ⟨pairs,diff,cross⟩ Z sub budget
    exact (localTest _ _ _ onto sorted part).mpr
      ⟨fun j => (pairLoss _ _ _ _).mpr (pairs j) Z sub budget,
        fun f hf g hg ne => (traceLoss _ _ _ _).mpr (diff f hf g hg ne) Z sub budget,
        fun f hf g hg => (traceLoss _ _ _ _).mpr (cross f hf g hg) Z sub budget⟩

private theorem copyLoss {α : Type} [DecidableEq α] (A : Finset α) (w : α → Nat)
    (pos : ∀ u∈A, 0<w u) (d : Nat) (holds : Finset α → Prop) :
    (∀ lost : α → Nat, A.sum lost ≤ d → holds (A.filter (fun u => lost u < w u))) ↔
    ∀ Z ⊆ A, Z.sum w ≤ d → holds (A\Z) := by
  classical
  constructor
  · intro ok Z sub budget
    let lost (u : α) := if u∈Z then w u else 0
    have cost : A.sum lost = Z.sum w := by
      change (∑ u∈A, if u∈Z then w u else 0) = _
      rw [←Finset.sum_filter]
      congr 1
      ext u
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
    have remaining : A.filter (fun u => lost u < w u) = A\Z := by
      ext u
      by_cases hu : u∈A <;> by_cases hz : u∈Z <;> simp_all [lost]
    exact remaining ▸ ok lost (cost.trans_le budget)
  · intro ok lost budget
    let Z := A.filter (fun u => w u ≤ lost u)
    have bill : Z.sum w ≤ A.sum lost := (Finset.sum_le_sum (s:=Z)
      (fun u hu => (Finset.mem_filter.mp hu).2)).trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    have remaining : A\Z=A.filter (fun u => lost u<w u) := by
      ext u
      by_cases hu : u∈A <;> simp [Z,hu]
    exact remaining ▸ ok Z (Finset.filter_subset _ _) (bill.trans budget)

theorem criterion :
∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  Function.Surjective color → (∀ e∈E, e.1<e.2) →
  (∀ V : Finset (Fin n), (∀ e∈E, e.1∈V ↔ e.2∈V) ↔
    ∀ i k, color i=color k → (i∈V ↔ k∈V)) →
  let W := Finset (Fin n)
  let F := (Fin n → Bool) → Bool
  let val := fun (f : F) (u : W) => f (fun i => decide (i∈u))
  let raw : Finset F := {fun _ => false,fun _ => true} ∪ Finset.univ.image (fun i x => x i) ∪
    E.image (fun e x => x e.1 == x e.2) ∪ E.image (fun e x => xor (x e.1) (x e.2))
  let target : Finset F := Finset.univ.image (fun i x => !(x i)) ∪
    E.image (fun e x => !(x e.1) && !(x e.2)) ∪ E.image (fun e x => x e.1 && !(x e.2)) ∪
    E.image (fun e x => !(x e.1) && x e.2)
  let bank := fun S : W => (({fun _ : W => false,fun _ : W => true} : Finset (W → Bool)) ∪
    Finset.univ.image (fun i u => decide (i∈u)) ∪ E.image (fun e u => decide (e.1∈u ↔ e.2∈u)) ∪
    E.image (fun e u => !(decide (e.1∈u ↔ e.2∈u))) ∪ S.image (fun i u => decide (i∉u))).toList
  let block := fun j : Fin c => Finset.univ.filter (fun i => color i=j)
  ∀ (A : Finset W) (w : W → Nat) (d : Nat), (∀ u∈A, 0<w u) →
  let gap := fun f g : F => (A.filter (fun u => val f u ≠ val g u)).sum w
  (∀ lost : W → Nat, A.sum lost ≤ d → ∀ (S : W) (p : Nat),
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (bank S).length C ∧
      C.output < (bank S).length+C.size ∧ C.size ≤ p ∧ ∀ f∈target.image val,
        ∃ j<(bank S).length+C.size, ∀ u∈A.filter (fun u => lost u < w u),
          (C.wires ((bank S).map (fun g => g u))).getD j false=f u) ↔
    (∀ j, ∃ i∈S, color i=j) ∧ n+3*E.card-S.card ≤ p) ↔
  (∀ j, (d < (A.filter (fun u => Disjoint u (block j) ∧ u∪block j∈A)).sum
    (fun u => min (w u) (w (u∪block j))))) ∧
  (∀ f∈target, ∀ g∈target, f≠g → d < gap f g) ∧
  ∀ f∈target, ∀ g∈raw, d < gap f g
 := by
  intro n c E color onto sorted part
  dsimp only
  intro A w d pos
  exact (copyLoss A w pos d (fun left => keeps left E color)).trans
    (byType A E color w d onto sorted part)

end
end PEqualNP.GraphSampleDistance
