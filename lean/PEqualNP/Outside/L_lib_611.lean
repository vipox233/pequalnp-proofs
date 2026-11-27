import Mathlib

namespace PEqualNP.Outside.L_lib_611_aux

abbrev K := ZMod 2
def bit (b : Bool) : K := if b then 1 else 0
theorem parity (k : ℕ) : bit (k % 2 == 1) = (k : K) := by
  rw [← ZMod.natCast_mod k 2]
  have h := k.mod_lt (by decide : 0<2)
  rcases (by omega : k%2=0 ∨ k%2=1) with e|e <;> rw [e] <;> rfl

noncomputable def mon {V : Type} (s : Finset V) (w : V → Bool) : K := by
  classical
  exact if ∀ v ∈ s, w v=true then 1 else 0

noncomputable def poly {V : Type} (T : Finset (Finset V)) (w : V → Bool) : K :=
  ∑ s ∈ T, mon s w
def vary {V : Type} [DecidableEq V] (U A : Finset V) (w : V → Bool) (v : V) :=
  if v ∈ U then decide (v ∈ A) else w v

theorem monSum {V : Type} [DecidableEq V] (U M : Finset V) (w : V → Bool)
    (maximal : U ⊆ M → M=U) :
    (∑ A ∈ U.powerset, mon M (vary U A w)) = if M=U then 1 else 0 := by
  classical
  have spec (A : Finset V) :
      (∀ v ∈ M, vary U A w v=true) ↔ M ∩ U ⊆ A ∧ ∀ v ∈ M, v ∉ U → w v=true := by
    constructor
    · intro h
      exact ⟨fun v hv => by
        obtain ⟨hm,hu⟩ := Finset.mem_inter.mp hv
        simpa [vary,hu] using h v hm,
        fun v hm hu => by simpa [vary,hu] using h v hm⟩
    · rintro ⟨sub,ok⟩ v hm
      by_cases hu : v ∈ U
      · simp [vary,hu,sub (Finset.mem_inter.mpr ⟨hm,hu⟩)]
      · simpa [vary,hu] using ok v hm hu
  by_cases outside : ∀ v ∈ M, v ∉ U → w v=true
  · have summand (A : Finset V) : mon M (vary U A w) = if M ∩ U ⊆ A then 1 else 0 := by
      by_cases sub : M ∩ U ⊆ A
      · exact (ite_eq_left ((spec A).mpr ⟨sub,outside⟩)).trans (ite_eq_left sub).symm
      · exact (ite_eq_right (fun h => sub ((spec A).mp h).1)).trans (ite_eq_right sub).symm
    simp_rw [summand]
    rw [Finset.sum_boole,← Finset.Icc_eq_filter_powerset,Finset.card_Icc_finset Finset.inter_subset_right]
    by_cases eq : M=U
    · subst M; simp
    · have proper : M ∩ U ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,by
        intro equal; apply eq; apply maximal; rw [← equal]; exact Finset.inter_subset_left⟩
      have less := Finset.card_lt_card proper
      obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt less)
      rw [ite_eq_right eq,he,pow_succ,Nat.cast_mul]
      rw [show ((2 : ℕ) : K)=0 by decide,mul_zero]
  · have ne : M ≠ U := by
      rintro rfl; exact outside (fun v hv hn => (hn hv).elim)
    simp only [mon,spec,outside,and_false,ite_false,Finset.sum_const_zero,ite_eq_right ne]

theorem cubeSum {V : Type} [DecidableEq V] (U : Finset V) (T : Finset (Finset V))
    (mem : U ∈ T) (maximal : ∀ s ∈ T, U ⊆ s → s=U) (w : V → Bool) :
    (∑ A ∈ U.powerset, poly T (vary U A w)) = 1 := by
  classical
  unfold poly
  rw [Finset.sum_comm]
  calc
    _ = ∑ s ∈ T, (if s=U then 1 else 0 : K) :=
      Finset.sum_congr rfl (fun s hs => monSum _ _ _ (maximal s hs))
    _ = 1 := by simp [mem]

theorem findSupport {V : Type} [DecidableEq V] (U : Finset V) (T : Finset (Finset V))
    (mem : U ∈ T) (maximal : ∀ s ∈ T, U ⊆ s → s=U) (w : V → Bool) :
    ∃ A ∈ U.powerset, poly T (vary U A w)=1 := by
  classical
  by_contra! no
  have zero (v : K) : v ≠ 1 → v=0 := by revert v; decide
  have h := cubeSum U T mem maximal w
  rw [Finset.sum_eq_zero (fun a ha => zero _ (no a ha))] at h
  exact zero_ne_one h

theorem repairBound {V : Type} [DecidableEq V] (U : Finset V)
    (bad good : Finset (V → Bool))
    (repair : ∀ w ∈ bad, ∃ y ∈ good, ∀ v ∉ U, y v=w v) :
    bad.card ≤ 2^U.card * good.card := by
  classical
  choose fix inside agrees using fun x : (↥bad) => repair x.val x.property
  let keep := fun (x : (↥bad)) => U.filter (fun v => x.val v = true)
  let enc : (↥bad) → (↥U.powerset) × (↥good) := fun x =>
    (⟨keep x,Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩,⟨fix x,inside x⟩)
  have inj : Function.Injective enc := by
    intro x y eq
    have own : keep x=keep y := congrArg (fun h : (↥U.powerset) × (↥good) => h.1.val) eq
    have rep : fix x=fix y := congrArg (fun h : (↥U.powerset) × (↥good) => h.2.val) eq
    apply Subtype.ext; funext v; by_cases hv : v ∈ U
    · have same : v ∈ keep x ↔ v ∈ keep y := by rw [own]
      have hbits : (x.val v=true ↔ y.val v=true) := by
        simpa only [keep,Finset.mem_filter,hv,true_and] using same
      exact Bool.eq_iff_iff.mpr hbits
    · exact (agrees x v hv).symm.trans ((congrFun rep v).trans (agrees y v hv))
  simpa using Fintype.card_le_of_injective enc inj

abbrev W (V : Type) := V → Bool
def D {V : Type} (d : ℕ) (f : W V → K) := ∃ t : Finset (Finset V),
  (∀ a ∈ t, a.card ≤ d) ∧ ∀ x, f x = ∑ a ∈ t, mon a x

theorem twoZero (z : K) : z+z=0 := by revert z; decide

theorem normalize {V I : Type} (s : Finset I) (m : I → Finset V) (d : ℕ)
    (bound : ∀ i ∈ s, (m i).card ≤ d) : D d (fun x => ∑ i ∈ s, mon (m i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨t,ht,eq⟩ := ih (fun j hj => bound j (Finset.mem_insert_of_mem hj))
    by_cases h : m i ∈ t
    · refine ⟨t.erase (m i),fun a ha => ht a (Finset.mem_of_mem_erase ha),?_⟩
      intro x
      dsimp only at eq ⊢
      rw [Finset.sum_insert hi,eq x,← Finset.add_sum_erase t (fun a => mon a x) h,
        ← add_assoc,twoZero,zero_add]
    · refine ⟨insert (m i) t,?_,?_⟩
      · intro a ha; rcases Finset.mem_insert.mp ha with h'|h'
        · subst a; exact bound i (Finset.mem_insert_self ..)
        · exact ht a h'
      · intro x; dsimp only at eq ⊢; rw [Finset.sum_insert hi,Finset.sum_insert h,eq x]

theorem dMono {V : Type} {d e : ℕ} {f : W V → K} (h : D d f) (le : d ≤ e) : D e f := by
  obtain ⟨t,ht,eq⟩ := h
  exact ⟨t,fun a ha => (ht a ha).trans le,eq⟩

theorem dZero {V : Type} (d : ℕ) : D d (fun _ : W V => 0) :=
  ⟨∅, by simp,by simp⟩

theorem dOne {V : Type} : D 0 (fun _ : W V => 1) := by
  classical
  exact ⟨{∅},by simp,by intro x; rw [Finset.sum_singleton]; simp [mon]⟩

theorem dVar {V : Type} (v : V) : D 1 (fun x : W V => if x v = true then 1 else 0) := by
  classical
  exact ⟨{{v}},by simp,by intro x; rw [Finset.sum_singleton]; simp [mon]⟩

theorem dAdd {V : Type} {d : ℕ} {f g : W V → K} (hf : D d f) (hg : D d g) :
    D d (fun x => f x + g x) := by
  classical
  obtain ⟨a,ba,ea⟩ := hf
  obtain ⟨b,bb,eb⟩ := hg
  let mon : Finset V ⊕ Finset V → Finset V := Sum.elim id id
  have h := normalize (a.disjSum b) mon d (by
    intro i hi; cases i with
    | inl i => exact ba i (by simpa using hi)
    | inr i => exact bb i (by simpa using hi))
  simpa only [Finset.sum_disjSum,mon,Sum.elim_inl,Sum.elim_inr,id_eq,← ea,← eb] using h

theorem evUnion {V : Type} [DecidableEq V] (a b : Finset V) (x : W V) :
    mon (a ∪ b) x = mon a x * mon b x := by
  classical
  simp only [mon,Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem dMul {V : Type} {d e : ℕ} {f g : W V → K} (hf : D d f) (hg : D e g) :
    D (d+e) (fun x => f x * g x) := by
  classical
  obtain ⟨a,ba,ea⟩ := hf
  obtain ⟨b,bb,eb⟩ := hg
  have h := normalize (a ×ˢ b) (fun p => p.1 ∪ p.2) (d+e) (by
    intro i hi
    exact (Finset.card_union_le ..).trans (Nat.add_le_add
      (ba i.1 (Finset.mem_product.mp hi).1) (bb i.2 (Finset.mem_product.mp hi).2)))
  simpa only [Finset.sum_product,evUnion,← Finset.mul_sum,← Finset.sum_mul,← ea,← eb] using h

theorem dProdCost {V I : Type} (s : Finset I) (cost : I → ℕ) (f : I → W V → K)
    (h : ∀ i ∈ s, D (cost i) (f i)) :
    D (∑ i ∈ s, cost i) (fun w => ∏ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dOne (V:=V))
  | @insert i s hi ih =>
    simpa [hi] using dMul (h _ (Finset.mem_insert_self ..)) (ih (fun a ha => h a (Finset.mem_insert_of_mem ha)))

theorem dMatch {V : Type} {q : W V → Bool} {d : ℕ} (hq : D d (fun x => bit (q x))) (b : Bool) :
    D d (fun x => if q x=b then 1 else 0) := by
  cases b with
  | true => exact hq
  | false =>
    have h := dAdd (dMono (dOne (V:=V)) (Nat.zero_le d)) hq
    convert h using 1
    funext x; cases q x <;> decide

def appendBit (h s : ℕ) (b : Bool) := h+(b.toNat <<< s)
theorem appendBound {h s : ℕ} (b : Bool) (small : h<2^s) : appendBit h s b < 2^(s+1) := by
  cases b <;> simp [appendBit,Nat.shiftLeft_eq,pow_succ] <;> omega
theorem appendEq {h h' s : ℕ} {b b' : Bool} (lh : h<2^s) (rh : h'<2^s) :
    appendBit h s b = appendBit h' s b' ↔ h=h' ∧ b=b' := by
  constructor
  · intro eq
    have mod := congrArg (· % (2^s)) eq
    simp only [appendBit,Nat.shiftLeft_eq,Nat.add_comm h,Nat.add_comm h',Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt lh,Nat.mod_eq_of_lt rh] at mod
    refine ⟨mod,?_⟩
    cases b <;> cases b' <;> simp_all [appendBit,Nat.shiftLeft_eq]
  · rintro ⟨rfl,rfl⟩;rfl

def code {V : Type} (ask : ℕ → ℕ → W V → Bool) (s : ℕ) (x : W V) :=
  (List.range s).foldl (fun h i => appendBit h i (ask i h x)) 0
theorem codeSucc {V : Type} (ask : ℕ → ℕ → W V → Bool) (s : ℕ) (x : W V) :
    code ask (s+1) x = appendBit (code ask s x) s (ask s (code ask s x) x) := by
  simp [code,List.range_succ,List.foldl_append]
theorem codeSmall {V : Type} (ask : ℕ → ℕ → W V → Bool) (s : ℕ) (x : W V) :
    code ask s x < 2^s := by
  induction s with
  | zero => simp [code]
  | succ s ih => rw [codeSucc]; exact appendBound _ ih
theorem codeMatch {V : Type} (ask : ℕ → ℕ → W V → Bool) (s : ℕ) (x anchor : W V) :
    code ask s x=code ask s anchor ↔
      ∀ i, i<s → ask i (code ask i anchor) x=ask i (code ask i anchor) anchor := by
  induction s with
  | zero => simp [code]
  | succ s ih =>
    rw [codeSucc,codeSucc,appendEq (codeSmall ..) (codeSmall ..)]
    constructor
    · rintro ⟨prev,now⟩ i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with small|rfl
      · exact ih.mp prev i small
      · rwa [prev] at now
    · intro h
      have prev := ih.mpr (fun i hi => h i (by omega))
      exact ⟨prev,by rw [prev]; exact h s (by omega)⟩

theorem prodTest {I : Type} (s : Finset I) (P : I → Prop) [DecidablePred P] :
    (∏ i ∈ s, if P i then (1:K) else 0) = if ∀ i ∈ s, P i then 1 else 0 := by
  classical
  by_cases ok : ∀ i ∈ s, P i
  · rw [ite_eq_left ok]; apply Finset.prod_eq_one; intro i hi; simp [ok i hi]
  · rw [ite_eq_right ok]; push Not at ok; obtain ⟨i,hi,no⟩ := ok
    exact Finset.prod_eq_zero hi (ite_eq_right no)

end PEqualNP.Outside.L_lib_611_aux


open PEqualNP.Outside.L_lib_611_aux in
theorem PEqualNP.Outside.L_lib_611 : ∀ (m r d : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧ ∀ word,
      f word = (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)
  let run := fun (ask : Nat → Nat → W → Bool) (len : Nat) (x : W) =>
    (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0
  ∀ (ask : Nat → Nat → W → Bool) (anchor : W) (j : Nat), j ≤ d →
    let pathCode := run ask j anchor
    let cell := (Finset.univ : Finset W).filter (fun sample => run ask j sample = pathCode)
    let leaves := cell.image (run ask d)
    ∀ B : Fin j → Nat, (∀ t, deg (B t) (ask t.val (run ask t.val anchor))) →
      ∃ U : Finset V, U.card ≤ ∑ t : Fin j, B t ∧
        ∀ (L : Nat) (bad : Nat → Fin L → Fin m → Symbol),
          let gone := U.image Prod.fst
          let outside := (Finset.univ : Finset W).filter (fun w =>
            ∀ h ∈ leaves, ∀ a, ∃ i, i ∉ gone ∧ (fun v => w (i,v)) = bad h a i)
          let errors := cell.filter (fun input => ∀ a, ∃ i,
            (fun v => input (i,v)) = bad (run ask d input) a i)
          outside.card ≤ 2^U.card * errors.card := by
  classical
  intro m r d V W Symbol deg run ask anchor j hj pathCode cell leaves B hB
  let q := fun (i : Fin j) => ask i.val (code ask i.val anchor)
  have dq (i : Fin j) : D (B i) (fun x => bit (q i x)) := by
    obtain ⟨t,ht,ok⟩ := hB i
    refine ⟨t,ht,?_⟩
    intro x
    change bit (ask i.val (run ask i.val anchor) x) = _
    rw [ok,parity,Finset.natCast_card_filter]
    exact Finset.sum_congr rfl (fun a _ => by unfold mon; split_ifs <;> rfl)
  let indicator := fun x : W => ∏ i : Fin j, if q i x=q i anchor then (1:K) else 0
  have eqv (x : W) : (∀ i : Fin j, q i x=q i anchor) ↔ code ask j x = pathCode := by
    apply Iff.trans _ (codeMatch ask j x anchor).symm
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i.val i.isLt⟩
  have test (x : W) : indicator x = if code ask j x=pathCode then 1 else 0 := by
    simp only [indicator,prodTest,Finset.mem_univ,forall_const,eqv]
  obtain ⟨T,bound,val⟩ : D (∑ i, B i) indicator :=
    dProdCost Finset.univ B _ (fun i _ => dMatch (dq i) (q i anchor))
  have liveA : indicator anchor=1 := by rw [test]; exact ite_eq_left rfl
  have nonempty : T.Nonempty := by
    by_contra! h
    have hh := val anchor
    rw [h,Finset.sum_empty,liveA] at hh
    exact one_ne_zero hh
  obtain ⟨U,hu,max⟩ := T.exists_max_image Finset.card nonempty
  have maximal (s) (hs : s ∈ T) (sub : U ⊆ s) : s=U :=
    (Finset.eq_of_subset_of_card_le sub (max s hs)).symm
  refine ⟨U,bound U hu,?_⟩
  intro L bad gone outside errors
  apply repairBound U
  intro x hx
  obtain ⟨A,_,one⟩ := findSupport U T hu maximal x
  let y := vary U A x
  have on : code ask j y = pathCode := by
    have h : indicator y=1 := (val y).trans one
    rw [test] at h
    by_contra hno
    rw [ite_eq_right hno] at h
    exact zero_ne_one h
  have atCell : y ∈ cell := Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩
  have atLeaf : run ask d y ∈ leaves := Finset.mem_image.mpr ⟨y,atCell,rfl⟩
  have same (v : V) (hv : v ∉ U) : y v=x v := by simp [y,vary,hv]
  refine ⟨y,Finset.mem_filter.mpr ⟨atCell,?_⟩,same⟩
  intro a
  obtain ⟨i,away,word⟩ := (Finset.mem_filter.mp hx).2 _ atLeaf a
  refine ⟨i,?_⟩
  funext v
  have hv : (i,v) ∉ U := fun h => away (Finset.mem_image.mpr ⟨(i,v),h,rfl⟩)
  exact (same _ hv).trans (congrFun word v)
