import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1075

private abbrev I (n : ℕ) := Fin n
private abbrev E (n : ℕ) := I n × I n
private abbrev Perm (n : ℕ) := Equiv.Perm (I n)
private abbrev Vec (n : ℕ) := E n → ℚ
private def live {n : ℕ} (H : I n → I n → Bool) (π : Perm n) : Prop := ∀ j, H (π j) j=true
private def qv {n : ℕ} (π : Perm n) : Vec n := fun e => if π e.2=e.1 then 1 else 0
private def ZV {n : ℕ} (H : I n → I n → Bool) : Submodule ℚ (Vec n) :=
  Submodule.span ℚ {v | ∃ π : Perm n, live H π ∧ v=qv π}

private lemma qv_mem {n : ℕ} (H : I n → I n → Bool) (π : Perm n) (hπ : live H π) : qv π ∈ ZV H :=
  Submodule.subset_span ⟨π,hπ,rfl⟩

private lemma qv_nonneg {n : ℕ} (π : Perm n) (e : E n) : 0 ≤ qv π e := by
  simp only [qv]; split_ifs <;> norm_num

private lemma qv_row {n : ℕ} (π : Perm n) (i : I n) : ∑ j, qv π (i,j)=1 := by
  classical
  simp only [qv,Equiv.apply_eq_iff_eq_symm_apply]
  simp

private lemma qv_col {n : ℕ} (π : Perm n) (j : I n) : ∑ i, qv π (i,j)=1 := by
  classical
  simp [qv]

private def Balanced {n : ℕ} (r : I n) (f : Vec n) : Prop :=
  (∀ i, ∑ j, f (i,j)=∑ i, f (i,r)) ∧ (∀ j, ∑ i, f (i,j)=∑ i, f (i,r))

private lemma balanced_span {n : ℕ} (H : I n → I n → Bool) (r : I n)
    (f : Vec n) (hf : f∈ZV H) : Balanced r f := by
  classical
  apply Submodule.span_induction (p:=fun f _ => Balanced r f) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨π,hπ,rfl⟩
    exact ⟨fun i => (qv_row π i).trans (qv_col π r).symm,
      fun j => (qv_col π j).trans (qv_col π r).symm⟩
  · constructor <;> intro i <;> simp
  · intro a b ha hb hba hbb
    constructor
    · intro i; simpa only [Pi.add_apply,Finset.sum_add_distrib,hba.1 i,hbb.1 i]
    · intro j; simpa only [Pi.add_apply,Finset.sum_add_distrib,hba.2 j,hbb.2 j]
  · intro c a ha hba
    constructor
    · intro i; simpa only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hba.1 i]
    · intro j; simpa only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hba.2 j]

private lemma support_span {n : ℕ} (H : I n → I n → Bool) (f : Vec n) (hf : f∈ZV H)
    (e : E n) (he : H e.1 e.2=false) : f e=0 := by
  classical
  apply Submodule.span_induction (p:=fun f _ => f e=0) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨π,hπ,rfl⟩
    have hp : π e.2≠e.1 := by intro hp; have hh := hπ e.2; rw [hp,he] at hh; contradiction
    simp [qv,hp]
  · rfl
  · intro a b ha hb hza hzb; simp [hza,hzb]
  · intro c a ha hza; simp [hza]

private lemma pm_qv {n : ℕ} (σ : Perm n) (i j : I n) :
    σ.permMatrix ℚ i j=qv σ.symm (i,j) := by
  classical
  simp only [Equiv.toPEquiv_apply,PEquiv.toMatrix_apply,Option.mem_def,Option.some.injEq,qv]
  congr 1
  exact propext ((σ.eq_symm_apply).symm.trans eq_comm)

private lemma nonneg_span {n : ℕ} (H : I n → I n → Bool) (r : I n) (f : Vec n)
    (hb : Balanced r f) (hn : ∀ e, 0 ≤ f e) (hs : ∀ e, H e.1 e.2=false → f e=0) :
    f∈ZV H := by
  classical
  let s : ℚ := ∑ i, f (i,r)
  let M : Matrix (I n) (I n) ℚ := fun i j => f (i,j)
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => hn (i,r))
  obtain ⟨M',hM',hM⟩ := (exists_mem_doublyStochastic_eq_smul_iff hs0).mpr
    (show (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j=s) ∧ (∀ j, ∑ i, M i j=s) from
      ⟨fun i j => hn (i,j),hb.1,hb.2⟩)
  obtain ⟨w,hw,hw1,hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM'
  let c : Perm n → ℚ := fun σ => s*w σ
  have hc0 : ∀ σ, 0 ≤ c σ := fun σ => mul_nonneg hs0 (hw σ)
  have hcM : ∑ σ, c σ • σ.permMatrix ℚ=M := by
    calc
      _ = s • (∑ σ, w σ • σ.permMatrix ℚ) := by simp only [Finset.smul_sum,smul_smul,c]
      _ = s • M' := by rw [hwM]
      _ = M := hM.symm
  have heq : ∀ e : E n, ∑ σ, c σ*qv σ.symm e=f e := by
    rintro ⟨i,j⟩
    have hh := congrArg (fun N : Matrix (I n) (I n) ℚ => N i j) hcM
    simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,pm_qv,M] using hh
  have hcSupport : ∀ σ, c σ≠0 → live H σ.symm := by
    intro σ hσ j
    by_contra hH
    have hH0 : H (σ.symm j) j=false := Bool.eq_false_iff.mpr hH
    have hcell : f (σ.symm j,j)=0 := hs _ hH0
    have hsummand : c σ*qv σ.symm (σ.symm j,j) ≤
        ∑ τ, c τ*qv τ.symm (σ.symm j,j) :=
      Finset.single_le_sum (fun τ _ => mul_nonneg (hc0 τ) (qv_nonneg _ _)) (Finset.mem_univ σ)
    rw [heq,hcell] at hsummand
    simp only [qv,ite_true,mul_one] at hsummand
    exact hσ (le_antisymm hsummand (hc0 σ))
  have hfEq : f=∑ σ, c σ • qv σ.symm := by
    funext e
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using (heq e).symm
  rw [hfEq]
  apply Submodule.sum_mem
  intro σ _
  by_cases hc : c σ=0
  · simp [hc]
  · exact Submodule.smul_mem _ _ (qv_mem H _ (hcSupport σ hc))


private noncomputable def codeIdx {n : ℕ} (π : Perm n) : ℕ := (Fintype.equivFin (Perm n) π).val

private lemma codeIdx_inj {n : ℕ} : Function.Injective (codeIdx (n:=n)) := by
  intro π ρ h
  apply (Fintype.equivFin (Perm n)).injective
  exact Fin.ext h

private noncomputable def liveSet {n : ℕ} (H : I n → I n → Bool) : Finset (Perm n) := by
  classical
  exact Finset.univ.filter (live H)

private noncomputable def sigSet {n : ℕ} (H : I n → I n → Bool) (e : E n) : Finset (Perm n) := by
  classical
  exact (liveSet H).filter (fun π => π e.2=e.1)

private noncomputable def codeN {n : ℕ} (H : I n → I n → Bool) (e : E n) : ℕ :=
  ∑ π∈sigSet H e, 2^codeIdx π

private noncomputable def uVec {n : ℕ} (H : I n → I n → Bool) : Vec n := fun e => (codeN H e : ℚ)

private lemma image_code_sum {n : ℕ} (S : Finset (Perm n)) :
    ∑ k∈S.image codeIdx, 2^k=∑ π∈S, 2^codeIdx π := by
  classical
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact codeIdx_inj hab

private lemma codeN_inj_sig {n : ℕ} (H : I n → I n → Bool) (e f : E n)
    (h : codeN H e=codeN H f) : sigSet H e=sigSet H f := by
  classical
  have hi : (sigSet H e).image codeIdx=(sigSet H f).image codeIdx := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2:ℕ))
    simpa only [image_code_sum,codeN] using h
  exact Finset.image_injective codeIdx_inj hi

private lemma coord_eq_span {n : ℕ} (H : I n → I n → Bool) (e f : E n)
    (h : ∀ π : Perm n, live H π → qv π e=qv π f) (z : Vec n) (hz : z∈ZV H) : z e=z f := by
  apply Submodule.span_induction (p:=fun z _ => z e=z f) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨π,hπ,rfl⟩; exact h π hπ
  · rfl
  · intro a b ha hb hza hzb; simp [hza,hzb]
  · intro c a ha hza; simp [hza]

private lemma code_eq_coord {n : ℕ} (H : I n → I n → Bool) (e f : E n)
    (h : codeN H e=codeN H f) (z : Vec n) (hz : z∈ZV H) : z e=z f := by
  classical
  have hs := codeN_inj_sig H e f h
  apply coord_eq_span H e f ?_ z hz
  intro π hπ
  have hm : (π∈sigSet H e) ↔ (π∈sigSet H f) := by rw [hs]
  have he : (π e.2=e.1) ↔ (π f.2=f.1) := by simpa [sigSet,liveSet,hπ] using hm
  simp only [qv]
  exact if_congr he rfl rfl

private lemma code_positive {n : ℕ} (H : I n → I n → Bool) (π : Perm n) (hπ : live H π)
    (e : E n) (he : π e.2=e.1) : 0 < codeN H e := by
  classical
  have hm : π∈sigSet H e := by simp [sigSet,liveSet,hπ,he]
  have hh : 2^codeIdx π ≤ codeN H e := by
    unfold codeN
    exact Finset.single_le_sum (fun ρ _ => Nat.zero_le (2^codeIdx ρ)) hm
  exact lt_of_lt_of_le (pow_pos (by decide) _) hh

private lemma code_zero_coord {n : ℕ} (H : I n → I n → Bool) (e : E n)
    (h : codeN H e=0) (z : Vec n) (hz : z∈ZV H) : z e=0 := by
  classical
  apply Submodule.span_induction (p:=fun z _ => z e=0) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨π,hπ,rfl⟩
    have hp : π e.2≠e.1 := by intro he; have hh := code_positive H π hπ e he; omega
    simp [qv,hp]
  · rfl
  · intro a b ha hb hza hzb; simp [hza,hzb]
  · intro c a ha hza; simp [hza]

private lemma uVec_mem {n : ℕ} (H : I n → I n → Bool) : uVec H∈ZV H := by
  classical
  have he : uVec H=∑ π∈liveSet H, (2:ℚ)^codeIdx π • qv π := by
    funext e
    simp [uVec,codeN,sigSet,Finset.sum_filter,Finset.sum_apply,qv,
      Pi.smul_apply,smul_eq_mul,mul_ite]
  rw [he]
  apply Submodule.sum_mem
  intro π hπ
  exact Submodule.smul_mem _ _ (qv_mem H π (by simpa [liveSet] using hπ))

private lemma facet_vector {n : ℕ} (hn : 0 < n) (H : I n → I n → Bool)
    (π : Perm n) (hπ : live H π) :
    ∃ e : E n, H e.1 e.2=true ∧ qv π e=1 ∧
      ∃ w : Vec n, w∈ZV H ∧ (∀ f, 0 ≤ w f) ∧ w e=0 ∧
        ∀ z : Vec n, z∈ZV H → z e=0 → ∀ f, w f=0 → z f=0 := by
  classical
  let r : I n := ⟨0,hn⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (I n))
    (fun j => codeN H (π j,j)) ⟨r,Finset.mem_univ _⟩
  let e : E n := (π j,j)
  let w : Vec n := uVec H-(uVec H e) • qv π
  refine ⟨e,hπ j,by simp [qv,e],w,?_,?_,?_,?_⟩
  · exact Submodule.sub_mem _ (uVec_mem H) (Submodule.smul_mem _ _ (qv_mem H π hπ))
  · intro f
    by_cases hf : π f.2=f.1
    · have hm : codeN H e ≤ codeN H f := by
        have hh := hmin f.2 (Finset.mem_univ _)
        simpa only [e,hf] using hh
      have hq : uVec H e ≤ uVec H f := by
        dsimp only [uVec]
        exact_mod_cast hm
      simpa only [w,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,qv,if_pos hf,mul_one] using sub_nonneg.mpr hq
    · simp [w,qv,hf,uVec]
  · simp [w,e,qv]
  · intro z hz he f hf
    by_cases hp : π f.2=f.1
    · have hw : uVec H f=uVec H e := by
        have hh : uVec H f-uVec H e=0 := by
          simpa only [w,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,qv,if_pos hp,mul_one] using hf
        exact sub_eq_zero.mp hh
      have hc : codeN H f=codeN H e := by
        dsimp only [uVec] at hw
        exact_mod_cast hw
      exact (code_eq_coord H f e hc z hz).trans he
    · have hw : uVec H f=0 := by simpa [w,qv,hp] using hf
      have hc : codeN H f=0 := by
        dsimp only [uVec] at hw
        exact_mod_cast hw
      exact code_zero_coord H f hc z hz


private def eraseH {n : ℕ} (H : I n → I n → Bool) (e : E n) : I n → I n → Bool :=
  fun i j => H i j && decide ((i,j)≠e)

private lemma erase_live {n : ℕ} (H : I n → I n → Bool) (e : E n) (π : Perm n) :
    live (eraseH H e) π ↔ live H π ∧ π e.2≠e.1 := by
  classical
  simp only [live,eraseH,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun j => (h j).1,?_⟩
    intro he
    exact (h e.2).2 (Prod.ext he rfl)
  · rintro ⟨hπ,he⟩ j
    refine ⟨hπ j,?_⟩
    intro hj
    have hc := congrArg Prod.snd hj
    have hr := congrArg Prod.fst hj
    exact he (hc ▸ hr)

private lemma erase_span_le {n : ℕ} (H : I n → I n → Bool) (e : E n) : ZV (eraseH H e) ≤ ZV H := by
  apply Submodule.span_le.mpr
  rintro f ⟨π,hπ,rfl⟩
  exact qv_mem H π ((erase_live H e π).mp hπ).1

private lemma erase_span_zero {n : ℕ} (H : I n → I n → Bool) (e : E n)
    (z : Vec n) (hz : z∈ZV (eraseH H e)) : z e=0 :=
  support_span (eraseH H e) z hz e (by simp [eraseH])

private lemma nonneg_mem_erase {n : ℕ} (H : I n → I n → Bool) (r : I n) (e : E n)
    (z : Vec n) (hz : z∈ZV H) (hn : ∀ f, 0 ≤ z f) (he : z e=0) : z∈ZV (eraseH H e) := by
  apply nonneg_span (eraseH H e) r z (balanced_span H r z hz) hn
  intro f hf
  by_cases hfe : f=e
  · simpa only [hfe] using he
  · have hH : H f.1 f.2=false := by simpa [eraseH,hfe] using hf
    exact support_span H z hz f hH

private lemma perturb_kernel {n : ℕ} (H : I n → I n → Bool) (r : I n) (e : E n)
    (w : Vec n) (hw : w∈ZV H) (hn : ∀ f, 0 ≤ w f) (he : w e=0)
    (hzero : ∀ z : Vec n, z∈ZV H → z e=0 → ∀ f, w f=0 → z f=0) :
    ∀ z : Vec n, z∈ZV H → z e=0 → z∈ZV (eraseH H e) := by
  classical
  intro z hz hze
  let c : ℚ := ∑ f : E n, |z f| / w f
  let g : Vec n := c • w+z
  have hg : g∈ZV H := Submodule.add_mem _ (Submodule.smul_mem _ _ hw) hz
  have hgn : ∀ f, 0 ≤ g f := by
    intro f
    by_cases hf : w f=0
    · have hzf := hzero z hz hze f hf
      simp [g,hf,hzf]
    · have ht : |z f| / w f ≤ c :=
        Finset.single_le_sum (fun a _ => div_nonneg (abs_nonneg _) (hn a)) (Finset.mem_univ f)
      have hh := mul_le_mul_of_nonneg_right ht (hn f)
      rw [div_mul_cancel₀ _ hf] at hh
      change 0 ≤ c*w f+z f
      linarith [neg_abs_le (z f)]
  have hge : g e=0 := by simp [g,he,hze]
  have hwe := nonneg_mem_erase H r e w hw hn he
  have hge' := nonneg_mem_erase H r e g hg hgn hge
  have hdiff : g-c•w=z := by dsimp only [g]; abel
  have hh := Submodule.sub_mem (ZV (eraseH H e)) hge' (Submodule.smul_mem _ c hwe)
  rwa [hdiff] at hh

private lemma facet_step {n : ℕ} (hn : 0 < n) (H : I n → I n → Bool)
    (π : Perm n) (hπ : live H π) :
    ∃ e : E n, H e.1 e.2=true ∧ qv π e=1 ∧
      ∀ z : Vec n, z∈ZV H → z e=0 → z∈ZV (eraseH H e) := by
  obtain ⟨e,hH,hπe,w,hw,hnw,he,hzero⟩ := facet_vector hn H π hπ
  exact ⟨e,hH,hπe,perturb_kernel H ⟨0,hn⟩ e w hw hnw he hzero⟩

private lemma facet_dimension {n : ℕ} (H : I n → I n → Bool) (π : Perm n)
    (hπ : live H π) (e : E n) (hπe : qv π e=1)
    (hker : ∀ z : Vec n, z∈ZV H → z e=0 → z∈ZV (eraseH H e)) :
    Module.finrank ℚ (ZV H)=Module.finrank ℚ (ZV (eraseH H e))+1 := by
  let C : Submodule ℚ (Vec n) := Submodule.span ℚ {qv π}
  let D : Submodule ℚ (Vec n) := ZV (eraseH H e)
  have hC : C ≤ ZV H := Submodule.span_le.mpr (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact qv_mem H π hπ)
  have hD : D ≤ ZV H := erase_span_le H e
  have hsup : C⊔D=ZV H := by
    apply le_antisymm (sup_le hC hD)
    intro z hz
    have hf : z-z e•qv π∈D := hker _ (Submodule.sub_mem _ hz (Submodule.smul_mem _ _ (qv_mem H π hπ))) (by simp [hπe])
    have hc : z e•qv π∈C := Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    have heq : z=z e•qv π+(z-z e•qv π) := by abel
    rw [heq]
    exact (C⊔D).add_mem ((show C ≤ C⊔D from le_sup_left) hc) ((show D ≤ C⊔D from le_sup_right) hf)
  have hdis : Disjoint C D := by
    rw [Submodule.disjoint_def]
    intro z hzC hzD
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hzC
    have hz0 := erase_span_zero H e z hzD
    have hc0 : c=0 := by
      have hh := congrFun hc e
      simpa [hπe,hz0] using hh
    rw [← hc,hc0,zero_smul]
  have hC1 : Module.finrank ℚ C=1 := finrank_span_singleton (by
    intro hz
    have hh := congrFun hz e
    simpa [hπe] using hh)
  have hh := Submodule.finrank_sup_add_finrank_inf_eq C D
  rw [hsup,hdis.eq_bot,finrank_bot,add_zero,hC1] at hh
  change Module.finrank ℚ (ZV H)=Module.finrank ℚ D+1
  omega


private def iv {n : ℕ} (π : Perm n) : E n → ℤ := fun e => if π e.2=e.1 then 1 else 0
private def castV {n : ℕ} (z : E n → ℤ) : Vec n := fun e => (z e : ℚ)

private lemma cast_iv {n : ℕ} (π : Perm n) : castV (iv π)=qv π := by
  funext e
  simp [castV,iv,qv]

private def Rep {n m : ℕ} (b : Fin m → Perm n) (z : E n → ℤ) (a : Fin m → ℤ) : Prop :=
  ∀ e, z e=∑ h, a h*iv (b h) e

private def Good {n m : ℕ} (H : I n → I n → Bool) (b : Fin m → Perm n) : Prop :=
  (∀ h, live H (b h)) ∧ LinearIndependent ℚ (fun h => qv (b h)) ∧
    Submodule.span ℚ (Set.range (fun h => qv (b h)))=ZV H ∧
    ∀ z : E n → ℤ, castV z∈ZV H → ∃ a : Fin m → ℤ, Rep b z a

private lemma facet_sup {n : ℕ} (H : I n → I n → Bool) (π : Perm n)
    (hπ : live H π) (e : E n) (hπe : qv π e=1)
    (hker : ∀ z : Vec n, z∈ZV H → z e=0 → z∈ZV (eraseH H e)) :
    Submodule.span ℚ {qv π} ⊔ ZV (eraseH H e)=ZV H := by
  have hC : Submodule.span ℚ {qv π} ≤ ZV H := Submodule.span_le.mpr (by
    intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact qv_mem H π hπ)
  apply le_antisymm (sup_le hC (erase_span_le H e))
  intro z hz
  have hf : z-z e•qv π∈ZV (eraseH H e) := hker _
    (Submodule.sub_mem _ hz (Submodule.smul_mem _ _ (qv_mem H π hπ))) (by simp [hπe])
  have hc : z e•qv π∈Submodule.span ℚ {qv π} :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have heq : z=z e•qv π+(z-z e•qv π) := by abel
  rw [heq]
  exact Submodule.add_mem_sup hc hf

private lemma good_extend {n m : ℕ} (H : I n → I n → Bool) (π : Perm n)
    (hπ : live H π) (e : E n) (hπe : qv π e=1)
    (hker : ∀ z : Vec n, z∈ZV H → z e=0 → z∈ZV (eraseH H e))
    (b : Fin m → Perm n) (hb : Good (eraseH H e) b) : Good H (Fin.cons π b) := by
  classical
  have hvec : (fun h : Fin (m+1) => qv (Fin.cons (α:=fun _ : Fin (m+1) => Perm n) π b h))=
      Fin.cons (α:=fun _ : Fin (m+1) => Vec n) (qv π) (fun h => qv (b h)) := by
    funext i; refine Fin.cases rfl (fun j => rfl) i
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    refine Fin.cases hπ (fun j => ?_) h
    exact ((erase_live H e (b j)).mp (hb.1 j)).1
  · rw [hvec]
    apply hb.2.1.finCons
    rw [hb.2.2.1]
    intro hh
    have hz := erase_span_zero H e (qv π) hh
    rw [hπe] at hz
    norm_num at hz
  · rw [hvec,Fin.range_cons,Submodule.span_insert,hb.2.2.1]
    exact facet_sup H π hπ e hπe hker
  · intro z hz
    let z' : E n → ℤ := fun f => z f-z e*iv π f
    have hc : castV z'=castV z-(z e : ℚ)•qv π := by
      funext f
      simp [z',castV,iv,qv]
    have hz' : castV z'∈ZV (eraseH H e) := hker _ (by
      rw [hc]
      exact Submodule.sub_mem _ hz (Submodule.smul_mem _ _ (qv_mem H π hπ))) (by
        rw [hc]; simp [castV,hπe])
    obtain ⟨a,ha⟩ := hb.2.2.2 z' hz'
    refine ⟨Fin.cons (z e) a,?_⟩
    intro f
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    have hh := ha f
    change z f-z e*iv π f=∑ h, a h*iv (b h) f at hh
    linarith

private def maskCard {n : ℕ} (H : I n → I n → Bool) : ℕ :=
  (Finset.univ.filter (fun e : E n => H e.1 e.2)).card

private lemma maskCard_erase {n : ℕ} (H : I n → I n → Bool) (e : E n)
    (he : H e.1 e.2=true) : maskCard (eraseH H e) < maskCard H := by
  classical
  have hset : Finset.univ.filter (fun f : E n => eraseH H e f.1 f.2)=
      (Finset.univ.filter (fun f : E n => H f.1 f.2)).erase e := by
    ext ⟨i,j⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,eraseH,Bool.and_eq_true,
      decide_eq_true_eq,Finset.mem_erase]
    exact and_comm
  unfold maskCard
  rw [hset]
  exact Finset.card_erase_lt_of_mem (by simp [he])

private lemma zero_space {n : ℕ} (H : I n → I n → Bool) (h : ¬∃ π : Perm n, live H π) : ZV H=⊥ := by
  classical
  have he : {v : Vec n | ∃ π : Perm n, live H π ∧ v=qv π}=∅ := by
    ext v
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨π,hπ,hv⟩
    exact h ⟨π,hπ⟩
  simp [ZV,he]

private lemma good_zero {n : ℕ} (H : I n → I n → Bool) (h : ZV H=⊥) :
    Good H (fun i : Fin 0 => Fin.elim0 i) := by
  classical
  refine ⟨fun i => Fin.elim0 i,?_,?_,?_⟩
  · exact linearIndependent_empty_type
  · simp [h]
  · intro z hz
    rw [h,Submodule.mem_bot] at hz
    refine ⟨fun i => Fin.elim0 i,?_⟩
    intro e
    have hh := congrFun hz e
    simp only [castV,Pi.zero_apply] at hh
    have hz0 : z e=0 := by exact_mod_cast hh
    simpa only [Fin.sum_univ_zero] using hz0

private lemma basis_good {n : ℕ} (hn : 0 < n) (H : I n → I n → Bool) :
    ∃ b : Fin (Module.finrank ℚ (ZV H)) → Perm n, Good H b := by
  classical
  suffices ∀ k : ℕ, ∀ H : I n → I n → Bool, maskCard H=k →
      ∃ b : Fin (Module.finrank ℚ (ZV H)) → Perm n, Good H b from this _ H rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro H hsize
    by_cases hLive : ∃ π : Perm n, live H π
    · obtain ⟨π,hπ⟩ := hLive
      obtain ⟨e,he,hπe,hker⟩ := facet_step hn H π hπ
      have hlt : maskCard (eraseH H e) < k := by rw [← hsize]; exact maskCard_erase H e he
      obtain ⟨b,hb⟩ := ih _ hlt (eraseH H e) rfl
      have hd := facet_dimension H π hπ e hπe hker
      rw [hd]
      exact ⟨Fin.cons π b,good_extend H π hπ e hπe hker b hb⟩
    · have hzero := zero_space H hLive
      have hd : Module.finrank ℚ (ZV H)=0 := by rw [hzero]; exact finrank_bot ℚ (Vec n)
      rw [hd]
      exact ⟨_,good_zero H hzero⟩


private lemma cast_iv_apply {n : ℕ} (π : Perm n) (e : E n) : (iv π e : ℚ)=qv π e :=
  congrFun (cast_iv π) e

private lemma rep_cast {n m : ℕ} (b : Fin m → Perm n) (z : E n → ℤ) (a : Fin m → ℤ)
    (ha : Rep b z a) : ∑ h, (a h : ℚ) • qv (b h)=castV z := by
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,castV]
  have hh : (z e : ℚ)=∑ h, (a h : ℚ)*(iv (b h) e : ℚ) := by exact_mod_cast ha e
  simpa only [cast_iv_apply] using hh.symm

private lemma rep_unique {n m : ℕ} (b : Fin m → Perm n)
    (hb : LinearIndependent ℚ (fun h => qv (b h))) (z : E n → ℤ) (a c : Fin m → ℤ)
    (ha : Rep b z a) (hc : Rep b z c) : a=c := by
  have he : (fun h => (a h : ℚ))=(fun h => (c h : ℚ)) :=
    hb.fintypeLinearCombination_injective (by
      simp only [Fintype.linearCombination_apply]
      exact (rep_cast b z a ha).trans (rep_cast b z c hc).symm)
  funext h
  have hh := congrFun he h
  exact_mod_cast hh

private lemma pow_sum {G α : Type*} [CommGroup G] (S : Finset α) (x : G) (a : α → ℤ) :
    x^(∑ i∈S, a i)=∏ i∈S, x^(a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,zpow_add,ih]

private lemma prod_incidence {G : Type*} [CommGroup G] {n : ℕ} (W : E n → G) (π : Perm n) :
    (∏ e : E n, W e^(iv π e))=∏ j : I n, W (π j,j) := by
  classical
  have hp : ∀ e : E n, W e^(iv π e)=if π e.2=e.1 then W e else 1 := by
    intro e
    by_cases he : π e.2=e.1 <;> simp [iv,he]
  simp only [hp,Fintype.prod_prod_type]
  rw [Finset.prod_comm]
  simp

private lemma laurent_group {G : Type*} [CommGroup G] {n m : ℕ} (W : E n → G)
    (b : Fin m → Perm n) (π : Perm n) (a : Fin m → ℤ) (ha : Rep b (iv π) a) :
    (∏ j : I n, W (π j,j))=∏ h : Fin m, (∏ j : I n, W (b h j,j))^(a h) := by
  classical
  calc
    _ = ∏ e : E n, W e^(iv π e) := (prod_incidence W π).symm
    _ = ∏ e : E n, W e^(∑ h, a h*iv (b h) e) := by
      apply Finset.prod_congr rfl
      intro e _
      rw [ha e]
    _ = ∏ e : E n, ∏ h : Fin m, W e^(a h*iv (b h) e) := by
      apply Finset.prod_congr rfl
      intro e _
      exact pow_sum Finset.univ (W e) _
    _ = ∏ h : Fin m, ∏ e : E n, W e^(a h*iv (b h) e) := Finset.prod_comm
    _ = ∏ h : Fin m, (∏ e : E n, W e^(iv (b h) e))^(a h) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro e _
      rw [← zpow_mul]
      congr 1
      ring
    _ = _ := by simp only [prod_incidence]

private lemma laurent_complex {n m : ℕ} (H : I n → I n → Bool) (b : Fin m → Perm n)
    (hb : ∀ h, live H (b h)) (π : Perm n) (hπ : live H π) (a : Fin m → ℤ)
    (ha : Rep b (iv π) a) (A : Matrix (I n) (I n) ℂ)
    (hA : ∀ i j, H i j=true → A i j≠0) :
    (∏ j, A (π j) j)=∏ h, (∏ j, A (b h j) j)^(a h) := by
  classical
  let W : E n → ℂˣ := fun e => if h : H e.1 e.2=true then Units.mk0 (A e.1 e.2) (hA _ _ h) else 1
  have hwπ : ∀ j, (W (π j,j) : ℂ)=A (π j) j := by intro j; simp [W,hπ j]
  have hwb : ∀ h j, (W (b h j,j) : ℂ)=A (b h j) j := by intro h j; simp [W,hb h j]
  have hg := laurent_group W b π a ha
  have hc := congrArg (Units.coeHom ℂ) hg
  simp only [map_prod,map_zpow,Units.coeHom_apply,hwπ,hwb] at hc
  exact hc

private lemma main_result {n : ℕ} (hn : 0 < n) (H : I n → I n → Bool) :
    ∃ b : Fin (Module.finrank ℚ (ZV H)) → Perm n, (∀ h, live H (b h)) ∧
      (∀ z : E n → ℤ, castV z∈ZV H → ∃! a : Fin (Module.finrank ℚ (ZV H)) → ℤ, Rep b z a) ∧
      ∀ π : Perm n, live H π → ∃ a : Fin (Module.finrank ℚ (ZV H)) → ℤ,
        ∀ A : Matrix (I n) (I n) ℂ, (∀ i j, H i j=true → A i j≠0) →
          (∏ j, A (π j) j)=∏ h, (∏ j, A (b h j) j)^(a h) := by
  obtain ⟨b,hb⟩ := basis_good hn H
  refine ⟨b,hb.1,?_,?_⟩
  · intro z hz
    obtain ⟨a,ha⟩ := hb.2.2.2 z hz
    exact ⟨a,ha,fun c hc => rep_unique b hb.2.1 z c a hc ha⟩
  · intro π hπ
    obtain ⟨a,ha⟩ := hb.2.2.2 (iv π) (by rw [cast_iv]; exact qv_mem H π hπ)
    exact ⟨a,fun A hA => laurent_complex H b hb.1 π hπ a ha A hA⟩

end PEqualNP.Outside.L_lib_1075

open PEqualNP.Outside.L_lib_1075

theorem PEqualNP.Outside.L_lib_1075 : (∀ (n : ℕ) (H : Fin n → Fin n → Bool), 0 < n →
  let I := Fin n
  let E := I × I
  let live := fun π : Equiv.Perm I => ∀ j, H (π j) j = true
  let v := fun (π : Equiv.Perm I) (e : E) => if π e.2 = e.1 then (1 : ℤ) else 0
  let V := Submodule.span ℚ {w : E → ℚ | ∃ π : Equiv.Perm I, live π ∧ w = fun e => (v π e : ℚ)}
  let d := Module.finrank ℚ V
  let prod := fun (A : Matrix I I ℂ) (π : Equiv.Perm I) => ∏ j : I, A (π j) j
  ∃ basis : Fin d → Equiv.Perm I, (∀ h, live (basis h)) ∧
    (∀ z : E → ℤ, (fun e => (z e : ℚ)) ∈ V →
      ∃! a : Fin d → ℤ, ∀ e : E, z e = ∑ h : Fin d, a h * v (basis h) e) ∧
    ∀ π : Equiv.Perm I, live π → ∃ a : Fin d → ℤ,
      ∀ A : Matrix I I ℂ, (∀ i j, H i j = true → A i j ≠ 0) →
        prod A π = ∏ h : Fin d, (prod A (basis h))^(a h)) := by
  intro n H hn
  let V0 : Submodule ℚ ((Fin n × Fin n) → ℚ) :=
    Submodule.span ℚ {w | ∃ π : Equiv.Perm (Fin n), live H π ∧ w=castV (iv π)}
  have hV : V0=ZV H := by
    simp only [V0,cast_iv,ZV]
  change ∃ b : Fin (Module.finrank ℚ V0) → Equiv.Perm (Fin n),
    (∀ h, live H (b h)) ∧
    (∀ z : (Fin n × Fin n) → ℤ, castV z∈V0 → ∃! a : Fin (Module.finrank ℚ V0) → ℤ, Rep b z a) ∧
    ∀ π : Equiv.Perm (Fin n), live H π → ∃ a : Fin (Module.finrank ℚ V0) → ℤ,
      ∀ A : Matrix (Fin n) (Fin n) ℂ, (∀ i j, H i j=true → A i j≠0) →
        (∏ j, A (π j) j)=∏ h, (∏ j, A (b h j) j)^(a h)
  rw [hV]
  exact main_result hn H
