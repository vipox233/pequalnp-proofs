import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1444_aux
def Width {m : ℕ} (A B : Fin m → Finset ℕ) (r w a f : ℕ) := ∃g h : Finset ℕ → Finset ℕ,
  Monotone g ∧ Monotone h ∧ (∀X ⊆ Finset.range r,g X ⊆ Finset.range w) ∧ (∀Y ⊆ Finset.range w,h Y ⊆ Finset.range r) ∧
  ∀i X Y,A i ⊆ X → X ⊆ B i → Y ⊆ Finset.range w → (g X\Y).card ≤ a → (Y\g X).card ≤ f → A i ⊆ h Y ∧ h Y ⊆ B i

theorem measure {S T Y : Finset ℕ} : (S\T).card ≤ (S\Y).card+(Y\T).card := by
  apply le_trans (Finset.card_le_card (t:=(S\Y)∪(Y\T)) _) (Finset.card_union_le ..)
  intro x hx
  simp only [Finset.mem_union,Finset.mem_sdiff] at *
  tauto

theorem noisyIff (A B : Fin m → Finset ℕ) (valid : ∀i,A i ⊆ B i ∧ B i ⊆ Finset.range r) :
    Width A B r w a f ↔ ∃g : Finset ℕ → Finset ℕ,Monotone g ∧ (∀X ⊆ Finset.range r,g X ⊆ Finset.range w) ∧
      ∀i j, ¬ A i ⊆ B j → a+f+1 ≤ (g (A i)\g (B j)).card := by
  classical
  constructor
  · rintro ⟨g,h,gm,hm,cap,_,recover⟩
    refine ⟨g,gm,cap,?_⟩
    intro i j bad
    by_contra! small
    let S := g (A i)
    let T := g (B j)
    let D := S\T
    have ss : S ⊆ Finset.range w := cap _ ((valid i).1.trans (valid i).2)
    have tt : T ⊆ Finset.range w := cap _ (valid j).2
    obtain ⟨Z,zd,zs⟩ := Finset.exists_subset_card_eq (s:=D) (Nat.min_le_right a D.card)
    let X := S\Z
    let Y := T∪(D\Z)
    have sub : X ⊆ Y := by
      intro v hv
      simp only [X,Y,D,Finset.mem_union,Finset.mem_sdiff] at *
      tauto
    have ZS : Z ⊆ S := zd.trans Finset.sdiff_subset
    have eq : S\X=Z := by
      ext v
      simp only [X,Finset.mem_sdiff]
      have := fun (hz : v∈Z) => ZS hz
      tauto
    have gain : (Y\T).card ≤ f := by
      have inc : Y\T ⊆ D\Z := by intro v hv; simp only [Y,Finset.mem_union,Finset.mem_sdiff] at *; tauto
      have c := Finset.card_le_card inc
      rw [Finset.card_sdiff_of_subset zd,zs] at c
      change D.card<a+f+1 at small
      omega
    have left := (recover i (A i) X (fun _ h => h) (valid i).1 (Finset.sdiff_subset.trans ss)
      (by change (S\X).card ≤ a; rw [eq,zs]; exact Nat.min_le_left ..)
      (by change (X\S).card ≤ f; simp [Finset.sdiff_eq_empty_iff_subset.mpr (show X ⊆ S from Finset.sdiff_subset)])).1
    have right := (recover j (B j) Y (valid j).1 (fun _ h => h)
      (Finset.union_subset tt (Finset.sdiff_subset.trans (Finset.sdiff_subset.trans ss)))
      (by change (T\Y).card ≤ a; simp [Finset.sdiff_eq_empty_iff_subset.mpr (show T ⊆ Y from Finset.subset_union_left)]) gain).2
    exact bad (left.trans ((hm sub).trans right))
  · rintro ⟨g,gm,cap,gap⟩
    let inds (Y : Finset ℕ) := Finset.univ.filter (fun i => (g (A i)\Y).card ≤ a)
    let h (Y) := (inds Y).biUnion A
    have hm : Monotone h := by
      intro X Y xy x hx
      obtain ⟨i,mem,yes⟩ := Finset.mem_biUnion.mp hx
      have bound := (Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl (g (A i))) xy)).trans (Finset.mem_filter.mp mem).2
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bound⟩,yes⟩
    refine ⟨g,h,gm,hm,cap,?_,?_⟩
    · intro Y _ x hx
      obtain ⟨i,_,yes⟩ := Finset.mem_biUnion.mp hx
      exact (valid i).2 ((valid i).1 yes)
    · intro i X Y ax xb _ lost gain
      constructor
      · intro x hx
        have low := (Finset.card_le_card (Finset.sdiff_subset_sdiff (gm ax) (Finset.Subset.refl Y))).trans lost
        exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,low⟩,hx⟩
      · intro x hx
        obtain ⟨j,mem,yes⟩ := Finset.mem_biUnion.mp hx
        by_contra no
        have far := gap j i (fun h => no (h yes))
        have bound := (Finset.mem_filter.mp mem).2
        have plus := (Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl Y) (gm xb))).trans gain
        have triangle := measure (S:=g (A j)) (T:=g (B i)) (Y:=Y)
        omega
end PEqualNP.Outside.L_lib_1444_aux

namespace PEqualNP.Outside.L_lib_1444_aux
abbrev bits (n : ℕ) := Nat.log2 (n+1)+3
abbrev k (n m : ℕ) := bits n+bits m
abbrev r (n m : ℕ) := n+k n m
abbrev Stage (n m : ℕ) := Fin (n+m+k n m+1)
def tag (off d j : ℕ) := insert (off+1) (((Finset.range (d-2)).filter (fun z => j/2^z % 2=1)).image (fun z => off+2+z))
def common (n m j : ℕ) := if j<n then tag n (bits n) j else if j<n+m then
  Finset.Ico n (n+bits n) ∪ tag (n+bits n) (bits m) (j-n) else Finset.Ico n (n+(j-(n+m)))
def A (n m : ℕ) (j : Stage n m) := if j.val<n then insert j.val (common n m j.val) else common n m j.val
def B (n m : ℕ) (E : Finset ℕ) (j : Stage n m) := common n m j.val ∪
  (if n ≤ j.val ∧ j.val<n+m then (Finset.range n).filter (fun i => i*m+(j.val-n)∉E) else Finset.range n)

theorem tagProp {off N j x : ℕ} (h : x∈tag off (bits N) j) : off<x ∧ x<off+bits N := by
  rcases Finset.mem_insert.mp h with rfl|h
  · dsimp [bits]; omega
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    dsimp [bits] at *; omega
theorem tagMark (off d j : ℕ) : off+1∈tag off d j := Finset.mem_insert_self ..
theorem tagUnique (off N i j : ℕ) (ii : i<N) (jj : j<N) (same : tag off (bits N) i=tag off (bits N) j) : i=j := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
  by_cases short : b<bits N-2
  · have read (z : ℕ) : off+2+b∈tag off (bits N) z ↔ z/2^b % 2=1 := by
      simp [tag,short,show off+2+b≠off+1 by omega]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq,←read,same])
  · have bd : N+1<2^(Nat.log2 (N+1)+1) := Nat.lt_log2_self
    have pow : 2^(Nat.log2 (N+1)+1) ≤ 2^b := Nat.pow_le_pow_right (by decide) (by dsimp [bits] at short; omega)
    simp [Nat.div_eq_of_lt (show i<2^b by omega),Nat.div_eq_of_lt (show j<2^b by omega)]
theorem loTag (i : Stage n m) (x) (hx : x∈common n m i.val) : n ≤ x ∧ x<r n m := by
  have lt := i.isLt
  unfold common at hx
  split at hx
  · have := tagProp hx; dsimp [r,k]; omega
  · split at hx
    · rcases Finset.mem_union.mp hx with hx|hx
      · have := Finset.mem_Ico.mp hx; dsimp [r,k]; omega
      · have := tagProp hx; dsimp [r,k]; omega
    · have := Finset.mem_Ico.mp hx; dsimp only [r]; omega
theorem tagSub (i : Stage n m) : common n m i.val ⊆ A n m i := by unfold A; split; exact Finset.subset_insert ..; exact fun _ h => h
theorem fromB {i : Stage n m} {x : ℕ} (hx : x∈B n m E i) (hi : n ≤ x) : x∈common n m i.val := by
  rcases Finset.mem_union.mp hx with h|h
  · exact h
  · split at h
    · have := Finset.mem_range.mp (Finset.mem_filter.mp h).1; omega
    · have := Finset.mem_range.mp h; omega
theorem inside (E : Finset ℕ) (i : Stage n m) : A n m i ⊆ B n m E i ∧ B n m E i ⊆ Finset.range (r n m) := by
  constructor
  · by_cases l : i.val<n
    · have nope : ¬(n ≤ i.val ∧ i.val<n+m) := by omega
      simp only [A,B,l,ite_true,nope,ite_false,Finset.insert_subset_iff]
      exact ⟨Finset.mem_union_right _ (Finset.mem_range.mpr l),Finset.subset_union_left⟩
    · simp only [A,l,ite_false,B]; exact Finset.subset_union_left
  · intro x hx
    by_cases hi : n ≤ x
    · exact Finset.mem_range.mpr (loTag i x (fromB hx hi)).2
    · exact Finset.mem_range.mpr (by dsimp [r]; omega)
end PEqualNP.Outside.L_lib_1444_aux

namespace PEqualNP.Outside.L_lib_1444_aux
def left (i : Fin n) (m : ℕ) : Stage n m := ⟨i.val,by have := i.isLt; omega⟩
def right (n : ℕ) (j : Fin m) : Stage n m := ⟨n+j.val,by have := j.isLt; omega⟩
def guard (n m g : ℕ) (h : g ≤ k n m) : Stage n m := ⟨n+m+g,by omega⟩
theorem guardA (h : g ≤ k n m) : A n m (guard n m g h)=Finset.Ico n (n+g) := by
  simp [A,common,guard,show ¬n+m+g<n by omega,show ¬n+m+g<n+m by omega]
theorem guardB (E : Finset ℕ) (h : g ≤ k n m) : B n m E (guard n m g h)=Finset.Ico n (n+g) ∪ Finset.range n := by
  simp [B,common,guard,show ¬n+m+g<n by omega,show ¬n+m+g<n+m by omega]
theorem guardConflict (E : Finset ℕ) (g : Fin (k n m)) :
    ¬ A n m (guard n m (g.val+1) g.isLt) ⊆ B n m E (guard n m g.val g.isLt.le) := by
  rw [guardA,guardB]
  intro h
  have x := h (show n+g.val∈Finset.Ico n (n+(g.val+1)) by simp)
  simpa using x
theorem guardForward (E : Finset ℕ) (g h : Fin (k n m)) (lt : g<h) :
    A n m (guard n m (g.val+1) g.isLt) ⊆ B n m E (guard n m h.val h.isLt.le) := by
  rw [guardA,guardB]
  exact (Finset.Ico_subset_Ico (le_refl _) (Nat.add_le_add_left lt n)).trans Finset.subset_union_left
theorem leftA (i : Fin n) : A n m (left i m)=insert i.val (tag n (bits n) i.val) := by simp [A,common,left,i.isLt]
theorem rightB (E : Finset ℕ) (j : Fin m) : B n m E (right n j)=Finset.Ico n (n+bits n) ∪ tag (n+bits n) (bits m) j.val ∪
    (Finset.range n).filter (fun i => i*m+j.val∉E) := by simp [B,common,right,j.isLt,Nat.not_lt_of_ge (Nat.le_add_right n j.val)]
theorem leftTags (i : Fin n) : tag n (bits n) i.val ⊆ Finset.Ico n (n+bits n) :=
  fun _ hx => Finset.mem_Ico.mpr ⟨(tagProp hx).1.le,(tagProp hx).2⟩
theorem source (E : Finset ℕ) (i : Fin n) (j : Fin m) :
    A n m (left i m) ⊆ B n m E (right n j) ↔ i.val*m+j.val∉E := by
  rw [leftA,rightB,Finset.insert_subset_iff]
  have excl : i.val∉tag (n+bits n) (bits m) j.val := fun hx => by have := (tagProp hx).1; have := i.isLt; omega
  have tags := (leftTags i).trans ((Finset.subset_union_left (s₂:=tag (n+bits n) (bits m) j.val)).trans (Finset.subset_union_left (s₂:=(Finset.range n).filter (fun x => x*m+j.val∉E))))
  rw [and_iff_left tags]
  simp [excl,i.isLt,show ¬n ≤ i.val from i.isLt.not_ge]
theorem guardToRight (E : Finset ℕ) (g : Fin (k n m)) (before : g.val<bits n) (j : Fin m) :
    A n m (guard n m (g.val+1) g.isLt) ⊆ B n m E (right n j) := by
  rw [guardA,rightB]
  exact (Finset.Ico_subset_Ico (le_refl _) (Nat.add_le_add_left before n)).trans (Finset.subset_union_left.trans Finset.subset_union_left)
theorem leftToGuard (E : Finset ℕ) (g : Fin (k n m)) (after : bits n ≤ g.val) (i : Fin n) :
    A n m (left i m) ⊆ B n m E (guard n m g.val g.isLt.le) := by
  rw [leftA,guardB,Finset.insert_subset_iff]
  exact ⟨Finset.mem_union_right _ (Finset.mem_range.mpr i.isLt),
    (leftTags i).trans ((Finset.Ico_subset_Ico (le_refl _) (Nat.add_le_add_left after n)).trans Finset.subset_union_left)⟩
end PEqualNP.Outside.L_lib_1444_aux

namespace PEqualNP.Outside.L_lib_1444_aux
def hits {c : ℕ} (P N : Fin c → Finset ℕ) (i j) := Finset.univ.filter (fun b => i∈P b ∧ j∈N b)
def Rect (n m : ℕ) (E : Finset ℕ) (c t : ℕ) := ∃P N : Fin c → Finset ℕ,∀ i < n,∀ j < m,
    (i*m+j∈E → t ≤ (hits P N i j).card) ∧ (i*m+j∉E → (hits P N i j).card=0)
theorem rectangles (E : Finset ℕ) (L : Fin n → Finset ℕ) (R : Fin m → Finset ℕ) (V : Finset ℕ)
    (sz : V.card ≤ c) (within : ∀i j,L i\R j ⊆ V)
    (yes : ∀i j,i.val*m+j.val∈E → t ≤ (L i\R j).card)
    (no : ∀i j,i.val*m+j.val∉E → L i ⊆ R j) : Rect n m E c t := by
  classical
  let enum := V.orderIsoOfFin rfl
  let val (b : Fin V.card) := (enum b).val
  let P (b : Fin c) := if hb : b.val<V.card then (Finset.range n).filter (fun i => ∃bi : i<n,val ⟨b.val,hb⟩∈L ⟨i,bi⟩) else ∅
  let N (b : Fin c) := if hb : b.val<V.card then (Finset.range m).filter (fun j => ∃bj : j < m,val ⟨b.val,hb⟩∉R ⟨j,bj⟩) else ∅
  refine ⟨P,N,?_⟩
  intro i hi j hj
  let I : Fin n := ⟨i,hi⟩
  let J : Fin m := ⟨j,hj⟩
  have hit (b : Fin c) (hb : b.val<V.card) : b∈hits P N i j ↔ val ⟨b.val,hb⟩∈L I\R J := by
    simp [hits,P,N,hb,hi,hj,I,J]
  constructor
  · intro edge
    apply (yes I J edge).trans
    let F (x : ↥(L I\R J)) : Fin c :=
      let p := enum.symm ⟨x.val,within I J x.property⟩
      ⟨p.val,p.isLt.trans_le sz⟩
    have hv (x : ↥(L I\R J)) : (F x).val<V.card := (enum.symm ⟨x.val,within I J x.property⟩).isLt
    have undo (x : ↥(L I\R J)) : val ⟨(F x).val,hv x⟩=x.val :=
      congrArg Subtype.val (enum.apply_symm_apply ⟨x.val,within I J x.property⟩)
    let G (x : ↥(L I\R J)) : ↥(hits P N i j) := ⟨F x,(hit _ (hv x)).mpr ((undo x).symm ▸ x.property)⟩
    have inj : Function.Injective G := by
      intro x y eq
      have same : (F x).val=(F y).val := congrArg (fun z : ↥(hits P N i j) => z.val.val) eq
      apply Subtype.ext
      exact (undo x).symm.trans ((congrArg val (Fin.ext same)).trans (undo y))
    simpa using Fintype.card_le_of_injective G inj
  · intro none
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b on
    by_cases hb : b.val<V.card
    · have m := Finset.mem_sdiff.mp ((hit b hb).mp on)
      exact m.2 (no I J none m.1)
    · have yes := (Finset.mem_filter.mp on).2.1
      simpa [P,hb] using yes

theorem lower (E : Finset ℕ) (fit : Width (A n m) (B n m E) (r n m) w a f) :
    k n m*(a+f+1) ≤ w ∧ Rect n m E (w-k n m*(a+f+1)) (a+f+1) := by
  classical
  obtain ⟨g,mono,cap,gap⟩ := (noisyIff _ _ (inside E)).mp fit
  let S (i : Fin (k n m)) := g (A n m (guard n m (i.val+1) i.isLt))\g (B n m E (guard n m i.val i.isLt.le))
  let reserved := Finset.univ.biUnion S
  have none (i j : Fin (k n m)) (lt : i<j) : Disjoint (S i) (S j) := by
    apply Finset.disjoint_left.mpr
    intro x xi xj
    exact (Finset.mem_sdiff.mp xj).2 (mono (guardForward E i j lt) (Finset.mem_sdiff.mp xi).1)
  have disj : (↑(Finset.univ : Finset (Fin (k n m))) : Set _).PairwiseDisjoint S := by
    intro i _ j _ ne
    exact (lt_or_gt_of_ne ne).elim (none i j) (fun lt => (none j i lt).symm)
  have use : k n m*(a+f+1) ≤ reserved.card := by
    dsimp only [reserved]
    rw [Finset.card_biUnion disj]
    simpa using (Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ : Fin (k n m) => a+f+1) (g:=fun i => (S i).card)
      (fun i _ => gap _ _ (guardConflict E i)))
  have small (i) : g (A n m i) ⊆ Finset.range w := cap _ ((inside E i).1.trans (inside E i).2)
  have inRange : reserved ⊆ Finset.range w := by
    intro x hx
    obtain ⟨i,_,h⟩ := Finset.mem_biUnion.mp hx
    exact small _ (Finset.mem_sdiff.mp h).1
  refine ⟨use.trans (by simpa using Finset.card_le_card inRange),?_⟩
  apply rectangles E (fun i => g (A _ _ (left i m))) (fun j => g (B _ _ E (right n j))) (Finset.range w\reserved)
  · rw [Finset.card_sdiff_of_subset inRange,Finset.card_range]
    omega
  · intro i j x hx
    obtain ⟨xl,xr⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨small _ xl,?_⟩
    intro hh
    obtain ⟨b,_,haveBit⟩ := Finset.mem_biUnion.mp hh
    by_cases before : b.val<bits n
    · exact xr (mono (guardToRight E b before j) (Finset.mem_sdiff.mp haveBit).1)
    · exact (Finset.mem_sdiff.mp haveBit).2 (mono (leftToGuard E b (by omega) i) xl)
  · intro i j edge
    exact gap _ _ (fun h => (source E i j).mp h edge)
  · intro i j nonedge
    exact mono ((source E i j).mpr nonedge)
end PEqualNP.Outside.L_lib_1444_aux

namespace PEqualNP.Outside.L_lib_1444_aux
def encode (n k t w : ℕ) (P : Fin c → Finset ℕ) (X : Finset ℕ) :=
  (Finset.range w).filter (fun b => if b < k*t then n+b/t∈X else
    ∃j : Fin c,b=k*t+j.val ∧ ∃i < n,i∈X ∧ i∈P j)
theorem up {n k t w c : ℕ} (P : Fin c → Finset ℕ) : Monotone (encode n k t w P) := by
  intro X Y xy b h
  obtain ⟨bound,yes⟩ := Finset.mem_filter.mp h
  refine Finset.mem_filter.mpr ⟨bound,?_⟩
  split at yes <;> rename_i side
  · rw [if_pos side]; exact xy yes
  · rw [if_neg side]
    obtain ⟨j,eq,i,small,hx,pi⟩ := yes
    exact ⟨j,eq,i,small,xy hx,pi⟩
theorem tagGap {n k t w c : ℕ} (P : Fin c → Finset ℕ) (baseBudget : k*t ≤ w) (off : ℕ) (slot : off < k) (pos : 0 < t)
    (yes : n+off∈X) (no : n+off∉Y) : t ≤ ((encode n k t w P X)\(encode n k t w P Y)).card := by
  let I := Finset.Ico (off*t) ((off+1)*t)
  have size : I.card=t := by simp [I,Nat.succ_mul]
  apply size.ge.trans
  apply Finset.card_le_card
  intro b hb
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hb
  have small : b < k*t := hi.trans_le (Nat.mul_le_mul_right t slot)
  have index : b/t=off := Nat.div_eq_of_lt_le lo hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (small.trans_le baseBudget),by simpa [small,index] using yes⟩,
    fun hy => no (by simpa [small,index] using (Finset.mem_filter.mp hy).2)⟩

theorem upper (E : Finset ℕ) (bnd : k n m*(a+f+1) ≤ w) (rect : Rect n m E (w-k n m*(a+f+1)) (a+f+1)) :
    Width (A n m) (B n m E) (r n m) w a f := by
  classical
  obtain ⟨P,N,cert⟩ := rect
  let t := a+f+1
  let base := k n m*t
  let g := encode n (k n m) t w P
  apply (noisyIff _ _ (inside E)).mpr
  refine ⟨g,up P,fun _ _ => Finset.filter_subset ..,?_⟩
  intro i j denied
  obtain ⟨x,hx,miss⟩ := Finset.not_subset.mp denied
  have below := Finset.mem_range.mp ((inside E i).2 ((inside E i).1 hx))
  by_cases raw : x < n
  · have xi : x=i.val ∧ i.val < n := by
      unfold A at hx
      split at hx
      · rename_i li
        rcases Finset.mem_insert.mp hx with eq|h
        · exact ⟨eq,li⟩
        · exact (raw.not_ge (loTag i _ h).1).elim
      · exact (raw.not_ge (loTag i _ hx).1).elim
    have right : n ≤ j.val ∧ j.val < n+m := by
      by_contra none
      exact miss (by unfold B; rw [if_neg none]; exact Finset.mem_union_right _ (Finset.mem_range.mpr raw))
    have col : j.val-n < m := by omega
    have rawB (y) (ys : y < n) : y∈B n m E j ↔ y*m+(j.val-n)∉E := by
      have noTag : y∉common n m j.val := fun hh => ys.not_ge (loTag j _ hh).1
      simp only [B,if_pos right,Finset.mem_union,noTag,false_or,Finset.mem_filter,Finset.mem_range,ys,true_and]
    have edge : x*m+(j.val-n)∈E := by by_contra h; exact miss ((rawB x raw).mpr h)
    let K := hits P N x (j.val-n)
    let b (h : Fin (w-base)) := base+h.val
    have inj : Function.Injective b := by intro u v eq; apply Fin.ext; exact Nat.add_left_cancel eq
    have inc : K.image b ⊆ g (A n m i)\g (B n m E j) := by
      intro bit mem
      obtain ⟨h,inK,rfl⟩ := Finset.mem_image.mp mem
      obtain ⟨ph,nh⟩ := (Finset.mem_filter.mp inK).2
      have lim := h.isLt
      have bw : b h < w := by dsimp [b]; change base ≤ w at bnd; omega
      have skip : ¬b h < k n m*t := by dsimp [b,base]; omega
      have active : b h∈g (A n m i) := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr bw,by
        rw [if_neg skip]
        exact ⟨h,rfl,x,raw,hx,ph⟩⟩
      refine Finset.mem_sdiff.mpr ⟨active,?_⟩
      intro on
      have yes := (Finset.mem_filter.mp on).2
      rw [if_neg skip] at yes
      obtain ⟨h',hb,y,yl,yb,py⟩ := yes
      have eq : h=h' := inj hb
      subst h'
      have zero := (cert y yl _ col).2 ((rawB y yl).mp yb)
      have witness : h∈hits P N y (j.val-n) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,py,nh⟩
      exact (Finset.card_pos.mpr ⟨h,witness⟩).ne' zero
    have s := Finset.card_le_card inc
    rw [Finset.card_image_of_injective _ inj] at s
    exact ((cert x raw _ col).1 edge).trans s
  · have run : x-n < k n m := by dsimp [r] at below; omega
    apply tagGap P bnd (x-n) run (by omega)
    · simpa [Nat.add_sub_of_le (show n ≤ x by omega)] using hx
    · simpa [Nat.add_sub_of_le (show n ≤ x by omega)] using miss
end PEqualNP.Outside.L_lib_1444_aux

namespace PEqualNP.Outside.L_lib_1444_aux
theorem gapInAddress {i : ℕ} (hi : i<n+m) :
    ∃x,n ≤ x ∧ x∉common n m i ∧ x+1∈common n m i := by
  by_cases l : i<n
  · simp only [common,l,ite_true]
    exact ⟨n,le_rfl,fun h => (tagProp h).1.false,tagMark ..⟩
  · simp only [common,l,ite_false,hi,ite_true]
    refine ⟨n+bits n,Nat.le_add_right ..,?_,Finset.mem_union_right _ (tagMark ..)⟩
    intro h
    rcases Finset.mem_union.mp h with hx|hx
    · exact (Finset.mem_Ico.mp hx).2.false
    · exact (tagProp hx).1.false
theorem addrInj (i j : Stage n m) (eq : common n m i.val=common n m j.val) : i=j := by
  have sameBlock {i j : Stage n m} (eq : common n m i.val=common n m j.val) (hi : i.val<n+m) : j.val<n+m := by
    by_contra no
    have nj : ¬j.val<n := by omega
    obtain ⟨x,lo,absent,yes⟩ := gapInAddress hi
    rw [eq] at absent yes
    simp only [common,nj,no,ite_false,Finset.mem_Ico] at absent yes
    omega
  by_cases enc : i.val<n+m
  · have encj := sameBlock eq enc
    have leftTest (i : Stage n m) (enc : i.val<n+m) : n∈common n m i.val ↔ ¬i.val<n := by
      by_cases l : i.val<n
      · simp only [common,l,ite_true,not_true_eq_false,iff_false]
        exact fun h => (tagProp h).1.false
      · simp [common,l,enc,bits]
    have sides : i.val<n ↔ j.val<n := by
      have e : n∈common n m i.val ↔ n∈common n m j.val := by rw [eq]
      rw [leftTest i enc,leftTest j encj] at e
      tauto
    by_cases el : i.val<n
    · have jl := sides.mp el
      simp only [common,el,jl,ite_true] at eq
      exact Fin.ext (tagUnique n n _ _ el jl eq)
    · have jl : ¬j.val<n := fun h => el (sides.mpr h)
      simp only [common,el,jl,enc,encj,ite_false,ite_true] at eq
      have tags : tag (n+bits n) (bits m) (i.val-n)=tag (n+bits n) (bits m) (j.val-n) := by
        ext x
        have mem : x∈Finset.Ico n (n+bits n) ∪ tag (n+bits n) (bits m) (i.val-n) ↔
          x∈Finset.Ico n (n+bits n) ∪ tag (n+bits n) (bits m) (j.val-n) := by rw [eq]
        by_cases v : x∈Finset.Ico n (n+bits n)
        · have b := (Finset.mem_Ico.mp v).2
          constructor <;> intro h <;> exact False.elim (b.not_gt (tagProp h).1)
        · simpa [v] using mem
      have q := tagUnique (n+bits n) m _ _ (by omega : i.val-n < m) (by omega : j.val-n < m) tags
      exact Fin.ext (by omega)
  · have encj : ¬j.val<n+m := fun h => enc (sameBlock eq.symm h)
    simp only [common,show ¬i.val<n by omega,show ¬j.val<n by omega,enc,encj,ite_false] at eq
    have cards := congrArg Finset.card eq
    simp at cards
    exact Fin.ext (by omega)
theorem uniqueBox (E : Finset ℕ) (i j : Stage n m) (X : Finset ℕ)
    (ai : A n m i ⊆ X) (bi : X ⊆ B n m E i) (aj : A n m j ⊆ X) (bj : X ⊆ B n m E j) : i=j := by
  have transfer {i j : Stage n m} (sub : A n m i ⊆ B n m E j) : common n m i.val ⊆ common n m j.val :=
    fun x hx => fromB (sub (tagSub i hx)) (loTag i x hx).1
  exact addrInj i j (Finset.Subset.antisymm (transfer (ai.trans bj)) (transfer (aj.trans bi)))
end PEqualNP.Outside.L_lib_1444_aux

namespace PEqualNP.Outside.L_lib_1444_aux
def minus (A B : Finset ℕ) := A\B
theorem sameDiff (d : DecidableEq ℕ) (A B : Finset ℕ) : @SDiff.sdiff _ (@Finset.instSDiff ℕ d) A B=minus A B := by
  rw [Subsingleton.elim d instDecidableEqNat]; rfl
noncomputable def select {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem sameFilter {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) : @Finset.filter α P d A=select P A := by
  ext x; simp only [select,Finset.mem_filter]
end PEqualNP.Outside.L_lib_1444_aux
open PEqualNP.Outside.L_lib_1444_aux in
theorem PEqualNP.Outside.L_lib_1444 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n m : Nat) (E : Finset Nat), E ⊆ Finset.range (n*m) →
  let s := Nat.log2 (n+1)+3
  let u := Nat.log2 (m+1)+3
  let k := s+u
  let r := n+k
  let tag := fun (off d j : Nat) => insert (off+1)
    (((Finset.range (d-2)).filter (fun z => j/2^z % 2=1)).image (fun z => off+2+z))
  let common := fun j : Nat => if j<n then tag n s j else if j<n+m then
    Finset.Ico n (n+s) ∪ tag (n+s) u (j-n) else Finset.Ico n (n+(j-(n+m)))
  let A := fun (j : Fin (n+m+k+1)) => if j.val<n then insert j.val (common j.val) else common j.val
  let B := fun (j : Fin (n+m+k+1)) => common j.val ∪
    (if n≤j.val ∧ j.val<n+m then (Finset.range n).filter (fun i => i*m+(j.val-n) ∉ E) else Finset.range n)
  let width := fun (w a f : Nat) => ∃ (g h : Finset Nat → Finset Nat), Monotone g ∧ Monotone h ∧
    (∀ X ⊆ Finset.range r, g X ⊆ Finset.range w) ∧ (∀ Y ⊆ Finset.range w, h Y ⊆ Finset.range r) ∧
    ∀ i X Y, A i ⊆ X → X ⊆ B i → Y ⊆ Finset.range w →
      (g X \ Y).card ≤ a → (Y \ g X).card ≤ f → A i ⊆ h Y ∧ h Y ⊆ B i
  let rect := fun (c t : Nat) => ∃ (P N : Fin c → Finset Nat),
    ∀ i < n, ∀ j < m,
      let hits := ((Finset.univ : Finset (Fin c)).filter (fun h => i ∈ P h ∧ j ∈ N h)).card
      (i*m+j ∈ E → t ≤ hits) ∧ (i*m+j ∉ E → hits=0)
  (∀ i, A i ⊆ B i ∧ B i ⊆ Finset.range r) ∧
  (∀ i j X, A i ⊆ X → X ⊆ B i → A j ⊆ X → X ⊆ B j → i=j) ∧
  ∀ w a f, let t := a+f+1
    width w a f ↔ k*t ≤ w ∧ rect (w-k*t) t) := by
  intro n m E _ s u k' r' tag' common' A' B' width' rect'
  have tg off d j : tag' off d j=tag off d j := by
    ext x
    simp only [tag',tag,Finset.mem_insert,Finset.mem_image,Finset.mem_filter]
  have cm j : common' j=common n m j := by
    by_cases l : j<n <;> by_cases h : j<n+m <;> simp only [common',common,l,h,ite_true,ite_false,tg]
    all_goals first | rfl | (ext x; simp only [Finset.mem_union]; rfl)
  have al i : A' i=A n m i := by
    ext x
    by_cases l : i.val<n <;> simp only [A',A,cm,l,ite_true,ite_false,Finset.mem_insert]
  have bl i : B' i=B n m E i := by
    ext x
    by_cases h : n ≤ i.val ∧ i.val<n+m <;> simp only [B',B,cm,h,true_and,ite_true,ite_false,Finset.mem_union,Finset.mem_filter]
  have wi w a f : width' w a f ↔ Width (A n m) (B n m E) (r n m) w a f := by
    simp only [width',Width,al,bl,sameDiff]
    rfl
  have re c t : rect' c t ↔ Rect n m E c t := by
    simp only [rect',Rect,hits,sameFilter]
  simp only [al,bl,wi,re]
  exact ⟨inside E,uniqueBox E,fun w a f => ⟨lower E,fun h => upper E h.1 h.2⟩⟩
