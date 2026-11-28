import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1438_aux
abbrev q (n m : ℕ) := n+m+10
abbrev t (n m : ℕ) := q n m*q n m
abbrev u (n m : ℕ) := t n m*n
abbrev z (n m : ℕ) := u n m+n+2*q n m
abbrev r (n m : ℕ) := z n m+m+2*q n m+1
abbrev Stage (n m : ℕ) := Fin (u n m+t n m*m)
def tag3 (base dim q j : ℕ) := ({base+j % dim,base+dim+(j/dim)/q,base+dim+q+(j/dim) % q} : Finset ℕ)
def Ltag (n m j : ℕ) := tag3 (u n m) n (q n m) j
def Rtag (n m j : ℕ) := Finset.Ico (u n m) (z n m) ∪ insert (r n m-1) (tag3 (z n m) m (q n m) j)
def addr (n m : ℕ) (i : Stage n m) := if i.val<u n m then Ltag n m i.val else Rtag n m (i.val-u n m)
def A (n m : ℕ) (i : Stage n m) := if i.val<u n m then insert i.val (addr n m i) else addr n m i
def B (n m : ℕ) (E : Finset ℕ) (i : Stage n m) := if i.val<u n m then Finset.range (u n m) ∪ addr n m i else
  addr n m i ∪ (Finset.range (u n m)).filter (fun x => x/n ≠ (i.val-u n m)/m ∨ (x % n)*m+(i.val-u n m) % m∉E)
theorem digitBounds {dim q j : ℕ} (h : j<q*q*dim) :
    j % dim<dim ∧ j/dim/q<q ∧ j/dim % q<q := by
  have d : 0<dim := by
    by_contra! e
    rw [show dim=0 by omega] at h
    simp at h
  have p : 0<q := by
    by_contra! e
    rw [show q=0 by omega] at h
    simp at h
  have dlt := (Nat.div_lt_iff_lt_mul d).mpr h
  exact ⟨Nat.mod_lt _ d,(Nat.div_lt_iff_lt_mul p).mpr dlt,Nat.mod_lt _ p⟩
theorem tagRange {base dim q i x : ℕ} (hi : i<q*q*dim) (mem : x∈tag3 base dim q i) :
    base ≤ x ∧ x<base+dim+2*q := by
  have h := digitBounds hi
  simp only [tag3,Finset.mem_insert,Finset.mem_singleton] at mem
  rcases mem with rfl|rfl|rfl <;> constructor <;> first | omega | exact Nat.le_add_right .. | exact Nat.le_trans (Nat.le_add_right ..) (Nat.le_add_right ..) | exact Nat.le_trans (Nat.le_trans (Nat.le_add_right ..) (Nat.le_add_right ..)) (Nat.le_add_right ..)
theorem tagInj {base dim q i j : ℕ} (hi : i<q*q*dim) (hj : j<q*q*dim)
    (sub : tag3 base dim q i ⊆ tag3 base dim q j) : i=j := by
  have hx := digitBounds hi
  have hy := digitBounds hj
  have h1 := sub (show base+i % dim∈tag3 base dim q i by simp [tag3])
  have h2 := sub (show base+dim+i/dim/q∈tag3 base dim q i by simp [tag3])
  have h3 := sub (show base+dim+q+i/dim % q∈tag3 base dim q i by simp [tag3])
  simp only [tag3,Finset.mem_insert,Finset.mem_singleton] at h1 h2 h3
  generalize hix : i % dim = ii at h1 h2 h3 hx
  generalize hiy : i/dim/q = ij at h1 h2 h3 hx
  generalize hiz : i/dim % q = ik at h1 h2 h3 hx
  generalize hjx : j % dim = ji at h1 h2 h3 hy
  generalize hjy : j/dim/q = jj at h1 h2 h3 hy
  generalize hjz : j/dim % q = jk at h1 h2 h3 hy
  have lo : i % dim=j % dim := by rw [hix,hjx]; omega
  have md : i/dim % q=j/dim % q := by rw [hiz,hjz]; omega
  have top : i/dim/q=j/dim/q := by rw [hiy,hjy]; omega
  have decomp (a b : ℕ) : a = a % b+b*(a/b) := (Nat.mod_add_div a b).symm
  have quo : i/dim=j/dim := by calc
    _ = _ := decomp _ q
    _ = _ := by rw [md,top]
    _ = _ := (decomp _ q).symm
  calc
    _ = _ := decomp _ dim
    _ = _ := by rw [lo,quo]
    _ = _ := (decomp _ dim).symm

theorem large {n m : ℕ} (i : Stage n m) (x) (h : x∈addr n m i) : u n m ≤ x ∧ x<r n m := by
  have si := i.isLt
  by_cases left : i.val<u n m
  · have hx : x∈Ltag n m i.val := by simpa [addr,left] using h
    have hh := tagRange left hx
    dsimp [r,z]; omega
  · have idx : i.val-u n m<t n m*m := by omega
    simp only [addr,left,ite_false,Rtag,Finset.mem_union,Finset.mem_insert] at h
    rcases h with a|rfl|a
    · have hh := Finset.mem_Ico.mp a; dsimp [r,z] at *; omega
    · dsimp [r,z]; omega
    · have hh := tagRange idx a
      dsimp [r,z] at *; omega
theorem addrLo {n m : ℕ} (i : Stage n m) : addr n m i ⊆ A n m i := by
  unfold A; split
  · exact Finset.subset_insert ..
  · exact fun _ h => h
theorem thru {n m : ℕ} {E : Finset ℕ} {x : ℕ} {i : Stage n m} (hi : x∈B n m E i) (hx : u n m ≤ x) : x∈addr n m i := by
  unfold B at hi; split at hi
  · exact (Finset.mem_union.mp hi).resolve_left (fun y => hx.not_gt (Finset.mem_range.mp y))
  · exact (Finset.mem_union.mp hi).resolve_right (fun y => hx.not_gt (Finset.mem_range.mp (Finset.mem_filter.mp y).1))
theorem inside (n m : ℕ) (E : Finset ℕ) (i : Stage n m) : A n m i ⊆ B n m E i ∧ B n m E i ⊆ Finset.range (r n m) := by
  constructor
  · by_cases l : i.val<u n m <;> simp only [A,B,l,ite_true,ite_false]
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl|h
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr l)
      · exact Finset.mem_union_right _ h
    · exact Finset.subset_union_left
  · intro x hx
    by_cases small : x<u n m
    · exact Finset.mem_range.mpr (by dsimp [r,z]; omega)
    · exact Finset.mem_range.mpr (large i x (thru hx (by omega))).2
end PEqualNP.Outside.L_lib_1438_aux

namespace PEqualNP.Outside.L_lib_1438_aux
theorem injectAddr (n m : ℕ) (i j : Stage n m) (eq : addr n m i=addr n m j) : i=j := by
  have si := i.isLt
  have sj := j.isLt
  have last (k : Stage n m) : r n m-1∈addr n m k ↔ ¬ k.val<u n m := by
    by_cases l : k.val<u n m
    · simp only [addr,l,ite_true,not_true_eq_false,iff_false]
      intro mem
      have hh := (tagRange l mem).2
      dsimp [r,z] at hh; omega
    · simp [addr,Rtag,l]
  have side : i.val<u n m ↔ j.val<u n m := by
    have e : r n m-1∈addr n m i ↔ r n m-1∈addr n m j := by rw [eq]
    rw [last,last] at e
    tauto
  by_cases li : i.val<u n m
  · have lj := side.mp li
    simp only [addr,li,lj,ite_true] at eq
    exact Fin.ext (tagInj li lj eq.subset)
  · have lj : ¬ j.val<u n m := fun h => li (side.mpr h)
    have vi : i.val-u n m<t n m*m := by omega
    have vj : j.val-u n m<t n m*m := by omega
    simp only [addr,li,lj,ite_false] at eq
    have sub : tag3 (z n m) m (q n m) (i.val-u n m) ⊆ tag3 (z n m) m (q n m) (j.val-u n m) := by
      intro x hx
      have bounds := tagRange vi hx
      have mem : x∈Rtag n m (i.val-u n m) := Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
      rw [eq] at mem
      rcases Finset.mem_union.mp mem with left|right
      · have hh := (Finset.mem_Ico.mp left).2; omega
      · rcases Finset.mem_insert.mp right with rfl|yes
        · dsimp [r] at bounds; omega
        · exact yes
    have same := tagInj vi vj sub
    exact Fin.ext (by omega)
theorem uniqueBox (n m : ℕ) (E : Finset ℕ) (i j : Stage n m) (X : Finset ℕ)
    (il : A n m i ⊆ X) (ih : X ⊆ B n m E i) (jl : A n m j ⊆ X) (jh : X ⊆ B n m E j) : i=j := by
  have incl {i j : Stage n m} (sub : A n m i ⊆ B n m E j) : addr n m i ⊆ addr n m j :=
    fun x h => thru (sub (addrLo i h)) (large i x h).1
  exact injectAddr n m i j (Finset.Subset.antisymm (incl (il.trans jh)) (incl (jl.trans ih)))

def leftStage (c : Fin (t n m)) (i : Fin n) : Stage n m :=
  ⟨c.val*n+i.val,by
    have b := Nat.mul_le_mul_right n (Nat.succ_le_of_lt c.isLt)
    rw [Nat.succ_mul] at b
    have ii := i.isLt
    change _ < t n m*n+_
    omega⟩
def rightStage (c : Fin (t n m)) (j : Fin m) : Stage n m :=
  ⟨u n m+c.val*m+j.val,by
    have b := Nat.mul_le_mul_right m (Nat.succ_le_of_lt c.isLt)
    rw [Nat.succ_mul] at b
    have jj := j.isLt; omega⟩
theorem leftLt (c : Fin (t n m)) (i : Fin n) : (leftStage c i).val<u n m := by
  have b := Nat.mul_le_mul_right n (Nat.succ_le_of_lt c.isLt)
  rw [Nat.succ_mul] at b
  have ii := i.isLt
  change c.val*n+i.val<t n m*n
  omega
theorem edge (E : Finset ℕ) (c c' : Fin (t n m)) (i : Fin n) (j : Fin m) :
    A n m (leftStage c i) ⊆ B n m E (rightStage c' j) ↔ c≠c' ∨ i.val*m+j.val∉E := by
  have left := leftLt c i
  have right : ¬(rightStage c' j).val<u n m := by dsimp [rightStage]; omega
  have dl : (c.val*n+i.val)/n=c.val := by rw [Nat.mul_comm,Nat.mul_add_div (by have := i.isLt; omega),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have dr : (c'.val*m+j.val)/m=c'.val := by rw [Nat.mul_comm,Nat.mul_add_div (by have := j.isLt; omega),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have ml : (c.val*n+i.val)%n=i.val := by simp [Nat.mod_eq_of_lt i.isLt]
  have mr : (c'.val*m+j.val)%m=j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  have lo : (rightStage c' j).val-u n m=c'.val*m+j.val := by dsimp [rightStage]; omega
  have tags : addr n m (leftStage c i) ⊆ addr n m (rightStage c' j) := by
    simp only [addr,left,right,ite_true,ite_false]
    intro x h
    exact Finset.mem_union_left _ (Finset.mem_Ico.mpr (tagRange left h))
  have never : (leftStage c i).val∉addr n m (rightStage c' j) := fun h => left.not_ge (large _ _ h).1
  simp only [A,left,B,right,ite_true,ite_false,Finset.insert_subset_iff]
  have target : (leftStage c i).val∈addr n m (rightStage c' j) ∪
    (Finset.range (u n m)).filter (fun x => x/n ≠ ((rightStage c' j).val-u n m)/m ∨ x%n*m+((rightStage c' j).val-u n m)%m∉E) ↔ c≠c' ∨ i.val*m+j.val∉E := by
    simp only [Finset.mem_union,never,false_or,Finset.mem_filter,Finset.mem_range,left,true_and,lo]
    change ((c.val*n+i.val)/n ≠ _ ∨ (c.val*n+i.val)%n*m+_∉E) ↔ _
    rw [dl,dr,ml,mr]
    exact or_congr (not_congr Fin.val_injective.eq_iff) Iff.rfl
  exact ⟨fun h => target.mp h.1,fun h => ⟨target.mpr h,tags.trans Finset.subset_union_left⟩⟩
end PEqualNP.Outside.L_lib_1438_aux

namespace PEqualNP.Outside.L_lib_1438_aux
def Rect (n m : ℕ) (E : Finset ℕ) (k : ℕ) := ∃P N : Fin k → Finset ℕ,∀ i < n, ∀ j < m,
  i*m+j∈E ↔ ∃h,i∈P h ∧ j∈N h
def Width (n m : ℕ) (E : Finset ℕ) (w : ℕ) := ∃g h : Finset ℕ → Finset ℕ,Monotone g ∧ Monotone h ∧
  (∀X ⊆ Finset.range (r n m),g X ⊆ Finset.range w) ∧ (∀Y ⊆ Finset.range w,h Y ⊆ Finset.range (r n m)) ∧
  ∀i X,A n m i ⊆ X → X ⊆ B n m E i → A n m i ⊆ h (g X) ∧ h (g X) ⊆ B n m E i
theorem buildWidth (E : Finset ℕ) (w : ℕ) (S : ℕ → Finset ℕ → Prop)
    (up : ∀ b X Y,X ⊆ Y → S b X → S b Y)
    (sep : ∀i j,¬ A n m i ⊆ B n m E j → ∃b<w,S b (A n m i) ∧ ¬ S b (B n m E j)) : Width n m E w := by
  classical
  let g (X : Finset ℕ) := (Finset.range w).filter (fun b => S b X)
  let inds (Y : Finset ℕ) := Finset.univ.filter (fun i : Stage n m => g (A n m i) ⊆ Y)
  let h (Y : Finset ℕ) := (inds Y).biUnion (A n m)
  have gm : Monotone g := by
    intro X Y xy b hb
    obtain ⟨lt,yes⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨lt,up b X Y xy yes⟩
  have hm : Monotone h := by
    intro X Y xy x hx
    obtain ⟨i,ii,mem⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ii).2.trans xy⟩,mem⟩
  refine ⟨g,h,gm,hm,fun _ _ => Finset.filter_subset ..,?_,?_⟩
  · rintro Y _ x hx
    obtain ⟨i,_,mem⟩ := Finset.mem_biUnion.mp hx
    exact (inside n m E i).2 ((inside n m E i).1 mem)
  · intro i X ax xb
    refine ⟨fun x hx => Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,gm ax⟩,hx⟩,?_⟩
    intro x hx
    obtain ⟨j,ok,mem⟩ := Finset.mem_biUnion.mp hx
    have sub := (Finset.mem_filter.mp ok).2.trans (gm xb)
    by_contra miss
    obtain ⟨b,lt,yes,no⟩ := sep j i (fun inc => miss (inc mem))
    exact no (Finset.mem_filter.mp (sub (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr lt,yes⟩))).2

def Sig (n m k : ℕ) (P : Fin k → Finset ℕ) (b : ℕ) (X : Finset ℕ) : Prop :=
  (∃x∈X,u n m ≤ x ∧ b=t n m*k+(x-u n m)) ∨
  ∃c : Fin (t n m),∃h : Fin k,b=c.val*k+h.val ∧ ∃x∈X,x<u n m ∧ x/n=c.val ∧ x%n∈P h
theorem digitLt (c : Fin t') (h : Fin k) : c.val*k+h.val<t'*k := by
  have hh := h.isLt
  have b := Nat.mul_le_mul_right k c.isLt
  rw [Nat.succ_mul] at b; omega
theorem digitUnique (c c' : ℕ) (h h' : Fin k) (eq : c*k+h.val=c'*k+h'.val) : c=c' ∧ h=h' := by
  have pos : 0<k := by have := h.isLt; omega
  have quo (x : ℕ) (y : Fin k) : (x*k+y.val)/k=x := by rw [Nat.mul_comm,Nat.mul_add_div pos,Nat.div_eq_of_lt y.isLt,Nat.add_zero]
  have same := congrArg (fun x => x/k) eq
  change (c*k+h.val)/k=(c'*k+h'.val)/k at same
  rw [quo,quo] at same
  exact ⟨same,Fin.ext (by simpa [same] using eq)⟩

theorem upper (E : Finset ℕ) (rec : Rect n m E k) : Width n m E (t n m*k+n+m+4*q n m+1) := by
  classical
  obtain ⟨P,N,rep⟩ := rec
  apply buildWidth E _ (Sig n m k P)
  · rintro b X Y sub (⟨x,hx,lt,eq⟩|⟨c,h,eq,x,hx,small,copy,yes⟩)
    · exact Or.inl ⟨x,sub hx,lt,eq⟩
    · exact Or.inr ⟨c,h,eq,x,sub hx,small,copy,yes⟩
  · intro i j conflict
    obtain ⟨x,ax,miss⟩ := Finset.not_subset.mp conflict
    have range := Finset.mem_range.mp ((inside n m E i).2 ((inside n m E i).1 ax))
    by_cases high : u n m ≤ x
    · refine ⟨t n m*k+(x-u n m),by dsimp [r,z] at range; omega,Or.inl ⟨x,ax,high,rfl⟩,?_⟩
      rintro (⟨y,yb,hy,eq⟩|⟨c,h,eq,_⟩)
      · have : y=x := by omega
        exact miss (this ▸ yb)
      · have lt := digitLt c h; omega
    · have small : x<u n m := by omega
      have xi : x=i.val ∧ i.val<u n m := by
        unfold A at ax; split at ax
        · rename_i li
          rcases Finset.mem_insert.mp ax with eq|tag
          · exact ⟨eq,li⟩
          · exact False.elim (high (large _ _ tag).1)
        · exact False.elim (high (large _ _ ax).1)
      have right : ¬j.val<u n m := by
        intro lj
        exact miss (by unfold B; rw [if_pos lj]; exact Finset.mem_union_left _ (Finset.mem_range.mpr small))
      have allowed (y) (ys : y<u n m) : y∈B n m E j ↔ y/n ≠ (j.val-u n m)/m ∨ y%n*m+(j.val-u n m)%m∉E := by
        unfold B
        rw [if_neg right]
        have mt : y∉addr n m j := fun h => ys.not_ge (large _ _ h).1
        simp [mt,ys]
      have neg := mt (allowed x small).mpr miss
      push_neg at neg
      have npos : 0<n := by
        by_contra! h
        have hz : n=0 := Nat.eq_zero_of_le_zero h
        simp [u,hz] at small
      have js := j.isLt
      have jr : j.val-u n m<t n m*m := by omega
      have mpos : 0 < m := by
        by_contra! h
        have hz : m=0 := Nat.eq_zero_of_le_zero h
        simp [hz] at jr
      obtain ⟨h,px,nj⟩ := (rep _ (Nat.mod_lt _ npos) _ (Nat.mod_lt _ mpos)).mp neg.2
      let c : Fin (t n m) := ⟨x/n,(Nat.div_lt_iff_lt_mul npos).mpr small⟩
      refine ⟨c.val*k+h.val,by have := digitLt c h; omega,Or.inr ⟨c,h,rfl,x,ax,small,rfl,px⟩,?_⟩
      rintro (⟨v,_,_,eq⟩|⟨d,h',eq,y,yb,ys,cy,py⟩)
      · have := digitLt c h; omega
      · obtain ⟨cd,hh⟩ := digitUnique _ _ h h' eq
        subst h'
        have sameCopy : y/n=(j.val-u n m)/m := cy.trans (cd.symm.trans neg.1)
        have hasEdge :=  (rep _ (Nat.mod_lt _ npos) _ (Nat.mod_lt _ mpos)).mpr ⟨h,py,nj⟩
        exact ((allowed y ys).mp yb).elim (fun h => h sameCopy) (fun h => h hasEdge)
end PEqualNP.Outside.L_lib_1438_aux

namespace PEqualNP.Outside.L_lib_1438_aux
theorem cheapCopy (t k : ℕ) (pos : 0<t) (K : Fin t → Finset ℕ) (range : ∀c,K c ⊆ Finset.range k)
    (disj : ∀c d,c≠d → Disjoint (K c) (K d)) : ∃c,(K c).card ≤ k/t := by
  classical
  have pair : (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint K := fun c _ d _ cd => disj c d cd
  have allbits : Finset.univ.biUnion K ⊆ Finset.range k := by
    intro b hb
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hb
    exact range c hc
  have cap : ∑ c,(K c).card ≤ k := by
    simpa only [Finset.card_biUnion pair,Finset.card_range] using Finset.card_le_card allbits
  by_contra! large
  have floor : t*(k/t+1) ≤ ∑ c,(K c).card := by
    simpa using (Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ : Fin t => k/t+1) (g:=fun c => (K c).card)
      (fun c _ => large c))
  exact (Nat.lt_succ_self (k/t)).not_ge ((Nat.le_div_iff_mul_le pos).mpr (by simpa [Nat.mul_comm] using floor.trans cap))

theorem lower (E : Finset ℕ) (fit : Width n m E k) : Rect n m E (k/t n m) := by
  classical
  obtain ⟨g,h,gm,hm,gcap,_,fit⟩ := fit
  have reflects (i j : Stage n m) :
      g (A n m i) ⊆ g (B n m E j) ↔ A n m i ⊆ B n m E j := by
    constructor
    · intro maps
      have li := (fit i (A n m i) (fun _ hx => hx) (inside _ _ E i).1).1
      have uj := (fit j (B n m E j) (inside _ _ E j).1 (fun _ hx => hx)).2
      exact li.trans ((hm maps).trans uj)
    · exact fun sub => gm sub
  let L (c : Fin (t n m)) (i : Fin n) := g (A n m (leftStage c i))
  let R (c : Fin (t n m)) (j : Fin m) := g (B n m E (rightStage c j))
  have maps (c d) (i : Fin n) (j : Fin m) : L c i ⊆ R d j ↔ c≠d ∨ i.val*m+j.val∉E :=
    (reflects ..).trans (edge E c d i j)
  let K (c : Fin (t n m)) := (Finset.range k).filter (fun b => (∃i,b∈L c i) ∧ ∃j,b∉R c j)
  obtain ⟨c,cheap⟩ := cheapCopy (t n m) k (by dsimp [t,q]; positivity) K
    (fun _ => Finset.filter_subset ..) (by
      intro c d ne
      apply Finset.disjoint_left.mpr
      intro b bc bd
      obtain ⟨i,li⟩ := (Finset.mem_filter.mp bc).2.1
      obtain ⟨j,rj⟩ := (Finset.mem_filter.mp bd).2.2
      exact rj (((maps c d i j).mpr (Or.inl ne)) li))
  let V := K c
  let pick (i : Fin V.card) := ((V.orderIsoOfFin rfl) i).val
  let P (b : Fin (k/t n m)) := if hb : b.val<V.card then
    (Finset.range n).filter (fun i => ∃hi : i<n,pick ⟨b.val,hb⟩∈L c ⟨i,hi⟩) else ∅
  let N (b : Fin (k/t n m)) := if hb : b.val<V.card then
    (Finset.range m).filter (fun j => ∃hj : j < m,pick ⟨b.val,hb⟩∉R c ⟨j,hj⟩) else ∅
  refine ⟨P,N,?_⟩
  intro i hi j hj
  let I : Fin n := ⟨i,hi⟩
  let J : Fin m := ⟨j,hj⟩
  constructor
  · intro hit
    have miss : ¬L c I ⊆ R c J := fun sub => ((maps c c I J).mp sub).elim (fun h => h rfl) (fun h => h hit)
    obtain ⟨b,yes,no⟩ := Finset.not_subset.mp miss
    have cap := gcap _ ((inside _ _ E (leftStage c I)).1.trans (inside _ _ E (leftStage c I)).2)
    have bV : b∈V := Finset.mem_filter.mpr ⟨cap yes,⟨I,yes⟩,J,no⟩
    let o := (V.orderIsoOfFin rfl).symm ⟨b,bV⟩
    have ev : pick o=b := congrArg Subtype.val ((V.orderIsoOfFin rfl).apply_symm_apply ⟨b,bV⟩)
    refine ⟨⟨o.val,o.isLt.trans_le cheap⟩,?_,?_⟩
    · dsimp only [P]; rw [dif_pos o.isLt]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hi,ev.symm ▸ yes⟩
    · dsimp only [N]; rw [dif_pos o.isLt]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hj,ev.symm ▸ no⟩
  · rintro ⟨b,yes,no⟩
    by_contra nonedge
    have sub := (maps c c I J).mpr (Or.inr nonedge)
    by_cases h : b.val<V.card
    · dsimp only [P,N] at yes no
      rw [dif_pos h] at yes no
      obtain ⟨_,left⟩ := (Finset.mem_filter.mp yes).2
      obtain ⟨_,right⟩ := (Finset.mem_filter.mp no).2
      exact right (sub left)
    · simpa [P,h] using yes
end PEqualNP.Outside.L_lib_1438_aux

namespace PEqualNP.Outside.L_lib_1438_aux
theorem widthMono (E : Finset ℕ) (le : b ≤ c) (work : Width n m E b) : Width n m E c := by
  obtain ⟨g,h,gm,hm,gb,hb,ok⟩ := work
  let trim (Y : Finset ℕ) := Y∩Finset.range b
  refine ⟨g,fun Y => h (trim Y),gm,fun _ _ incl => hm (Finset.inter_subset_inter_right incl),
    fun X xs => (gb X xs).trans (Finset.range_mono le),fun Y _ => hb (trim Y) Finset.inter_subset_right,?_⟩
  intro i X low high
  have sub := gb X (high.trans (inside n m E i).2)
  simpa only [trim,Finset.inter_eq_left.mpr sub] using ok i X low high
theorem paddedBudget (T k h : ℕ) (small : h<T) : T*k+h ≤ T*(k+1)-1 ∧ (T*(k+1)-1)/T=k := by
  have positive : 0<T := by omega
  have base : T*(k+1) = T*k+T := Nat.mul_succ T k
  constructor
  · rw [base]; omega
  · apply Nat.div_eq_of_lt_le
    · have ordered : k*T=T*k := Nat.mul_comm .. 
      omega
    · have ordered : (k+1)*T=T*(k+1) := Nat.mul_comm ..
      omega

theorem exactWidth (n m : ℕ) (E : Finset ℕ) (k : ℕ) : Rect n m E k ↔ Width n m E (t n m*(k+1)-1) := by
  have small : n+m+4*q n m+1<t n m := by dsimp [t,q]; nlinarith [Nat.zero_le ((n+m)*(n+m))]
  obtain ⟨pad,div⟩ := paddedBudget (t n m) k (n+m+4*q n m+1) small
  constructor
  · intro rec
    exact widthMono E (by simpa only [Nat.add_assoc] using pad) (upper E rec)
  · intro fit
    simpa only [div] using lower E fit
end PEqualNP.Outside.L_lib_1438_aux

open PEqualNP.Outside.L_lib_1438_aux in
theorem PEqualNP.Outside.L_lib_1438 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n m : Nat) (E : Finset Nat), E ⊆ Finset.range (n*m) →
  let q := n+m+10
  let t := q*q
  let u := t*n
  let z := u+n+2*q
  let r := z+m+2*q+1
  let tagL := fun j : Nat => ({u+j % n,u+n+(j/n)/q,u+n+q+(j/n) % q} : Finset Nat)
  let tagR := fun j : Nat => (Finset.Ico u z) ∪ ({z+j % m,z+m+(j/m)/q,z+m+q+(j/m) % q,r-1} : Finset Nat)
  let A := fun (s : Fin (u+t*m)) => if s.val<u then insert s.val (tagL s.val) else tagR (s.val-u)
  let B := fun (s : Fin (u+t*m)) => if s.val<u then Finset.range u ∪ tagL s.val else
    let j := s.val-u
    tagR j ∪ (Finset.range u).filter (fun i => i/n ≠ j/m ∨ (i % n)*m+j % m ∉ E)
  let width := fun (k : Nat) => ∃ (g h : Finset Nat → Finset Nat), Monotone g ∧ Monotone h ∧
    (∀ X ⊆ Finset.range r, g X ⊆ Finset.range k) ∧ (∀ Y ⊆ Finset.range k, h Y ⊆ Finset.range r) ∧
    ∀ i X, A i ⊆ X → X ⊆ B i → A i ⊆ h (g X) ∧ h (g X) ⊆ B i
  let rect := fun k : Nat => ∃ (P N : Fin k → Finset Nat),
    ∀ i < n, ∀ j < m, i*m+j ∈ E ↔ ∃ h, i ∈ P h ∧ j ∈ N h
  (∀ i, A i ⊆ B i ∧ B i ⊆ Finset.range r) ∧
  (∀ i j X, A i ⊆ X → X ⊆ B i → A j ⊆ X → X ⊆ B j → i=j) ∧
  (∀ k, rect k → width (t*k+n+m+4*q+1)) ∧ (∀ k, width k → rect (k/t)) ∧
  ∀ k, rect k ↔ width (t*(k+1)-1)) := by
  intro n m E _ q' t' u' z' r' tagL tagR A' B' width' rect'
  have tagsL j : tagL j=Ltag n m j := by
    ext x
    simp only [tagL,Ltag,tag3,Finset.mem_insert,Finset.mem_singleton,q',u',t']
  have tagsR j : tagR j=Rtag n m j := by
    ext x
    simp only [tagR,Rtag,tag3,Finset.mem_union,Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton,r',z',u',t',q']
    unfold r z u t q
    tauto
  have lo (i) : A' i=A n m i := by
    by_cases l : i.val<u n m
    · ext x
      simp only [A',A,addr,show i.val<u' from l,l,ite_true,Finset.mem_insert,tagsL]
    · simpa only [A',A,addr,show ¬i.val<u' from l,l,ite_false] using tagsR (i.val-u')
  have hi (i) : B' i=B n m E i := by
    ext x
    by_cases l : i.val<u n m
    · simp only [B',B,addr,show i.val<u' from l,l,ite_true,Finset.mem_union,tagsL]
      rfl
    · simp only [B',B,addr,show ¬i.val<u' from l,l,ite_false,Finset.mem_union,tagsR,Finset.mem_filter]
      rfl
  simp only [width',rect',lo,hi]
  exact ⟨inside n m E,uniqueBox n m E,fun _ => upper E,fun _ => lower E,exactWidth n m E⟩
