import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_957.FL957
def Exact (old : Nat) {ι : Type} (endp : ι → Nat × Nat) (A : Finset ι) : Prop :=
  ∀ n : Fin old, ∃! j : ι, j ∈ A ∧ ((endp j).1 = n.val ∨ (endp j).2 = n.val)
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
abbrev Idx (c : List (Nat × Nat)) := Fin c.length
abbrev K (o : Nat) (c : List (Nat × Nat)) := o + 2*c.length
abbrev Lft (c : List (Nat × Nat)) (j : Idx c) := (c.get j).1
abbrev Rgt (c : List (Nat × Nat)) (j : Idx c) := (c.get j).2
abbrev B (o : Nat) {c : List (Nat × Nat)} (j : Idx c) := o+2*j.val
def Good (o : Nat) (c : List (Nat × Nat)) := ∀ j : Idx c, Lft c j < Rgt c j ∧ Rgt c j < o
def Joins (x y a b : Nat) := (x = a ∧ y = b) ∨ (x = b ∧ y = a)
def Raw (o : Nat) (c : List (Nat × Nat)) (x y : Nat) := ∃ j : Idx c, Joins x y (Lft c j) (B o j) ∨ Joins x y (B o j) (B o j+1) ∨ Joins x y (Rgt c j) (B o j+1)
def Mate (o : Nat) (c : List (Nat × Nat)) (A : Finset (Idx c)) (x y : Nat) := ∃ j : Idx c, (j ∈ A ∧ (Joins x y (Lft c j) (B o j) ∨ Joins x y (Rgt c j) (B o j+1))) ∨ (j ∉ A ∧ Joins x y (B o j) (B o j+1))
def active (o : Nat) (c : List (Nat × Nat)) (P : Equiv.Perm (Fin (K o c))) := Finset.univ.filter fun j : Idx c => (P ⟨B o j, by have := j.isLt; unfold B K; omega⟩).val = Lft c j
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
variable {o : Nat} {c : List (Nat × Nat)}
def pathEdges (o : Nat) (c : List (Nat × Nat)) := c.zipIdx.flatMap (fun z => let b := o+2*z.2
  [(z.1.1,b),(b,b+1),(z.1.2,b+1)])
def Perfect (o : Nat) (c : List (Nat × Nat)) (P : Equiv.Perm (Fin (K o c))) := Function.Involutive P ∧
    ∀ i : Fin (K o c), P i ≠ i ∧ (min i.val (P i).val,max i.val (P i).val) ∈ pathEdges o c

theorem joins_minmax {x y a b : Nat} (hab : a ≤ b) : Joins x y a b ↔ (min x y, max x y) = (a,b) := by
  unfold Joins
  rcases le_total x y with h | h
  · simp only [min_eq_left h, max_eq_right h, Prod.mk.injEq]; omega
  · simp only [min_eq_right h, max_eq_left h, Prod.mk.injEq]; omega

theorem zip_mem_fin (j : Idx c) : (c.get j,j.val) ∈ c.zipIdx := by
  rw [List.mk_mem_zipIdx_iff_getElem?]; simp

theorem raw_iff_mem (g : Good o c) (x y : Nat) : Raw o c x y ↔ (min x y,max x y) ∈ pathEdges o c := by
  unfold Raw pathEdges
  simp only [List.mem_flatMap, List.mem_cons]
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨(c.get j,j.val),zip_mem_fin j,?_⟩
    obtain ⟨h1,h2⟩ := g j
    change (_,_) = (Lft c j,B o j) ∨ (_,_) = (B o j,B o j+1) ∨ (_,_) = (Rgt c j,B o j+1) ∨ _
    unfold B at *
    rcases hj with h|h|h
    · exact Or.inl ((joins_minmax (by omega)).mp h)
    · exact Or.inr (Or.inl ((joins_minmax (by omega)).mp h))
    · exact Or.inr (Or.inr (Or.inl ((joins_minmax (by omega)).mp h)))
  · rintro ⟨⟨u,i⟩,hu,h⟩
    obtain ⟨hi,he⟩ := List.mem_zipIdx' hu
    rw [he] at h
    let j : Idx c := ⟨i,hi⟩
    refine ⟨j,?_⟩
    obtain ⟨h1,h2⟩ := g j
    change (_,_) = (Lft c j,B o j) ∨ (_,_) = (B o j,B o j+1) ∨ (_,_) = (Rgt c j,B o j+1) ∨ _ at h
    unfold B at *
    rcases h with h|h|h|h
    · exact Or.inl ((joins_minmax (by omega)).mpr h)
    · exact Or.inr (Or.inl ((joins_minmax (by omega)).mpr h))
    · exact Or.inr (Or.inr ((joins_minmax (by omega)).mpr h))
    · simp at h

theorem raw_ne (g : Good o c) {x y : Nat} (h : Raw o c x y) : x ≠ y := by
  obtain ⟨j,h⟩ := h
  obtain ⟨h1,h2⟩ := g j
  simp only [Joins,B] at h; omega

theorem active_iff_first (P : Equiv.Perm (Fin (K o c))) (hi : Function.Involutive P) (j : Idx c) :
    j ∈ active o c P ↔ ∃ i : Fin (K o c), i.val = Lft c j ∧ (P i).val = B o j := by
  let b : Fin (K o c) := ⟨B o j,by have := j.isLt; unfold B K; omega⟩
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  change (P b).val = _ ↔ _
  constructor
  · intro h
    exact ⟨P b,h,by rw [hi]⟩
  · rintro ⟨i,hi₁,hi₂⟩
    have : P i = b := Fin.ext hi₂
    rw [← this,hi,hi₁]

theorem exists_zip_active (P : Equiv.Perm (Fin (K o c))) (hi : Function.Involutive P) (u v : Nat) :
    (∃ z ∈ c.zipIdx, z.1 = (u,v) ∧ ∃ i : Fin (K o c), i.val = u ∧ (P i).val = o+2*z.2) ↔
      ∃ j ∈ active o c P, c.get j = (u,v) := by
  constructor
  · rintro ⟨⟨pair,n⟩,hm,he,i,hi₁,hi₂⟩
    obtain ⟨hn,he'⟩ := List.mem_zipIdx' hm
    let j : Idx c := ⟨n,hn⟩
    have eq : c.get j = (u,v) := he'.symm.trans he
    exact ⟨j,(active_iff_first P hi j).mpr ⟨i, hi₁.trans (congrArg Prod.fst eq).symm, hi₂⟩,eq⟩
  · rintro ⟨j,hm,he⟩
    obtain ⟨i,hi₁,hi₂⟩ := (active_iff_first P hi j).mp hm
    exact ⟨(c.get j,j.val),zip_mem_fin j,he,i,hi₁.trans (congrArg Prod.fst he),hi₂⟩
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957

private theorem fw_side {o c} (g : Good o c) (j : Idx c) (d y : Nat) (hd : d ≤ 1)
    (h : Raw o c (B o j + d) y) :
    (d = 0 ∧ (y = Lft c j ∨ y = B o j+1)) ∨
    (d = 1 ∧ (y = Rgt c j ∨ y = B o j)) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨hl,hr⟩ := g k
  unfold Joins at hk
  unfold B at *
  rcases hk with (⟨e,t⟩|⟨e,t⟩)|(⟨e,t⟩|⟨e,t⟩)|(⟨e,t⟩|⟨e,t⟩) <;>
    first | omega | (have ej : j = k := Fin.ext (by omega); subst k; omega)

theorem forward {o : Nat} {c : List (Nat × Nat)} (g : Good o c)
    (P : Equiv.Perm (Fin (K o c))) (hi : Function.Involutive P)
    (h : ∀ x, Raw o c x.val (P x).val) :
    Exact o (fun j : Idx c => c.get j) (active o c P) ∧
    ∀ x, Mate o c (active o c P) x.val (P x).val := by
  classical
  let f (n : Nat) := if hn : n < K o c then (P ⟨n,hn⟩).val else n
  have fp (x : Fin (K o c)) : f x.val = (P x).val := by simp [f, x.isLt]
  have sym (x : Fin (K o c)) : f (P x).val = x.val := by rw [fp, hi x]
  have sym' (n : Nat) (hn : n < K o c) : f (f n) = n := by
    let x : Fin (K o c) := ⟨n,hn⟩
    change f (f x.val) = x.val
    rw [fp, sym]
  have raw (n : Nat) (hn : n < K o c) : Raw o c n (f n) := by
    let x : Fin (K o c) := ⟨n, hn⟩
    change Raw o c x.val (f x.val)
    rw [fp]; exact h x
  have bnd (j : Idx c) : B o j+1 < K o c := by have := j.isLt; unfold B K; omega
  have am (j : Idx c) : j ∈ active o c P ↔ f (B o j) = Lft c j := by
    simp [active, f, show B o j < K o c by have := bnd j; omega]
  have right (j : Idx c) : j ∈ active o c P ↔ f (B o j+1) = Rgt c j := by
    have hb := bnd j
    have hb' : B o j < K o c := by omega
    have h0 := fw_side g j 0 (f (B o j)) (by decide) (by simpa using raw _ hb')
    have h1 := fw_side g j 1 (f (B o j+1)) (by decide) (raw _ hb)
    obtain ⟨hl,hr⟩ := g j
    have hle : o ≤ B o j := by unfold B; omega
    rw [am]
    constructor
    · intro ha
      by_contra hn
      have he : f (B o j+1) = B o j := by omega
      have hs := sym' _ hb
      rw [he,ha] at hs; omega
    · intro ha
      by_contra hn
      have he : f (B o j) = B o j+1 := by omega
      have hs := sym' _ hb'
      rw [he,ha] at hs; omega
  have joined (x : Fin (K o c)) {a b : Nat} (hh : Joins x.val (P x).val a b) : f a = b ∧ f b = a := by
    rcases hh with ⟨ha,hb⟩|⟨ha,hb⟩ <;> rw [← ha, ← hb] <;> first | exact ⟨fp x, sym x⟩ | exact ⟨sym x, fp x⟩
  have hm (x : Fin (K o c)) : Mate o c (active o c P) x.val (P x).val := by
    obtain ⟨j,hj|hj|hj⟩ := h x
    · exact ⟨j, Or.inl ⟨(am j).2 (joined x hj).2, Or.inl hj⟩⟩
    · refine ⟨j, Or.inr ⟨?_,hj⟩⟩
      intro ha
      have he := (joined x hj).1
      have hl := (am j).1 ha
      have := g j; unfold B at he hl; omega
    · exact ⟨j, Or.inl ⟨(right j).2 (joined x hj).2, Or.inr hj⟩⟩
  refine ⟨?_,hm⟩
  intro n
  have hn := n.isLt
  let x : Fin (K o c) := ⟨n.val, by unfold K; omega⟩
  have ex : ∃ j : Idx c, j ∈ active o c P ∧ (Lft c j = n.val ∨ Rgt c j = n.val) := by
    obtain ⟨j,hj⟩ := hm x
    have hn' : x.val < o := hn
    have hb : o ≤ B o j := by unfold B; omega
    rcases hj with ⟨ha,hp|hp⟩|⟨_,hp⟩ <;>
      rcases hp with ⟨he,_⟩|⟨he,_⟩ <;> first | omega | exact ⟨j,ha,Or.inl he.symm⟩ | exact ⟨j,ha,Or.inr he.symm⟩
  obtain ⟨j,hj,ej⟩ := ex
  refine ⟨j,⟨hj,ej⟩,?_⟩
  have tag (i : Idx c) (ha : i ∈ active o c P) (he : Lft c i = n.val ∨ Rgt c i = n.val) :
      f n.val = B o i ∨ f n.val = B o i+1 := by
    have hb := bnd i
    rcases he with he|he
    · left; have hh := sym' (B o i) (by omega); rwa [(am i).1 ha, he] at hh
    · right; have hh := sym' _ hb; rwa [(right i).1 ha, he] at hh
  intro k hk
  have ht := tag j hj ej
  have hu := tag k hk.1 hk.2
  unfold B at ht hu; apply Fin.ext; omega
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957

theorem mate_unique {o c} (g : Good o c) (A : Finset (Idx c))
    (hA : Exact o (fun j : Idx c => c.get j) A) (x : Fin (K o c)) :
    ∃! y : Fin (K o c), Mate o c A x.val y.val := by
  classical
  let E (j : Idx c) (y : Nat) :=
    (j ∈ A ∧ (Joins x.val y (Lft c j) (B o j) ∨ Joins x.val y (Rgt c j) (B o j+1))) ∨
    (j ∉ A ∧ Joins x.val y (B o j) (B o j+1))
  have uniq (j k : Idx c) (y z : Nat) (hj : E j y) (hk : E k z) : y = z := by
    have hjk : j = k := by
      by_cases ho : x.val < o
      · have classify (i : Idx c) (w : Nat) (hi : E i w) :
            i ∈ A ∧ (Lft c i = x.val ∨ Rgt c i = x.val) := by
          dsimp only [E, Joins, B] at hi
          rcases hi with ⟨h, (⟨e,f⟩ | ⟨e,f⟩) | (⟨e,f⟩ | ⟨e,f⟩)⟩ | ⟨h, ⟨e,f⟩ | ⟨e,f⟩⟩ <;>
            first | exact ⟨h, Or.inl e.symm⟩ | exact ⟨h, Or.inr e.symm⟩ | omega
        obtain ⟨i, _, hi⟩ := hA ⟨x.val, ho⟩
        exact (hi j (classify j y hj)).trans (hi k (classify k z hk)).symm
      · have classify (i : Idx c) (w : Nat) (hi : E i w) :
            x.val = o+2*i.val ∨ x.val = o+2*i.val+1 := by
          have ⟨hl,hr⟩ := g i
          dsimp only [E, Joins, B] at hi
          rcases hi with ⟨h, (⟨e,f⟩ | ⟨e,f⟩) | (⟨e,f⟩ | ⟨e,f⟩)⟩ | ⟨h, ⟨e,f⟩ | ⟨e,f⟩⟩ <;> omega
        have := classify j y hj
        have := classify k z hk
        apply Fin.ext
        omega
    subst k
    have ⟨hl,hr⟩ := g j
    dsimp only [E, Joins, B] at hj hk
    rcases hj with ⟨h, (⟨_,_⟩ | ⟨_,_⟩) | (⟨_,_⟩ | ⟨_,_⟩)⟩ | ⟨h, ⟨_,_⟩ | ⟨_,_⟩⟩ <;>
      rcases hk with ⟨h', (⟨_,_⟩ | ⟨_,_⟩) | (⟨_,_⟩ | ⟨_,_⟩)⟩ | ⟨h', ⟨_,_⟩ | ⟨_,_⟩⟩ <;>
      first | contradiction | omega
  suffices h : ∃ y : Fin (K o c), Mate o c A x.val y.val by
    obtain ⟨y,hy⟩ := h
    refine ⟨y, hy, ?_⟩
    rintro z ⟨j,hj⟩
    obtain ⟨k,hk⟩ := hy
    exact Fin.ext (uniq j k z.val y.val hj hk)
  have bound (j : Idx c) : B o j + 1 < K o c := by
    have := j.isLt
    dsimp [B,K]; omega
  by_cases ho : x.val < o
  · obtain ⟨j,⟨hj,e | e⟩,_⟩ := hA ⟨x.val, ho⟩
    · exact ⟨⟨B o j, Nat.lt_trans (Nat.lt_succ_self _) (bound j)⟩, j, Or.inl ⟨hj, Or.inl (Or.inl ⟨e.symm,rfl⟩)⟩⟩
    · exact ⟨⟨B o j+1, bound j⟩, j, Or.inl ⟨hj, Or.inr (Or.inl ⟨e.symm,rfl⟩)⟩⟩
  · have hx := x.isLt
    dsimp only [K] at hx
    let j : Idx c := ⟨(x.val-o)/2, by omega⟩
    have casesX : x.val = B o j ∨ x.val = B o j+1 := by dsimp [B,j]; omega
    have ⟨hl,hr⟩ := g j
    by_cases hj : j ∈ A
    · rcases casesX with e | e
      · exact ⟨⟨Lft c j, by dsimp only [K]; omega⟩, j, Or.inl ⟨hj, Or.inl (Or.inr ⟨e,rfl⟩)⟩⟩
      · exact ⟨⟨Rgt c j, by dsimp only [K]; omega⟩, j, Or.inl ⟨hj, Or.inr (Or.inr ⟨e,rfl⟩)⟩⟩
    · rcases casesX with e | e
      · exact ⟨⟨B o j+1, bound j⟩, j, Or.inr ⟨hj, Or.inl ⟨e,rfl⟩⟩⟩
      · exact ⟨⟨B o j, Nat.lt_trans (Nat.lt_succ_self _) (bound j)⟩, j, Or.inr ⟨hj, Or.inr ⟨e,rfl⟩⟩⟩

end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
variable {o : Nat} {c : List (Nat × Nat)}
private theorem joins_symm {x y a b : Nat} (h : Joins x y a b) : Joins y x a b := by
  unfold Joins at *; tauto
private theorem mate_symm {A : Finset (Idx c)} {x y : Nat} (h : Mate o c A x y) : Mate o c A y x := by
  obtain ⟨j,h⟩ := h
  exact ⟨j,by rcases h with ⟨ha,hl|hr⟩|⟨ha,hc⟩
              · exact Or.inl ⟨ha,Or.inl (joins_symm hl)⟩
              · exact Or.inl ⟨ha,Or.inr (joins_symm hr)⟩
              · exact Or.inr ⟨ha,joins_symm hc⟩⟩
private theorem mate_raw {A : Finset (Idx c)} {x y : Nat} (h : Mate o c A x y) : Raw o c x y := by
  obtain ⟨j,h⟩ := h
  exact ⟨j,by tauto⟩

section
variable (g : Good o c)
private noncomputable def matePerm (A : Finset (Idx c)) (hA : Exact o (fun j : Idx c => c.get j) A) :
    {P : Equiv.Perm (Fin (K o c)) // Perfect o c P ∧ ∀ x, Mate o c A x.val (P x).val} := by
  classical
  let f (x : Fin (K o c)) := (mate_unique g A hA x).exists.choose
  have hf (x : Fin (K o c)) : Mate o c A x.val (f x).val := (mate_unique g A hA x).exists.choose_spec
  have hi : Function.Involutive f := fun x => (mate_unique g A hA (f x)).unique (hf (f x)) (mate_symm (hf x))
  let P : Equiv.Perm (Fin (K o c)) := ⟨f,f,hi,hi⟩
  refine ⟨P,⟨hi,fun x => ?_⟩,hf⟩
  have h := mate_raw (hf x)
  exact ⟨fun he => raw_ne g h (congrArg Fin.val he.symm),(raw_iff_mem g _ _).mp h⟩

include g in
private theorem active_eq_of_mates (A : Finset (Idx c)) (hA : Exact o (fun j : Idx c => c.get j) A)
    (P : Equiv.Perm (Fin (K o c))) (hm : ∀ x, Mate o c A x.val (P x).val) : active o c P = A := by
  classical
  ext j
  obtain ⟨hl,hr⟩ := g j
  have hj := j.isLt
  let b : Fin (K o c) := ⟨B o j,by unfold K B; omega⟩
  simp only [active,Finset.mem_filter,Finset.mem_univ,true_and]
  change (P b).val = Lft c j ↔ _
  by_cases ha : j ∈ A
  · let l : Fin (K o c) := ⟨Lft c j, by unfold K; omega⟩
    have h : Mate o c A b.val l.val := ⟨j,Or.inl ⟨ha,Or.inl (Or.inr ⟨rfl,rfl⟩)⟩⟩
    exact iff_of_true (congrArg Fin.val ((mate_unique g A hA b).unique (hm b) h)) ha
  · let r : Fin (K o c) := ⟨B o j+1,by unfold K B; omega⟩
    have h : Mate o c A b.val r.val := ⟨j,Or.inr ⟨ha,Or.inl ⟨rfl,rfl⟩⟩⟩
    have he : (P b).val = B o j+1 := congrArg Fin.val ((mate_unique g A hA b).unique (hm b) h)
    unfold B at he
    exact iff_of_false (by omega) ha

noncomputable def pathEquiv : {P // Perfect o c P} ≃
    {A // Exact o (fun j : Idx c => c.get j) A} := by
  let fw (P : {P // Perfect o c P}) := forward g P.val P.2.1 (fun x => (raw_iff_mem g _ _).mpr (P.2.2 x).2)
  refine { toFun := fun P => ⟨_,(fw P).1⟩
           invFun := fun A => ⟨_,(matePerm g A.val A.2).2.1⟩
           left_inv := ?_
           right_inv := ?_ }
  · intro P
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (mate_unique g _ (fw P).1 x).unique ((matePerm g _ (fw P).1).2.2 x) ((fw P).2 x)
  · intro A
    apply Subtype.ext
    exact active_eq_of_mates g A.val A.2 _ (matePerm g _ A.2).2.2
end
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
variable {o : Nat} {c : List (Nat × Nat)}
@[simp] theorem pathEquiv_apply_val (g : Good o c) (P : {P // Perfect o c P}) :
    ((pathEquiv g) P).val = active o c P.val := rfl

noncomputable def pathFiberEquiv (g : Good o c)
    (p : Equiv.Perm (Fin (K o c)) → Prop) (q : Finset (Idx c) → Prop)
    (h : ∀ P, Perfect o c P → (p P ↔ q (active o c P))) :
    {P // Perfect o c P ∧ p P} ≃ {A // Exact o (fun j : Idx c => c.get j) A ∧ q A} := by
  let E := pathEquiv g
  let splitP : {P // Perfect o c P ∧ p P} ≃ {P : {P // Perfect o c P} // p P.val} :=
    ⟨fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩,fun x => ⟨x.1.1,x.1.2,x.2⟩,fun _ => rfl,fun _ => rfl⟩
  let splitA : {A // Exact o (fun j : Idx c => c.get j) A ∧ q A} ≃
      {A : {A // Exact o (fun j : Idx c => c.get j) A} // q A.val} :=
    ⟨fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩,fun x => ⟨x.1.1,x.1.2,x.2⟩,fun _ => rfl,fun _ => rfl⟩
  exact (splitP.trans (E.subtypeEquiv (fun x => h x.val x.2))).trans splitA.symm
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957
def oldPair {v : Nat} (z : Fin v × Fin v) : Nat × Nat := (z.1.val,z.2.val)
def dPair {v t : Nat} (i : Fin v) (d : Fin t) : Nat × Nat := (i.val,v+d.val)
def dv {v : Nat} (z : Fin v × Fin v) : Finset (Fin v) := {z.1,z.2}
def remain {v : Nat} (S : Finset (Fin v × Fin v)) := Finset.univ \ S.biUnion dv
def DSep {v : Nat} (S : Finset (Fin v × Fin v)) : Prop := ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint (dv e) (dv g)
def DummyFiber (v t : Nat) (S : Finset (Fin v × Fin v)) := {Y : Finset (Nat × Nat) // Exact (v+t) id Y ∧ (∀ z : Fin v × Fin v, oldPair z ∈ Y ↔ z ∈ S) ∧ ∀ p ∈ Y, (∃ z ∈ S, oldPair z = p) ∨ ∃ i : Fin v, ∃ d : Fin t, dPair i d = p}
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
variable {v t : Nat} {S : Finset (Fin v × Fin v)}
private theorem dCollide (Y : DummyFiber v t S) (n : Fin (v+t)) {p q : Nat × Nat}
    (hp : p ∈ Y.val) (hq : q ∈ Y.val) (hi : p.1 = n.val ∨ p.2 = n.val)
    (hj : q.1 = n.val ∨ q.2 = n.val) : p = q := by
  obtain ⟨u, _, hu⟩ := Y.property.1 n
  exact (hu p ⟨hp,hi⟩).trans (hu q ⟨hq,hj⟩).symm
private theorem dvHit {i : Fin v} {z : Fin v × Fin v} (hi : i ∈ dv z) :
    (oldPair z).1 = i.val ∨ (oldPair z).2 = i.val := by
  simp [dv] at hi
  rcases hi with h|h <;> subst i <;> simp [oldPair]
private theorem oldInj : Function.Injective (@oldPair v) := by
  intro a b h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
theorem dummySep (Y : DummyFiber v t S) : DSep S := by
  intro e he g hg hn
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hn (oldInj (dCollide Y ⟨i.val, by omega⟩ ((Y.property.2.1 _).mpr he)
    ((Y.property.2.1 _).mpr hg) (dvHit hi) (dvHit hj)))
private theorem dInRemain (Y : DummyFiber v t S) {i : Fin v} {d : Fin t}
    (hd : dPair i d ∈ Y.val) : i ∈ remain S := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hi
  obtain ⟨e, he, hi⟩ := Finset.mem_biUnion.mp hi
  have hh := dCollide Y ⟨i.val, by omega⟩ hd ((Y.property.2.1 _).mpr he) (Or.inl rfl) (dvHit hi)
  have hh' : v+d.val = e.2.val := congrArg Prod.snd hh
  omega
private theorem dTotal (Y : DummyFiber v t S) (i : ↥(remain S)) :
    ∃ d : Fin t, dPair i.val d ∈ Y.val := by
  obtain ⟨p, ⟨hp, hi⟩, _⟩ := Y.property.1 ⟨i.val.val, by have := i.val.isLt; omega⟩
  change p.1 = i.val.val ∨ p.2 = i.val.val at hi
  rcases Y.property.2.2 p hp with ⟨z,hz,rfl⟩|⟨k,d,rfl⟩
  · exfalso
    apply (Finset.mem_sdiff.mp i.property).2 (Finset.mem_biUnion.mpr ⟨z,hz,?_⟩)
    change z.1.val = i.val.val ∨ z.2.val = i.val.val at hi
    simp only [dv, Finset.mem_insert, Finset.mem_singleton]
    rcases hi with h|h
    · exact Or.inl (Fin.ext h.symm)
    · exact Or.inr (Fin.ext h.symm)
  · change k.val = i.val.val ∨ v+d.val = i.val.val at hi
    have h : k = i.val := Fin.ext (by have := i.val.isLt; omega)
    exact ⟨d, h ▸ hp⟩
private theorem dOnto (Y : DummyFiber v t S) (d : Fin t) :
    ∃ i : ↥(remain S), dPair i.val d ∈ Y.val := by
  obtain ⟨p, ⟨hp, hi⟩, _⟩ := Y.property.1 ⟨v+d.val, by omega⟩
  change p.1 = v+d.val ∨ p.2 = v+d.val at hi
  rcases Y.property.2.2 p hp with ⟨z,hz,rfl⟩|⟨k,c,rfl⟩
  · change z.1.val = v+d.val ∨ z.2.val = v+d.val at hi
    omega
  · change k.val = v+d.val ∨ v+c.val = v+d.val at hi
    have h : c = d := Fin.ext (by omega)
    subst c
    exact ⟨⟨k,dInRemain Y hp⟩,hp⟩
private noncomputable def dRead (Y : DummyFiber v t S) (i : ↥(remain S)) : Fin t :=
  (dTotal Y i).choose
private theorem dRead_spec (Y : DummyFiber v t S) (i : ↥(remain S)) (d : Fin t) :
    dRead Y i = d ↔ dPair i.val d ∈ Y.val := by
  constructor
  · rintro rfl
    exact (dTotal Y i).choose_spec
  · intro hd
    have he := dCollide Y ⟨i.val.val, by have := i.val.isLt; omega⟩ (dTotal Y i).choose_spec hd
      (Or.inl rfl) (Or.inl rfl)
    have hh : v+(dRead Y i).val = v+d.val := congrArg Prod.snd he
    exact Fin.ext (by omega)
noncomputable def dummyRead (Y : DummyFiber v t S) : ↥(remain S) ≃ Fin t := by
  apply Equiv.ofBijective (dRead Y)
  constructor
  · intro i j hij
    have he := dCollide Y ⟨v+(dRead Y j).val, by omega⟩ ((dRead_spec Y i _).mp hij)
      ((dRead_spec Y j _).mp rfl) (Or.inr rfl) (Or.inr rfl)
    exact Subtype.ext (Fin.ext (congrArg Prod.fst he))
  · intro d
    obtain ⟨i, hi⟩ := dOnto Y d
    exact ⟨i,(dRead_spec Y i d).mpr hi⟩
theorem dummyRead_mem (Y : DummyFiber v t S) (i : ↥(remain S)) (d : Fin t) :
    dummyRead Y i = d ↔ dPair i.val d ∈ Y.val := dRead_spec Y i d
theorem dummyRead_injective : Function.Injective (@dummyRead v t S) := by
  intro Y Z he
  have incl (Y Z : DummyFiber v t S) (h : dummyRead Y = dummyRead Z) : Y.val ⊆ Z.val := by
    intro p hp
    rcases Y.property.2.2 p hp with ⟨e,he,rfl⟩|⟨i,d,rfl⟩
    · exact (Z.property.2.1 e).mpr he
    · let k : ↥(remain S) := ⟨i,dInRemain Y hp⟩
      apply (dummyRead_mem Z k d).mp
      rw [← h]
      exact (dummyRead_mem Y k d).mpr hp
  exact Subtype.ext (Finset.Subset.antisymm (incl Y Z he) (incl Z Y he.symm))
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
private theorem db_dv {v} (i : Fin v) (z : Fin v × Fin v) :
    i ∈ dv z ↔ z.1.val = i.val ∨ z.2.val = i.val := by
  simp [dv, Fin.ext_iff, eq_comm]

private theorem db_away {v} {S : Finset (Fin v × Fin v)} (i : ↥(remain S))
    {z : Fin v × Fin v} (hz : z ∈ S) : i.val ∉ dv z := by
  exact fun hi => (Finset.mem_sdiff.mp i.property).2 (Finset.mem_biUnion.mpr ⟨z,hz,hi⟩)

noncomputable def dummyBuild {v t : Nat} {S : Finset (Fin v × Fin v)} (h : DSep S)
    (f : ↥(remain S) ≃ Fin t) : DummyFiber v t S := by
  classical
  let A := S.image oldPair ∪ Finset.univ.image (fun i : ↥(remain S) => dPair i.val (f i))
  have mem (p) : p ∈ A ↔ (∃ z ∈ S, oldPair z = p) ∨ ∃ i : ↥(remain S), dPair i.val (f i) = p := by
    simp [A]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n.val < v
    · let i : Fin v := ⟨n.val,hn⟩
      by_cases hm : i ∈ S.biUnion dv
      · obtain ⟨e,he,hie⟩ := Finset.mem_biUnion.mp hm
        refine ⟨oldPair e, ⟨(mem _).2 (.inl ⟨e,he,rfl⟩), (db_dv i e).1 hie⟩, ?_⟩
        rintro p ⟨hp,hl⟩
        rcases (mem p).1 hp with ⟨z,hz,rfl⟩ | ⟨k,rfl⟩
        · have hiz := (db_dv i z).2 hl
          by_cases hze : z = e
          · rw [hze]
          · exact False.elim ((Finset.disjoint_left.mp (h z hz e he hze)) hiz hie)
        · change k.val.val = n.val ∨ v + (f k).val = n.val at hl
          have hki : k.val = i := Fin.ext (by change k.val.val = n.val; omega)
          exact False.elim (db_away k he (hki ▸ hie))
      · let k : ↥(remain S) := ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hm⟩⟩
        refine ⟨dPair k.val (f k), ⟨(mem _).2 (.inr ⟨k,rfl⟩), Or.inl rfl⟩, ?_⟩
        rintro p ⟨hp,hl⟩
        rcases (mem p).1 hp with ⟨z,hz,rfl⟩ | ⟨l,rfl⟩
        · exact False.elim (hm (Finset.mem_biUnion.mpr ⟨z,hz,(db_dv i z).2 hl⟩))
        · change l.val.val = n.val ∨ v + (f l).val = n.val at hl
          have hlk : l = k := Subtype.ext (Fin.ext (by change l.val.val = n.val; omega))
          rw [hlk]
    · let d : Fin t := ⟨n.val-v,by have := n.isLt; omega⟩
      let k := f.symm d
      have hkd : f k = d := f.apply_symm_apply d
      have hnv : v + d.val = n.val := by dsimp [d]; omega
      refine ⟨dPair k.val (f k), ⟨(mem _).2 (.inr ⟨k,rfl⟩), Or.inr (hkd ▸ hnv)⟩, ?_⟩
      rintro p ⟨hp,hl⟩
      rcases (mem p).1 hp with ⟨z,hz,rfl⟩ | ⟨l,rfl⟩
      · change z.1.val = n.val ∨ z.2.val = n.val at hl
        have := z.1.isLt; have := z.2.isLt; omega
      · change l.val.val = n.val ∨ v + (f l).val = n.val at hl
        have := l.val.isLt
        have hlk : l = k := f.injective (hkd ▸ Fin.ext (by omega))
        rw [hlk]
  · intro z
    constructor
    · intro hp
      rcases (mem _).1 hp with ⟨e,he,hep⟩ | ⟨l,hl⟩
      · have hez : e = z := Prod.ext (Fin.ext (congrArg Prod.fst hep)) (Fin.ext (congrArg Prod.snd hep))
        exact hez ▸ he
      · have hl' : v+(f l).val = z.2.val := congrArg Prod.snd hl
        have := z.2.isLt; omega
    · exact fun hz => (mem _).2 (.inl ⟨z,hz,rfl⟩)
  · intro p hp
    rcases (mem _).1 hp with hz | ⟨l,rfl⟩
    · exact Or.inl hz
    · exact Or.inr ⟨l.val, f l, rfl⟩

theorem dummyBuild_mem {v t : Nat} {S : Finset (Fin v × Fin v)} (h : DSep S)
    (f : ↥(remain S) ≃ Fin t) (i : ↥(remain S)) (d : Fin t) :
    dPair i.val d ∈ (dummyBuild h f).val ↔ f i = d := by
  classical
  change _ ∈ S.image oldPair ∪ Finset.univ.image (fun l : ↥(remain S) => dPair l.val (f l)) ↔ _
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨z,hz,he⟩ | ⟨l,he⟩)
    · have hh : z.2.val = v+d.val := congrArg Prod.snd he
      have := z.2.isLt; omega
    · have hli : l = i := Subtype.ext (Fin.ext (congrArg Prod.fst he))
      have hh : v + (f l).val = v+d.val := congrArg Prod.snd he
      rw [hli] at hh
      exact Fin.ext (by omega)
  · rintro rfl
    exact .inr ⟨i,rfl⟩
end PEqualNP.Outside.L_lib_957.FL957
namespace PEqualNP.Outside.L_lib_957.FL957
noncomputable def dummyEquiv {v t : Nat} {S : Finset (Fin v × Fin v)} (h : DSep S) :
    DummyFiber v t S ≃ (↥(remain S) ≃ Fin t) := by
  have inv (f : ↥(remain S) ≃ Fin t) : dummyRead (dummyBuild h f) = f := by
    apply Equiv.ext
    intro i
    exact (dummyRead_mem _ i _).mpr ((dummyBuild_mem h f i _).mpr rfl)
  exact ⟨dummyRead, dummyBuild h, fun Y => dummyRead_injective (inv _), inv⟩
instance dummyFiberFinite {v t : Nat} {S : Finset (Fin v × Fin v)} : Finite (DummyFiber v t S) :=
  Finite.of_injective dummyRead dummyRead_injective

theorem dummyBuild_read {v t : Nat} {S : Finset (Fin v × Fin v)} (Y : DummyFiber v t S) :
    dummyBuild (dummySep Y) (dummyRead Y) = Y := (dummyEquiv (dummySep Y)).left_inv Y
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957
open scoped Classical

theorem remain_add_twice {v : Nat} {S : Finset (Fin v × Fin v)}
    (hs : ∀ z ∈ S, z.1 < z.2) (hd : DSep S) : (remain S).card + 2*S.card = v := by
  have hp : (↑S : Set (Fin v × Fin v)).PairwiseDisjoint dv := hd
  have hu : (S.biUnion dv).card = 2*S.card := by
    rw [Finset.card_biUnion hp]
    calc
      ∑ z ∈ S, (dv z).card = ∑ _z ∈ S, 2 := Finset.sum_congr rfl fun z hz => Finset.card_pair (ne_of_lt (hs z hz))
      _ = _ := by simp [Nat.mul_comm]
  have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S.biUnion dv))
  simpa only [remain, hu, Finset.card_univ, Fintype.card_fin] using hh

theorem dummyCard {v r : Nat} (hle : 2*r ≤ v) {S : Finset (Fin v × Fin v)}
    (hs : ∀ z ∈ S, z.1 < z.2) : Nat.card (DummyFiber v (v-2*r) S) =
      if S.card = r ∧ DSep S then (v-2*r).factorial else 0 := by
  classical
  by_cases h : S.card = r ∧ DSep S
  · rw [ite_eq_left h, Nat.card_congr (dummyEquiv h.2), Nat.card_eq_fintype_card]
    have ha := remain_add_twice hs h.2
    have hc : Fintype.card ↥(remain S) = v-2*r := by rw [Fintype.card_coe]; omega
    have e : ↥(remain S) ≃ Fin (v-2*r) := Fintype.equivOfCardEq (by simpa using hc)
    rw [Fintype.card_equiv e, hc]
  · rw [ite_eq_right h]
    have : IsEmpty (DummyFiber v (v-2*r) S) := ⟨fun Y => by
      have hd := dummySep Y
      have ha := remain_add_twice hs hd
      have hc := Fintype.card_congr (dummyEquiv hd Y)
      simp only [Fintype.card_coe, Fintype.card_fin] at hc
      exact h ⟨by omega,hd⟩⟩
    exact Nat.card_of_isEmpty
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957
open scoped BigOperators

section
variable {I B : Type} [DecidableEq I] [DecidableEq B]

noncomputable def liftEquiv (f : I → B) (Y : Finset B) :
    (∀ y : Y, {i : I // f i = y.val}) ≃
      {A : Finset I // Set.InjOn f (↑A : Set I) ∧ A.image f = Y} := by
  classical
  let L (g : ∀ y : Y, {i : I // f i = y.val}) : Finset I :=
    Finset.univ.image (fun y : Y => (g y).val)
  have hm (g : ∀ y : Y, {i : I // f i = y.val}) (i : I) :
      i ∈ L g ↔ ∃ y : Y, (g y).val = i := by simp [L]
  have hL (g : ∀ y : Y, {i : I // f i = y.val}) :
      Set.InjOn f (↑(L g) : Set I) ∧ (L g).image f = Y := by
    constructor
    · intro i hi j hj hij
      obtain ⟨y, rfl⟩ := (hm g i).mp hi
      obtain ⟨z, rfl⟩ := (hm g j).mp hj
      have hyz : y = z := Subtype.ext ((g y).property.symm.trans (hij.trans (g z).property))
      cases hyz
      rfl
    · ext b
      constructor
      · intro hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨y, rfl⟩ := (hm g i).mp hi
        rw [(g y).property]
        exact y.property
      · intro hb
        let y : Y := ⟨b,hb⟩
        exact Finset.mem_image.mpr ⟨(g y).val, (hm g _).mpr ⟨y,rfl⟩, (g y).property⟩
  let F (g : ∀ y : Y, {i : I // f i = y.val}) :=
    (⟨L g,hL g⟩ : {A : Finset I // Set.InjOn f (↑A : Set I) ∧ A.image f = Y})
  apply Equiv.ofBijective F
  constructor
  · intro g h heq
    have he : L g = L h := congrArg Subtype.val heq
    funext y
    apply Subtype.ext
    have hh := (hm g _).mpr ⟨y,rfl⟩
    rw [he] at hh
    obtain ⟨z,hz⟩ := (hm h _).mp hh
    have hzy : z = y := Subtype.ext ((h z).property.symm.trans ((congrArg f hz).trans (g y).property))
    cases hzy
    exact hz.symm
  · rintro ⟨A, hinj, hY⟩
    have hpre (y : Y) : ∃ i ∈ A, f i = y.val := by
      apply Finset.mem_image.mp
      rw [hY]
      exact y.property
    choose s hs hs' using hpre
    let g (y : Y) : {i : I // f i = y.val} := ⟨s y, hs' y⟩
    refine ⟨g, Subtype.ext ?_⟩
    change L g = A
    ext i
    rw [hm]
    constructor
    · rintro ⟨y,rfl⟩
      exact hs y
    · intro hi
      have hy : f i ∈ Y := hY ▸ Finset.mem_image_of_mem f hi
      let y : Y := ⟨f i,hy⟩
      exact ⟨y, hinj (hs y) hi (hs' y)⟩

theorem card_lift (f : I → B) (Y : Finset B) :
    Nat.card {A : Finset I // Set.InjOn f (↑A : Set I) ∧ A.image f = Y} =
      ∏ y ∈ Y, Nat.card {i : I // f i = y} := by
  classical
  rw [← Nat.card_congr (liftEquiv f Y), Nat.card_pi]
  exact Finset.prod_coe_sort Y (fun y => Nat.card {i : I // f i = y})
end

section
variable {I : Type}

theorem exact_image_iff (old : Nat) (f : I → Nat × Nat) (A : Finset I)
    (hb : ∀ i, (f i).1 < old) :
    Exact old f A ↔ Exact old id (A.image f) ∧ Set.InjOn f (↑A : Set I) := by
  classical
  constructor
  · intro h
    constructor
    · intro n
      obtain ⟨i,hi,hu⟩ := h n
      refine ⟨f i, ⟨Finset.mem_image_of_mem f hi.1,hi.2⟩, ?_⟩
      rintro y ⟨hy,hyn⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
      exact congrArg f (hu j ⟨hj,hyn⟩)
    · intro i hi j hj hij
      let n : Fin old := ⟨(f i).1,hb i⟩
      exact (h n).unique ⟨hi,Or.inl rfl⟩ ⟨hj,Or.inl (congrArg Prod.fst hij.symm)⟩
  · rintro ⟨h,hinj⟩ n
    obtain ⟨y,⟨hy,hyn⟩,hu⟩ := h n
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨i,⟨hi,hyn⟩,?_⟩
    rintro j ⟨hj,hjn⟩
    exact hinj hj hi (hu (f j) ⟨Finset.mem_image_of_mem f hj,hjn⟩)

theorem card_exact_image (old : Nat) (f : I → Nat × Nat) (Y : Finset (Nat × Nat))
    (hb : ∀ i, (f i).1 < old) (hY : Exact old id Y) :
    Nat.card {A : Finset I // Exact old f A ∧ A.image f = Y} =
      ∏ y ∈ Y, Nat.card {i : I // f i = y} := by
  classical
  rw [← card_lift f Y]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro A
  rw [exact_image_iff _ _ _ hb]
  constructor
  · rintro ⟨⟨_,h⟩,h'⟩
    exact ⟨h,h'⟩
  · rintro ⟨hinj, heq⟩
    exact ⟨⟨heq.symm ▸ hY, hinj⟩, heq⟩
end
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957
open Finset

theorem placementProd {v t : Nat} (S : Finset (Fin v × Fin v)) (U : Finset (Fin v))
    (h : U ≃ Fin t) (μ : Nat × Nat → Nat) (w : Fin v → Fin v → Nat) (a : Fin v → Nat)
    (hw : ∀ e ∈ S, μ (e.1.val,e.2.val) = w e.1 e.2)
    (ha : ∀ i : U, μ (i.val.val,v + (h i).val) = a i.val) :
    ((S.image (fun e => (e.1.val,e.2.val))) ∪ (U.attach.image (fun i => (i.val.val,v + (h i).val)))).prod μ =
    S.prod (fun e => w e.1 e.2) * U.prod a := by
  classical
  let f := fun e : Fin v × Fin v => (e.1.val,e.2.val)
  let g := fun i : U => (i.val.val,v + (h i).val)
  change ((S.image f) ∪ (U.attach.image g)).prod μ = _
  have disj : Disjoint (S.image f) (U.attach.image g) := by
    refine Finset.disjoint_left.mpr ?_
    intro z h1 h2
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h2
    have heq := congrArg Prod.snd eq
    change v + (h i).val = e.2.val at heq
    omega
  have injf : Function.Injective f := by
    intro e e' eq
    exact Prod.ext (Fin.ext (congrArg Prod.fst eq)) (Fin.ext (congrArg Prod.snd eq))
  have injg : Function.Injective g := by
    intro i i' eq
    exact Subtype.ext (Fin.ext (congrArg Prod.fst eq))
  rw [Finset.prod_union disj, Finset.prod_image (fun _ _ _ _ eq => injf eq), Finset.prod_image (fun _ _ _ _ eq => injg eq)]
  congr 1
  · exact Finset.prod_congr rfl hw
  · calc
      _ = U.attach.prod (fun i => a i.val) := Finset.prod_congr rfl (fun i _ => ha i)
      _ = _ := Finset.prod_attach U a
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957
universe u v

theorem card_uniform {A : Type u} {B : Type v} [Finite A] [Finite B]
    (f : A → B) (n : Nat) (hf : ∀ b, Nat.card {a // f a = b} = n) :
    Nat.card A = Nat.card B * n := by
  classical
  letI := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b, {a // f a = b}) := Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b, Nat.card {a // f a = b} := Nat.card_sigma
    _ = Nat.card B * n := by simp [hf, Nat.card_eq_fintype_card]

theorem count_by_placement {A : Type u} {B : Type v} [Finite A]
    (f : A → B) (P : A → Prop) (Q R : B → Prop) [Finite {b // R b ∧ Q b}]
    (image_ok : ∀ a, P a → Q (f a) → R (f a)) (n : Nat)
    (weight : ∀ b, R b → Q b → Nat.card {a // P a ∧ f a = b} = n) :
    Nat.card {a // P a ∧ Q (f a)} = Nat.card {b // R b ∧ Q b} * n := by
  classical
  let g : {a // P a ∧ Q (f a)} → {b // R b ∧ Q b} :=
    fun a => ⟨f a.val, image_ok _ a.property.1 a.property.2, a.property.2⟩
  apply card_uniform g
  intro b
  have e : {a // g a = b} ≃ {a // P a ∧ f a = b.val} :=
    { toFun := fun a => ⟨a.val.val, a.val.property.1, congrArg Subtype.val a.property⟩
      invFun := fun a => ⟨⟨a.val,a.property.1,(show Q (f a.val) by rw [a.property.2]; exact b.property.2)⟩,Subtype.ext a.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (weight _ b.property.1 b.property.2)
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957

def idxCells (v : Nat) := (List.finRange v).flatMap (fun i =>
  ((List.finRange v).filter (fun j => decide (i < j))).map (fun j => (i,j)))

def idxCopiesOO (v : Nat) (w : Fin v → Fin v → Nat) := (idxCells v).flatMap
  (fun z => List.replicate (w z.1 z.2) (z.1.val,z.2.val))

def idxCopiesOD (v t : Nat) (a : Fin v → Nat) :=
  (List.finRange v).flatMap (fun i => (List.range t).flatMap (fun d =>
      List.replicate (a i) (i.val,v+d)))

def idxCopies (v t : Nat) (a : Fin v → Nat) (w : Fin v → Fin v → Nat) :=
  idxCopiesOO v w ++ idxCopiesOD v t a

theorem mem_idxCells {v : Nat} {z : Fin v × Fin v} : z ∈ idxCells v ↔ z.1 < z.2 := by
  rcases z with ⟨i,j⟩
  simp [idxCells, List.mem_flatMap,List.mem_finRange]

theorem idxCells_nodup (v : Nat) : (idxCells v).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    apply List.Nodup.map (fun _ _ h => congrArg Prod.snd h)
    exact (List.nodup_finRange v).filter _
  · apply (List.nodup_finRange v).imp
    intro x y h z hx hy
    obtain ⟨u, -,rfl⟩ := List.mem_map.mp hx
    obtain ⟨w,-,hw⟩ := List.mem_map.mp hy
    exact h (congrArg Prod.fst hw).symm

theorem idxOO_ok {v} {w : Fin v → Fin v → Nat} {z} (hz : z ∈ idxCopiesOO v w) :
    z.1 < z.2 ∧ z.2 < v := by
  obtain ⟨⟨i,j⟩,hij,hz⟩ := List.mem_flatMap.mp hz
  have h := mem_idxCells.mp hij
  obtain rfl := List.eq_of_mem_replicate hz
  exact ⟨h,j.isLt⟩

theorem idxOD_ok {v t} {a : Fin v → Nat} {z} (hz : z ∈ idxCopiesOD v t a) :
    z.1 < v ∧ v ≤ z.2 ∧ z.2 < v+t := by
  obtain ⟨i, -, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨d, hd, hz⟩ := List.mem_flatMap.mp hz
  obtain rfl := List.eq_of_mem_replicate hz
  exact ⟨i.isLt,Nat.le_add_right _ _,Nat.add_lt_add_left (List.mem_range.mp hd) _⟩

theorem idxCopies_ok {v t} {a : Fin v → Nat} {w : Fin v → Fin v → Nat} {z}
    (hz : z ∈ idxCopies v t a w) : z.1 < v ∧ z.1 < z.2 ∧ z.2 < v+t := by
  rcases List.mem_append.mp hz with hz|hz
  · obtain ⟨h₁,h₂⟩ := idxOO_ok hz
    omega
  · obtain ⟨h₁,h₂,h₃⟩ := idxOD_ok hz
    omega

theorem idxCopies_kind {v t} {a : Fin v → Nat} {w : Fin v → Fin v → Nat}
    {p : Nat × Nat} (h : p ∈ idxCopies v t a w) :
    (∃ z : Fin v × Fin v, z ∈ idxCells v ∧ (z.1.val,z.2.val) = p) ∨
      (∃ i : Fin v, ∃ d : Fin t, (i.val,v+d.val) = p) := by
  rcases List.mem_append.mp h with ho | hd
  · obtain ⟨z,hz,h⟩ := List.mem_flatMap.mp ho
    exact Or.inl ⟨z,hz,(List.eq_of_mem_replicate h).symm⟩
  · obtain ⟨i, -, h⟩ := List.mem_flatMap.mp hd
    obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp h
    exact Or.inr ⟨i,⟨d,List.mem_range.mp hd⟩,(List.eq_of_mem_replicate h).symm⟩

theorem idxCopies_bounds (v t) (a : Fin v → Nat) (w : Fin v → Fin v → Nat) :
    ∀ z ∈ idxCopies v t a w, z.1 < v+t ∧ z.2 < v+t := by
  intro z hz
  obtain ⟨h₁,h₂,h₃⟩ := idxCopies_ok hz
  omega

private theorem idxFlatSingle {α β : Type} [DecidableEq β] (f : α → List β)
    (a : α) (b : β) (hf : ∀ x, b ∈ f x → x = a) (l : List α) (hn : l.Nodup) (ha : a ∈ l) :
    (l.flatMap f).count b = (f a).count b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with h|h
    · subst x
      have hz : b ∉ xs.flatMap f := by
        intro h
        obtain ⟨x,hx',hx''⟩ := List.mem_flatMap.mp h
        exact hx (hf x hx'' ▸ hx')
      simp [List.flatMap_cons,List.count_eq_zero_of_not_mem hz]
    · have hz : b ∉ f x := fun hh => hx (hf x hh ▸ h)
      simp [List.flatMap_cons,List.count_eq_zero_of_not_mem hz,ih ht h]

theorem idxCount_oo (v t : Nat) (a : Fin v → Nat) (w : Fin v → Fin v → Nat)
    (i j : Fin v) (h : i < j) : (idxCopies v t a w).count (i.val,j.val) = w i j := by
  have hz : (i.val,j.val) ∉ idxCopiesOD v t a := fun hm =>
    Nat.not_le_of_lt j.isLt (idxOD_ok hm).2.1
  simp only [idxCopies,List.count_append,List.count_eq_zero_of_not_mem hz,Nat.add_zero,idxCopiesOO]
  rw [idxFlatSingle _ (i,j) _ _ _ (idxCells_nodup _) (mem_idxCells.mpr h)]
  · simp
  · rintro ⟨i',j'⟩ h'
    have he := List.eq_of_mem_replicate h'
    exact Prod.ext (Fin.ext (congrArg Prod.fst he).symm) (Fin.ext (congrArg Prod.snd he).symm)

theorem idxCount_od (v t : Nat) (a : Fin v → Nat) (w : Fin v → Fin v → Nat)
    (i : Fin v) (d : Fin t) : (idxCopies v t a w).count (i.val,v+d.val) = a i := by
  have hz : (i.val,v+d.val) ∉ idxCopiesOO v w := by
    intro hm
    have h := (idxOO_ok hm).2
    dsimp at h
    omega
  simp only [idxCopies,List.count_append,List.count_eq_zero_of_not_mem hz,Nat.zero_add,idxCopiesOD]
  rw [idxFlatSingle _ i _ _ _ (List.nodup_finRange v) (List.mem_finRange _)]
  · rw [idxFlatSingle _ d.val _ _ _ List.nodup_range (List.mem_range.mpr d.isLt)]
    · simp
    · intro y hy
      have h := congrArg Prod.snd (List.eq_of_mem_replicate hy)
      dsimp at h
      omega
  · intro x hx
    obtain ⟨y, -, hy⟩ := List.mem_flatMap.mp hx
    exact Fin.ext (congrArg Prod.fst (List.eq_of_mem_replicate hy)).symm

theorem card_get_eq_count {α : Type} [DecidableEq α] (cs : List α) (x : α) :
    Nat.card {j : Fin cs.length // cs.get j = x} = cs.count x := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hb := Finset.sum_boole (R := ℕ) (fun j : Fin cs.length => cs.get j = x) Finset.univ
  simp only [Nat.cast_id] at hb
  rw [← hb]
  clear hb
  induction cs with
  | nil => simp
  | cons a cs ih =>
    erw [Fin.sum_univ_succ (n := cs.length) (fun j => if (a :: cs).get j = x then (1 : ℕ) else 0)]
    change (if a = x then 1 else 0) + (∑ j : Fin cs.length, if cs.get j = x then 1 else 0) = _
    rw [ih]
    by_cases h : a = x <;> simp [h, Nat.add_comm]

theorem idxCard_oo (v t : Nat) (a : Fin v → Nat) (w : Fin v → Fin v → Nat)
    (i j : Fin v) (h : i < j) :
    Nat.card {q : Fin (idxCopies v t a w).length // (idxCopies v t a w).get q = (i.val,j.val)} = w i j := by
  rw [card_get_eq_count, idxCount_oo _ _ _ _ _ _ h]

theorem idxCard_od (v t : Nat) (a : Fin v → Nat) (w : Fin v → Fin v → Nat)
    (i : Fin v) (d : Fin t) :
    Nat.card {q : Fin (idxCopies v t a w).length // (idxCopies v t a w).get q = (i.val,v+d.val)} = a i := by
  rw [card_get_eq_count, idxCount_od v t a w i d]

theorem idxCard_outside (v t : Nat) (a : Fin v → Nat) (w : Fin v → Fin v → Nat)
    (i j : Nat) (h : ¬ (i < v ∧ i < j ∧ j < v+t)) :
    Nat.card {q : Fin (idxCopies v t a w).length // (idxCopies v t a w).get q = (i,j)} = 0 := by
  rw [card_get_eq_count,List.count_eq_zero]
  exact fun hm => h (idxCopies_ok hm)

end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957

def idxPathEdges (old : Nat) (cs : List (Nat × Nat)) :=
  cs.zipIdx.flatMap (fun z => let b := old+2*z.2
    [(z.1.1,b),(b,b+1),(z.1.2,b+1)])

private def shiftedEdges (old i : Nat) (cs : List (Nat × Nat)) :=
  (cs.zipIdx i).flatMap (fun z => let b := old+2*z.2
    [(z.1.1,b),(b,b+1),(z.1.2,b+1)])

private theorem shiftedEdges_ok (old i : Nat) (cs : List (Nat × Nat))
    (h : ∀ z ∈ cs, z.1 < old ∧ z.2 < old) :
    (shiftedEdges old i cs).Nodup ∧ ∀ z ∈ shiftedEdges old i cs,
      z.1 < z.2 ∧ old+2*i ≤ z.2 ∧ z.2 < old+2*(i+cs.length) := by
  induction cs generalizing i with
  | nil => simp [shiftedEdges]
  | cons a cs ih =>
    obtain ⟨ha, hb⟩ := h a (by simp)
    obtain ⟨hn, hm⟩ := ih (i+1) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    let b := old+2*i
    change ((a.1,b) :: (b,b+1) :: (a.2,b+1) :: shiftedEdges old (i+1) cs).Nodup ∧ _
    have hnot (x y : Nat) (hy : y ≤ b+1) : (x,y) ∉ shiftedEdges old (i+1) cs := by
      intro hin
      have hh := (hm _ hin).2.1
      dsimp [b] at *
      omega
    constructor
    · simp only [List.nodup_cons, List.mem_cons, Prod.mk.injEq]
      have hab : b ≠ a.2 := by dsimp [b]; omega
      simp [hab, hnot, hn]
    · intro z hz
      change z ∈ (a.1,b) :: (b,b+1) :: (a.2,b+1) :: shiftedEdges old (i+1) cs at hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | rfl | hz
      all_goals first | (dsimp [b]; omega) | (have h' := hm z hz; simp only [List.length_cons]; omega)

theorem pathEdges_ok (old : Nat) (cs : List (Nat × Nat))
    (h : ∀ z ∈ cs, z.1 < old ∧ z.2 < old) :
    (idxPathEdges old cs).Nodup ∧ ∀ z ∈ idxPathEdges old cs, z.1 < z.2 ∧ z.2 < old+2*cs.length := by
  obtain ⟨hn, hm⟩ := shiftedEdges_ok old 0 cs h
  exact ⟨hn, fun z hz => ⟨(hm z hz).1, by simpa using (hm z hz).2.2⟩⟩

end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957

theorem copy_index {cs : List (Nat × Nat)} {p : Nat × Nat} {q : Nat} :
    (p,q) ∈ cs.zipIdx ↔ ∃ i : Fin cs.length, i.val = q ∧ cs.get i = p := by
  rw [List.mem_zipIdx_iff_getElem?]
  constructor
  · intro h
    by_cases hq : q < cs.length
    · exact ⟨⟨q,hq⟩,rfl,by simpa [List.getElem?_eq_getElem hq] using h⟩
    · simp [List.getElem?_eq_none (by omega : cs.length ≤ q)] at h
  · rintro ⟨j,rfl,rfl⟩
    simp [List.getElem?_eq_getElem j.isLt]

theorem projection_iff {v old k : Nat} (cs : List (Nat × Nat))
    (P : Equiv.Perm (Fin k)) (A : Finset (Fin cs.length))
    (active : ∀ j : Fin cs.length, j ∈ A ↔ ∃ i : Fin k,
      i.val = (cs.get j).1 ∧ (P i).val = old + 2*j.val)
    (cells S : Finset (Fin v × Fin v)) (sub : S ⊆ cells)
    (legal : ∀ (z : Fin v × Fin v) (j : Fin cs.length), cs.get j = (z.1.val,z.2.val) → z ∈ cells) :
    cells.filter (fun z => ∃ c ∈ cs.zipIdx, c.1 = (z.1.val,z.2.val) ∧
      ∃ i : Fin k, i.val = z.1.val ∧ (P i).val = old+2*c.2) = S ↔
    ∀ z : Fin v × Fin v, (z.1.val,z.2.val) ∈ A.image cs.get ↔ z ∈ S := by
  classical
  have iffAt (z : Fin v × Fin v) :
      (z ∈ cells ∧ ∃ c ∈ cs.zipIdx, c.1 = (z.1.val,z.2.val) ∧
        ∃ i : Fin k, i.val = z.1.val ∧ (P i).val = old+2*c.2) ↔
      (z.1.val,z.2.val) ∈ A.image cs.get := by
    constructor
    · rintro ⟨_,⟨p,q⟩,hc,rfl,i,hi,hpi⟩
      obtain ⟨j,rfl,hj⟩ := copy_index.mp hc
      exact Finset.mem_image.mpr ⟨j,(active j).mpr ⟨i,hi.trans (congrArg Prod.fst hj).symm,hpi⟩,hj⟩
    · intro hz
      obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hz
      obtain ⟨i,hi,pi⟩ := (active j).mp hj
      exact ⟨legal _ j eq,⟨cs.get j,j.val⟩,copy_index.mpr ⟨j,rfl,rfl⟩,eq,i,hi.trans (congrArg Prod.fst eq),pi⟩
  constructor
  · intro h z
    exact (iffAt z).symm.trans ((Finset.mem_filter (p := fun z : Fin v × Fin v => ∃ c ∈ cs.zipIdx, c.1 = (z.1.val,z.2.val) ∧ ∃ i : Fin k, i.val = z.1.val ∧ (P i).val = old+2*c.2)).symm.trans (by rw [h]))
  · intro h
    ext z
    exact Finset.mem_filter.trans ((iffAt z).trans (h z))
end PEqualNP.Outside.L_lib_957.FL957

namespace PEqualNP.Outside.L_lib_957.FL957

theorem aggregateCard (v t : Nat) (cs : List (Nat × Nat)) (S : Finset (Fin v × Fin v))
    (w : Fin v → Fin v → Nat) (a : Fin v → Nat)
    (hk : ∀ p ∈ cs, (∃ z : Fin v × Fin v, oldPair z = p) ∨ ∃ i : Fin v, ∃ d : Fin t, dPair i d = p)
    (hw : ∀ z ∈ S, Nat.card {j // cs.get j = oldPair z} = w z.1 z.2)
    (ha : ∀ (i : Fin v) (d : Fin t), Nat.card {j // cs.get j = dPair i d} = a i) :
    Nat.card {A : Finset (Fin cs.length) // Exact (v+t) cs.get A ∧
      ∀ z : Fin v × Fin v, oldPair z ∈ A.image cs.get ↔ z ∈ S} =
    Nat.card (DummyFiber v t S) * (S.prod (fun z => w z.1 z.2) * (remain S).prod a) := by
  classical
  let Q (Y : Finset (Nat × Nat)) := ∀ z : Fin v × Fin v, oldPair z ∈ Y ↔ z ∈ S
  have hb (j : Fin cs.length) : (cs.get j).1 < v+t := by
    rcases hk _ (List.get_mem cs j) with ⟨z,h⟩ | ⟨i,d,h⟩
    · rw [← h]; exact Nat.lt_of_lt_of_le z.1.isLt (Nat.le_add_right _ _)
    · rw [← h]; exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  let g : {A : Finset (Fin cs.length) // Exact (v+t) cs.get A ∧ Q (A.image cs.get)} → DummyFiber v t S :=
    fun A => ⟨A.val.image cs.get, ((exact_image_iff _ _ _ hb).mp A.property.1).1,A.property.2, by
      intro p hp
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
      rcases hk _ (List.get_mem cs j) with ⟨z,h⟩ | hd
      · exact Or.inl ⟨z,(A.property.2 z).mp (h ▸ Finset.mem_image_of_mem cs.get hj),h⟩
      · exact Or.inr hd⟩
  apply card_uniform g
  intro Y
  let e : {b // g b = Y} ≃ {A : Finset (Fin cs.length) // Exact (v+t) cs.get A ∧ A.image cs.get = Y.val} :=
    { toFun := fun b => ⟨b.val.val, b.val.property.1,congrArg Subtype.val b.property⟩
      invFun := fun A => ⟨⟨A.val,A.property.1, A.property.2.symm ▸ Y.property.2.1⟩,Subtype.ext A.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_exact_image _ _ _ hb Y.property.1]
  let μ (p : Nat × Nat) := Nat.card {j // cs.get j = p}
  change Y.val.prod μ = _
  have hh := congrArg Subtype.val (dummyBuild_read Y)
  rw [← hh]
  exact placementProd S (remain S) (dummyRead Y) μ w a hw (fun i => ha i.val _)
end PEqualNP.Outside.L_lib_957.FL957

open PEqualNP.Outside.L_lib_957.FL957 in
theorem PEqualNP.Outside.L_lib_957 : (∀ (v r : Nat), 2*r ≤ v → ∀ (a : Fin v → Nat) (w : Fin v → Fin v → Nat),
  let t := v-2*r
  let cells := (List.finRange v).flatMap (fun i =>
    ((List.finRange v).filter (fun j => decide (i < j))).map (fun j => (i,j)))
  let copies := cells.flatMap (fun z => List.replicate (w z.1 z.2) (z.1.val,z.2.val)) ++
    (List.finRange v).flatMap (fun i => (List.range t).flatMap (fun d =>
      List.replicate (a i) (i.val,v+d)))
  let old := v+t
  let k := old+2*copies.length
  let edges := copies.zipIdx.flatMap (fun z => let b := old+2*z.2
    [(z.1.1,b),(b,b+1),(z.1.2,b+1)])
  let perfect := fun P : Equiv.Perm (Fin k) => Function.Involutive P ∧
    ∀ i : Fin k, P i ≠ i ∧ (min i.val (P i).val,max i.val (P i).val) ∈ edges
  let proj := fun P : Equiv.Perm (Fin k) => cells.toFinset.filter (fun z =>
    ∃ c ∈ copies.zipIdx, c.1 = (z.1.val,z.2.val) ∧
      ∃ i : Fin k, i.val = z.1.val ∧ (P i).val = old+2*c.2)
  let verts := fun z : Fin v × Fin v => ({z.1,z.2} : Finset (Fin v))
  edges.Nodup ∧ (∀ z ∈ edges, z.1 < z.2 ∧ z.2 < k) ∧
  ∀ S ⊆ cells.toFinset, Nat.card {P : Equiv.Perm (Fin k) // perfect P ∧ proj P = S} =
    if S.card = r ∧ (∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint (verts e) (verts g)) then
      t.factorial * S.prod (fun z => w z.1 z.2) * (Finset.univ \ S.biUnion verts).prod a else 0) := by
  classical
  intro v r hle a w
  let t := v - 2*r
  let cs := idxCopies v t a w
  let o := v+t
  have good : Good o cs := by
    intro j
    exact (idxCopies_ok (List.get_mem cs j)).2
  have ed := pathEdges_ok o cs (idxCopies_bounds v t a w)
  refine ⟨ed.1,ed.2,?_⟩
  intro S hs
  have sub : S ⊆ (idxCells v).toFinset := hs
  have strict (z) (h : z ∈ S) := mem_idxCells.mp (List.mem_toFinset.mp (sub h))
  let p (P : Equiv.Perm (Fin (K o cs))) := (idxCells v).toFinset.filter (fun z =>
    ∃ c ∈ cs.zipIdx, c.1 = (z.1.val,z.2.val) ∧ ∃ i : Fin (K o cs), i.val = z.1.val ∧ (P i).val = o+2*c.2) = S
  let q (A : Finset (Idx cs)) := ∀ z : Fin v × Fin v, oldPair z ∈ A.image cs.get ↔ z ∈ S
  have bridge (P) (hp : Perfect o cs P) : p P ↔ q (active o cs P) := by
    apply projection_iff cs P _ (active_iff_first P hp.1) _ S sub
    intro z j eq
    apply List.mem_toFinset.mpr
    apply mem_idxCells.mpr
    have lt := (good j).1
    change (cs.get j).1 < (cs.get j).2 at lt
    rw [eq] at lt
    exact lt
  have countPaths := Nat.card_congr (pathFiberEquiv good p q bridge)
  have agg := aggregateCard v t cs S w a (by
    intro z hz
    rcases idxCopies_kind hz with ⟨e,_,he⟩ | hd
    · exact Or.inl ⟨e,he⟩
    · exact Or.inr hd) (by
    intro z hz
    exact (card_get_eq_count cs (oldPair z)).trans (idxCount_oo v t a w z.1 z.2 (strict z hz))) (by
    intro i d
    exact (card_get_eq_count cs (dPair i d)).trans (idxCount_od v t a w i d))
  have combined := countPaths.trans agg
  change Nat.card {P // Perfect o cs P ∧ p P} = _
  rw [combined, dummyCard hle strict]
  by_cases h : S.card = r ∧ DSep S
  · rw [if_pos h]
    unfold DSep dv at h
    rw [if_pos h]
    exact (Nat.mul_assoc _ _ _).symm
  · rw [if_neg h]
    unfold DSep dv at h
    rw [if_neg h, Nat.zero_mul]

