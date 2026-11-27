import Mathlib
import PEqualNP.Defs

-- Generic run and backward-liveness helpers adapted from
-- PEqualNP/Outside/L_meta_4536.lean at 2e11e655454b7cd7dd6b8c82381f3b5360a30e9b (Apache-2.0).
namespace PEqualNP.Outside.L_meta_27237_aux

private abbrev Wire (R : Type) := R → Bool

private def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

private def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

private def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

private noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

private noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

private def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

private def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

private def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => (∃ bank a, Reach roots p bank ∧ Available bank a ∧ c=inv a :: bank) ∨
    (∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach roots p bank ∧ Available bank a ∧
      Available bank b ∧ c=combine op a b :: bank)
private theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
private theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank)
    (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) := Or.inl ⟨bank,a,h,ha,rfl⟩
private theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  Or.inr ⟨op,bank,a,b,h,ha,hb,rfl⟩
private theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (h : Reach roots p bank) (ha : Available bank a), motive p bank h →
      motive (p+1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    rcases h with ⟨bank,a,h,ha,rfl⟩ | ⟨op,bank,a,b,h,ha,hb,rfl⟩
    · exact one h ha (ih h)
    · exact two op h ha hb (ih h)

private def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

private def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => (∃ (save : Bool) (a : Wire R) (rest : List (Wire R)), (a::rest).Perm zs ∧
      Run goal s (inv a :: kept save a rest)) ∨
    (∃ (op ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), (a::b::rest).Perm zs ∧
      Run goal s (combine op a b :: kept ka a (kept kb b rest)))
private theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
private theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    rcases h with ⟨save,a,rest,q,h⟩ | ⟨op,ka,kb,a,b,rest,q,h⟩
    · exact Or.inl ⟨save,a,rest,q.trans p,h⟩
    · exact Or.inr ⟨op,ka,kb,a,b,rest,q.trans p,h⟩
private theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  Or.inl ⟨save,a,rest,List.Perm.refl _,h⟩
private theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  Or.inr ⟨op,ka,kb,a,b,rest,List.Perm.refl _,h⟩
private theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (one : ∀ {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)),
      motive s _ h → motive (s+1) (a::rest) (Run.one save h))
    (two : ∀ {s a b rest} (op ka kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    rcases h with ⟨save,a,rest,p,h⟩ | ⟨op,ka,kb,a,b,rest,p,h⟩
    · exact perm p (Run.one save h) (one save h (ih h))
    · exact perm p (Run.two op ka kb h) (two op ka kb h (ih h))

private theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

private theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

private theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

private theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

private theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

private theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

private theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

private theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

private theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

private theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

private def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

private theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

private theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih


section Backward
open scoped Classical

private def Proper {R : Type} (a : Wire R) : Prop := ¬ Constant a

variable {R : Type}

private def Live (target : (Wire R)) : Nat → Nat → Finset (Wire R) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ Proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Wire R)) (a : (Wire R)), t=u+1 ∧ S=insert a U ∧ Proper a ∧
      inv a ∉ insert a U ∧ Live target k u (insert (inv a) U)) ∨
    (∃ (U : Finset (Wire R)) (a b : (Wire R)) (d : Bool), S=insert a (insert b U) ∧ Proper a ∧ Proper b ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧ Live target k t (insert (combine d a b) U))
private theorem Live.stop {target : (Wire R)} (hp : Proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
private theorem Live.unary {target : (Wire R)} {k t : Nat} {U : Finset (Wire R)} {a : (Wire R)} (ha : Proper a)
    (hfresh : inv a ∉ insert a U) (tail : Live target k t (insert (inv a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
private theorem Live.binary {target : (Wire R)} {k t : Nat} {U : Finset (Wire R)} {a b : (Wire R)} {d : Bool}
    (ha : Proper a) (hb : Proper b) (hab : a ≠ b)
    (hfresh : combine d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (combine d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
private theorem Live.ind {target : (Wire R)} {motive : ∀ (k t : Nat) (S : Finset (Wire R)), Live target k t S → Prop}
    (stop : ∀ (hp : Proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Wire R)} {a : (Wire R)} (ha : Proper a)
      (hfresh : inv a ∉ insert a U) (tail : Live target k t (insert (inv a) U)),
      motive k t (insert (inv a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Wire R)} {a b : (Wire R)} {d : Bool}
      (ha : Proper a) (hb : Proper b) (hab : a ≠ b)
      (hfresh : combine d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (combine d a b) U)),
      motive k t (insert (combine d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Wire R)} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, Proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private def represented (w : List (Wire R)) (v : (Wire R)) : Prop := v ∈ w ∨ ¬ Proper v

private def witness (w : List (Wire R)) (z : (Wire R)) : Prop :=
  (∃ a ∈ w, Proper a ∧ z = inv a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ Proper a ∧ Proper b ∧ a ≠ b ∧ z = combine d a b)

private theorem inv_rep {w : List (Wire R)} {a : (Wire R)} (ha : Available w a) :
    represented w (inv a) ∨ witness w (inv a) := by
  by_cases hc : Constant a
  · exact Or.inl (Or.inr (fun h => h (inv_constant hc)))
  · exact Or.inr (Or.inl ⟨a,ha.resolve_right hc,hc,rfl⟩)

private theorem bin_rep {w : List (Wire R)} {a b : (Wire R)} (d : Bool) (ha : Available w a)
    (hb : Available w b) : represented w (combine d a b) ∨ witness w (combine d a b) := by
  by_cases hc : Constant a ∨ Constant b
  · rcases from_constant d hc ha hb with hm | hz
    · exact Or.inl (Or.inl hm)
    · exact Or.inl (Or.inr fun h => h hz)
  · have ca : ¬Constant a := fun h => hc (Or.inl h)
    have cb : ¬Constant b := fun h => hc (Or.inr h)
    by_cases eq : a = b
    · subst b
      have same : combine d a a = a := by cases d <;> funext r <;> simp [combine]
      exact Or.inl (Or.inl (same.symm ▸ ha.resolve_right ca))
    · exact Or.inr (Or.inr ⟨d,a,b,ha.resolve_right ca,hb.resolve_right cb,ca,cb,eq,rfl⟩)

private lemma pull_gate {w : List (Wire R)} {z : (Wire R)} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (inv a)
        have ht : Live target k t (insert (inv a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : inv a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (combine d a b)
        have ht : Live target k t (insert (combine d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : combine d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

private theorem kept_fin (k : Bool) (a : (Wire R)) (l : List (Wire R)) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

private theorem list_run {T : (Wire R)} {k u S} (h : Live T k u S) (v : List (Wire R))
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run T k v := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simp [eqv]
    exact Run.perm eq Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : inv a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (inv a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm perm (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : combine d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (combine d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all
    exact Run.perm perm (Run.two d ka kb progress)


private theorem reach_live_sub {roots : List (Wire R)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots := by
  induction h using Reach.ind generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_gate run (inv_rep ha)
      (fun v hv => by simpa [or_comm] using sub v hv)
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_gate run (bin_rep d ha hb)
      (fun v hv => by simpa [or_comm] using sub v hv)
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

private theorem reachRun {roots : List (Wire R)} {p bank target}
    (h : Reach roots p bank) (hit : Available bank target) (nc : ¬ Constant target) :
    ∃ k ws, k ≤ p ∧ ws.Nodup ∧ (∀ a ∈ ws, a ∈ roots) ∧ Run target k ws := by
  obtain ⟨k,t,S,hk,hl,hs⟩ := reach_live_sub h (Live.stop nc)
    (fun a ha => by simpa using (show a = target from by simpa using ha) ▸ hit.resolve_right nc)
  exact ⟨k,S.toList,by omega,Finset.nodup_toList _,fun a ha => hs a (by simpa using ha),
    list_run hl _ (Finset.nodup_toList _) (by simp)⟩

end Backward




private def cube (r : Fin 256) (i : Fin 8) : Bool := r.val.testBit i.val

private def goal (r : Fin 256) : Bool :=
  (cube r 0 && cube r 2 && cube r 7) ||
  (cube r 0 && cube r 4 && cube r 5) ||
  (cube r 1 && cube r 2 && cube r 6) ||
  (cube r 1 && cube r 3 && cube r 5)

private abbrev slice (z : Option (Fin 8)) (r : Fin 256) : Prop :=
  z.elim true (cube r) = true

private abbrev Recipe := Fin 8 × Nat × Nat

-- The pair states tested are 00, the state with only `middle` true, and 11.
-- `lower` distinguishes 00 from both larger states; `upper` distinguishes
-- the middle state from 11. Each unordered pair has two candidate recipes.
private def recipes : Nat → Nat → List Recipe
  | 0, 1 => [⟨0, 52, 84⟩, ⟨0, 236, 232⟩]
  | 0, 2 => [⟨0, 50, 82⟩, ⟨0, 248, 232⟩]
  | 0, 3 => [⟨0, 54, 38⟩, ⟨3, 242, 212⟩]
  | 0, 4 => [⟨0, 134, 38⟩, ⟨0, 236, 232⟩]
  | 0, 5 => [⟨0, 134, 14⟩, ⟨0, 220, 216⟩]
  | 0, 6 => [⟨0, 50, 38⟩, ⟨6, 158, 156⟩]
  | 0, 7 => [⟨0, 50, 22⟩, ⟨0, 124, 108⟩]
  | 1, 2 => [⟨1, 41, 73⟩, ⟨1, 248, 240⟩]
  | 1, 3 => [⟨1, 69, 37⟩, ⟨1, 244, 240⟩]
  | 1, 4 => [⟨1, 45, 37⟩, ⟨4, 233, 204⟩]
  | 1, 5 => [⟨1, 69, 13⟩, ⟨1, 220, 216⟩]
  | 1, 6 => [⟨1, 41, 13⟩, ⟨1, 188, 180⟩]
  | 1, 7 => [⟨1, 41, 37⟩, ⟨7, 93, 92⟩]
  | 2, 3 => [⟨2, 82, 50⟩, ⟨3, 227, 225⟩]
  | 2, 4 => [⟨2, 75, 41⟩, ⟨4, 227, 226⟩]
  | 2, 5 => [⟨2, 67, 81⟩, ⟨2, 155, 154⟩]
  | 2, 6 => [⟨2, 153, 27⟩, ⟨2, 163, 162⟩]
  | 2, 7 => [⟨2, 90, 27⟩, ⟨2, 99, 97⟩]
  | 3, 4 => [⟨3, 39, 37⟩, ⟨4, 227, 226⟩]
  | 3, 5 => [⟨5, 21, 7⟩, ⟨5, 211, 210⟩]
  | 3, 6 => [⟨3, 39, 7⟩, ⟨6, 182, 178⟩]
  | 3, 7 => [⟨3, 54, 23⟩, ⟨3, 99, 101⟩]
  | 4, 5 => [⟨5, 14, 7⟩, ⟨5, 203, 201⟩]
  | 4, 6 => [⟨4, 45, 15⟩, ⟨4, 163, 166⟩]
  | 4, 7 => [⟨4, 39, 7⟩, ⟨7, 109, 105⟩]
  | 5, 6 => [⟨5, 15, 7⟩, ⟨6, 158, 153⟩]
  | 5, 7 => [⟨5, 14, 7⟩, ⟨7, 93, 89⟩]
  | 6, 7 => [⟨6, 31, 29⟩, ⟨7, 39, 38⟩]
  | _, _ => []

private def candidates (a b : Fin 8) : List Recipe :=
  recipes (min a.val b.val) (max a.val b.val)

private def middleState (a b : Fin 8) (w : Recipe) : Bool × Bool :=
  (decide (w.1 = a), decide (w.1 = b))

private def sectionRow (base : Nat) (a b : Fin 8) (p : Bool × Bool) : Fin 256 :=
  Fin.ofNat 256 (base + (if p.1 then 2 ^ a.val else 0) + (if p.2 then 2 ^ b.val else 0))

private abbrev separates (z : Option (Fin 8)) (a b : Fin 8) (p q : Bool × Bool)
    (base : Nat) : Prop :=
  let r := sectionRow base a b p
  let s := sectionRow base a b q
  slice z r ∧ slice z s ∧
    (∀ i : Fin 8, i ≠ a → i ≠ b → cube r i = cube s i) ∧
    cube r a = p.1 ∧ cube r b = p.2 ∧ cube s a = q.1 ∧ cube s b = q.2 ∧
    goal r ≠ goal s

private abbrev verifies (z : Option (Fin 8)) (a b : Fin 8) (w : Recipe) : Prop :=
  separates z a b (false, false) (middleState a b w) w.2.1 ∧
  separates z a b (false, false) (true, true) w.2.1 ∧
  separates z a b (middleState a b w) (true, true) w.2.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem checked : ∀ (a b : Fin 8) (z : Option (Fin 8)),
    a ≠ b → z ≠ some a → z ≠ some b →
      (candidates a b).any (fun w => decide (verifies z a b w)) = true := by
  intro a
  fin_cases a <;> decide +kernel

private theorem encodeCollision {z : Option (Fin 8)} {a b : Fin 8} {p q : Bool × Bool}
    {base : Nat} (h : separates z a b p q base) (enc : Bool → Bool → Bool)
    (he : enc p.1 p.2 = enc q.1 q.2) :
    ∃ r s : Fin 256, slice z r ∧ slice z s ∧
      (∀ i, i ≠ a → i ≠ b → cube r i = cube s i) ∧
      enc (cube r a) (cube r b) = enc (cube s a) (cube s b) ∧ goal r ≠ goal s := by
  obtain ⟨hr, hs, hsame, hra, hrb, hsa, hsb, hg⟩ := h
  refine ⟨sectionRow base a b p, sectionRow base a b q, hr, hs, hsame, ?_, hg⟩
  simpa only [hra, hrb, hsa, hsb] using he

private theorem boolCollision (p q r : Bool) : p = q ∨ p = r ∨ q = r := by
  cases p <;> cases q <;> cases r <;> decide

/-- No single Boolean signal of two axes suffices, even after fixing another axis true. -/
private theorem pair_collision (z : Option (Fin 8)) (a b : Fin 8) (hab : a ≠ b)
    (ha : z ≠ some a) (hb : z ≠ some b) (enc : Bool → Bool → Bool) :
    ∃ r s : Fin 256, slice z r ∧ slice z s ∧
      (∀ i, i ≠ a → i ≠ b → cube r i = cube s i) ∧
      enc (cube r a) (cube r b) = enc (cube s a) (cube s b) ∧ goal r ≠ goal s := by
  obtain ⟨w, _, hw⟩ := List.any_eq_true.mp (checked a b z hab ha hb)
  obtain ⟨h₀ₘ, h₀₁, hₘ₁⟩ : verifies z a b w := of_decide_eq_true hw
  rcases boolCollision (enc false false) (enc (middleState a b w).1 (middleState a b w).2)
    (enc true true) with he | he | he
  · exact encodeCollision h₀ₘ enc he
  · exact encodeCollision h₀₁ enc he
  · exact encodeCollision hₘ₁ enc he

private theorem otherAxis : ∀ (a : Fin 8) (z : Option (Fin 8)),
    ∃ b : Fin 8, a ≠ b ∧ z ≠ some b := by
  intro a
  fin_cases a <;> decide +kernel

/-- Every unfixed axis is essential, with all other axes held equal. -/
private theorem axis_essential (z : Option (Fin 8)) (a : Fin 8) (ha : z ≠ some a) :
    ∃ r s : Fin 256, slice z r ∧ slice z s ∧
      (∀ i, i ≠ a → cube r i = cube s i) ∧ goal r ≠ goal s := by
  obtain ⟨b, hab, hb⟩ := otherAxis a z
  obtain ⟨r, s, hr, hs, hsame, he, hg⟩ := pair_collision z a b hab ha hb (fun _ y => y)
  refine ⟨r, s, hr, hs, ?_, hg⟩
  intro i hi
  by_cases hib : i = b
  · simpa only [hib] using he
  · exact hsame i hi hib




/- This fragment follows the generic Wire, Run, Reach, and contraction helpers. -/

/-- Each axis value can change the goal while the other axes stay fixed. -/
private def SlackEssential {R : Type} (goal : Wire R) (axes : List (Wire R)) : Prop :=
  ∀ a ∈ axes, ∃ x y : R,
    a x ≠ a y ∧ (∀ v ∈ axes, v ≠ a → v x = v y) ∧ goal x ≠ goal y

/-- No one-bit encoding of two distinct axes, together with the untouched axes,
    determines the goal. -/
private def SlackNoPair {R : Type} (goal : Wire R) (axes : List (Wire R)) : Prop :=
  ∀ a b : Wire R, a ≠ b → a ∈ axes → b ∈ axes → ∀ code : Bool → Bool → Bool,
    ∃ x y : R, code (a x) (b x) = code (a y) (b y) ∧
      (∀ v ∈ axes, v ≠ a → v ≠ b → v x = v y) ∧ goal x ≠ goal y

private abbrev slackTrueRows {R : Type} (z : Wire R) : {r : R // z r = true} → R := Subtype.val

/-- The other axes and the goal, on each slice where one axis is true. -/
private def SlackTrueSlices {R : Type} (goal : Wire R) (axes : List (Wire R)) : Prop :=
  ∀ (z : Wire R) (others : List (Wire R)), (z :: others).Perm axes →
    let ws := others.map (restrictRows (slackTrueRows z))
    ws.Nodup ∧ SlackEssential (restrictRows (slackTrueRows z) goal) ws ∧
      SlackNoPair (restrictRows (slackTrueRows z) goal) ws

/-- The conversion from bank executions to live executions. -/
private def SlackReachRun : Prop :=
  ∀ {R : Type} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {goal : Wire R},
    Reach roots p bank → Available bank goal → ¬ Constant goal →
      ∃ k ws, k ≤ p ∧ ws.Nodup ∧ (∀ a ∈ ws, a ∈ roots) ∧ Run goal k ws

private theorem slack_run_length {R : Type} {goal : Wire R} {s ws} (h : Run goal s ws) :
    ws.length ≤ s + 1 := by
  induction h using Run.ind with
  | stop => simp
  | perm p _ ih => exact p.length_eq ▸ ih
  | one save _ ih => cases save <;> simp [kept] at ih ⊢ <;> omega
  | two op ka kb _ ih => cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

private theorem slack_run_agree {R : Type} {goal : Wire R} {s ws} {x y : R}
    (h : Run goal s ws) : (∀ a ∈ ws, a x = a y) → goal x = goal y := by
  induction h using Run.ind with
  | stop => exact fun agree => agree goal (by simp)
  | perm p _ ih => exact fun agree => ih (fun a ha => agree a (p.mem_iff.mp ha))
  | @one s a rest save _ ih =>
    intro agree
    apply ih
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · have ha := agree a (by simp)
      simp [inv, ha]
    · exact agree v (List.mem_cons.mpr (mem_kept hv))
  | @two s a b rest op ka kb _ ih =>
    intro agree
    apply ih
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · have ha := agree a (by simp)
      have hb := agree b (by simp)
      cases op <;> simp [combine, ha, hb]
    · rcases mem_kept hv with rfl | hv
      · exact agree _ (by simp)
      · exact agree v (List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hv)))

private theorem slack_pairs_mono {R : Type} {goal : Wire R} {ws roots : List (Wire R)}
    (h : SlackNoPair goal roots) (sub : ∀ a ∈ ws, a ∈ roots) : SlackNoPair goal ws := by
  intro a b hab ha hb code
  obtain ⟨x, y, hc, hr, hg⟩ := h a b hab (sub a ha) (sub b hb) code
  exact ⟨x, y, hc, fun v hv => hr v (sub v hv), hg⟩

private theorem slack_drop_pair {R : Type} {goal a b : Wire R} {rest : List (Wire R)}
    {s : Nat} {op : Bool} (nd : (a :: b :: rest).Nodup)
    (pairs : SlackNoPair goal (a :: b :: rest)) :
    ¬ Run goal s (combine op a b :: rest) := by
  intro tail
  have na := (List.nodup_cons.mp nd).1
  have nb := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
  have hab : a ≠ b := fun e => na (by simp [e])
  let code : Bool → Bool → Bool := fun x y => if op then x || y else x && y
  obtain ⟨x, y, hc, hr, hg⟩ := pairs a b hab (by simp) (by simp) code
  apply hg (slack_run_agree tail ?_)
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · cases op <;> simpa [code, combine] using hc
  · exact hr v (by simp [hv])
      (fun e => na (List.mem_cons_of_mem _ (e ▸ hv))) (fun e => nb (e ▸ hv))

/-- A tight live execution, with at least two roots, must first merge two roots
    and drop both; the pair collision excludes that step. -/
private theorem slack_tight {R : Type} {goal : Wire R} {s ws} (h : Run goal s ws)
    (two : 2 ≤ ws.length) (tight : s + 1 ≤ ws.length)
    (nd : ws.Nodup) (pairs : SlackNoPair goal ws) : False := by
  cases s with
  | zero =>
    have p : [goal].Perm ws := h
    have len := p.length_eq
    simp at len
    omega
  | succ s =>
    rcases h with ⟨save, a, rest, p, tail⟩ | ⟨op, ka, kb, a, b, rest, p, tail⟩
    · have len := p.length_eq
      have bound := slack_run_length tail
      cases save <;> simp [kept] at bound len <;> omega
    · have len := p.length_eq
      have bound := slack_run_length tail
      cases ka <;> cases kb
      · exact slack_drop_pair (p.nodup_iff.mpr nd)
          (slack_pairs_mono pairs (fun _ hv => p.mem_iff.mp hv)) tail
      all_goals simp [kept] at bound len; omega

private theorem slack_recode_pairs {R : Type} {goal : Wire R} {ws : List (Wire R)}
    (bit : Wire R → Bool → Bool) (pairs : SlackNoPair goal ws) :
    SlackNoPair goal (ws.map (fun w r => bit w (w r))) := by
  intro a b hab ha hb code
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
  have huv : u ≠ v := fun h => hab (congrArg (fun (w : Wire R) r => bit w (w r)) h)
  obtain ⟨x, y, hc, hr, hg⟩ := pairs u v huv hu hv (fun x y => code (bit u x) (bit v y))
  refine ⟨x, y, hc, ?_, hg⟩
  intro c hc hcu hcv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  exact congrArg (bit w) (hr w hw
    (fun h => hcu (congrArg (fun (k : Wire R) r => bit k (k r)) h))
    (fun h => hcv (congrArg (fun (k : Wire R) r => bit k (k r)) h)))

private theorem slack_flip_head {R : Type} {goal a : Wire R} {rest : List (Wire R)}
    (nd : (a :: rest).Nodup) (ess : SlackEssential goal (a :: rest))
    (pairs : SlackNoPair goal (a :: rest)) :
    (inv a :: rest).Nodup ∧ SlackNoPair goal (inv a :: rest) := by
  classical
  obtain ⟨hna, nr⟩ := List.nodup_cons.mp nd
  have diff : ∀ w ∈ rest, w ≠ a := fun w hw h => hna (h ▸ hw)
  have fresh : inv a ∉ rest := by
    intro hm
    obtain ⟨x, y, hxy, hagree, _⟩ := ess a (by simp)
    exact hxy (Bool.not_inj (hagree (inv a) (List.mem_cons_of_mem _ hm) (diff (inv a) hm)))
  let bit : Wire R → Bool → Bool := fun w b => if w = a then !b else b
  have he : (a :: rest).map (fun w r => bit w (w r)) = inv a :: rest := by
    have hh : (fun r => bit a (a r)) = inv a := by funext r; simp [bit, inv]
    have ht : rest.map (fun w r => bit w (w r)) = rest.map id := by
      apply List.map_congr_left
      intro w hw
      funext r
      simp [bit, diff w hw]
    simp only [List.map_cons, hh, ht, List.map_id]
  exact ⟨List.nodup_cons.mpr ⟨fresh, nr⟩, he ▸ slack_recode_pairs bit pairs⟩

private theorem slack_slice {R : Type} {goal z w : Wire R} {axes rest : List (Wire R)}
    {s : Nat} {op swap : Bool} (bridge : SlackReachRun)
    (hlen : axes.length = 8) (slices : SlackTrueSlices goal axes)
    (p : (z :: w :: rest).Perm axes) (hs : s ≤ 7)
    (tail : Run goal s ((if swap then combine op w z else combine op z w) :: z :: rest)) : False := by
  classical
  let row := slackTrueRows z
  let cut := restrictRows row
  let roots := (w :: rest).map cut
  let gate := if swap then combine op w z else combine op z w
  obtain ⟨nd, ess, pairs⟩ := slices z (w :: rest) p
  have hw : cut w ∈ roots := by simp [roots]
  have hz : Constant (cut z) := ⟨true, by funext r; exact r.property⟩
  have nc : ¬ Constant (cut goal) := by
    rintro ⟨b, hb⟩
    obtain ⟨x, y, _, _, hg⟩ := ess (cut w) hw
    apply hg
    change cut goal x = cut goal y
    rw [hb]
  have ag : Available roots (cut gate) := by
    cases swap <;> cases op
    · exact from_constant false (Or.inl hz) (Or.inr hz) (Or.inl hw)
    · exact from_constant true (Or.inl hz) (Or.inr hz) (Or.inl hw)
    · exact from_constant false (Or.inr hz) (Or.inl hw) (Or.inr hz)
    · exact from_constant true (Or.inr hz) (Or.inl hw) (Or.inr hz)
  have supplyCut : supply roots (cut gate :: cut z :: rest.map cut) := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ag
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inr hz
    · exact Or.inl (List.mem_cons_of_mem _ ha)
  have tailCut : Run (cut goal) s (cut gate :: cut z :: rest.map cut) :=
    restrict_run row tail
  obtain ⟨q, bank, hq, hit, hmass⟩ :=
    contraction nc tailCut roots Reach.start supplyCut
  have charge : cost (cut z) = 1 := by simp [cost, hz]
  rw [mass_cons, mass_cons, charge] at hmass
  obtain ⟨k, used, hk, nu, sub, run⟩ := bridge hq hit nc
  have full : ∀ a ∈ roots, a ∈ used := by
    intro a ha
    by_contra hmiss
    obtain ⟨x, y, _, agree, hg⟩ := ess a ha
    apply hg (slack_run_agree run ?_)
    intro v hv
    exact agree v (sub v hv) (fun e => hmiss (e ▸ hv))
  have he : used.toFinset = roots.toFinset := by
    ext a
    simpa only [List.mem_toFinset] using (show a ∈ used ↔ a ∈ roots from ⟨sub a, full a⟩)
  have hl := congrArg Finset.card he
  rw [List.toFinset_card_of_nodup nu, List.toFinset_card_of_nodup nd] at hl
  have len := p.length_eq
  have seven : roots.length = 7 := by
    simp [roots] at len ⊢
    omega
  change used.length = roots.length at hl
  exact slack_tight run (by omega) (by omega) nu (slack_pairs_mono pairs sub)

/-- Eight distinct essential axes, with no compressible pair either on the full
    rows or on any one-axis true slice, rule out a live execution of at most
    eight steps. The row type can in particular be `Fin 256`. -/
private theorem slackOne_impossible {R : Type} {goal : Wire R} {axes : List (Wire R)} {s : Nat}
    (bridge : SlackReachRun) (len : axes.length = 8) (nd : axes.Nodup)
    (ess : SlackEssential goal axes) (pairs : SlackNoPair goal axes)
    (slices : SlackTrueSlices goal axes) (hs : s ≤ 8) (run : Run goal s axes) : False := by
  cases s with
  | zero =>
    have p : [goal].Perm axes := run
    have hl := p.length_eq
    simp [len] at hl
  | succ s =>
    rcases run with ⟨save, a, rest, p, tail⟩ | ⟨op, ka, kb, a, b, rest, p, tail⟩
    · have hl := p.length_eq
      have bound := slack_run_length tail
      cases save
      · have ess' : SlackEssential goal (a :: rest) := by
          intro w hw
          obtain ⟨x, y, hd, ho, hg⟩ := ess w (p.mem_iff.mp hw)
          exact ⟨x, y, hd, fun v hv => ho v (p.mem_iff.mp hv), hg⟩
        obtain ⟨nd', pairs'⟩ := slack_flip_head (p.nodup_iff.mpr nd) ess'
          (slack_pairs_mono pairs (fun _ hv => p.mem_iff.mp hv))
        have tail' : Run goal s (inv a :: rest) := tail
        exact slack_tight tail' (by simp at hl ⊢; omega) (by simp at hl ⊢; omega) nd' pairs'
      · simp [kept] at bound hl
        omega
    · cases ka <;> cases kb
      · exact slack_drop_pair (p.nodup_iff.mpr nd)
          (slack_pairs_mono pairs (fun _ hv => p.mem_iff.mp hv)) tail
      · exact slack_slice (op := op) (swap := true) bridge len slices
          ((List.Perm.swap a b rest).trans p) (by omega) tail
      · exact slack_slice (op := op) (swap := false) bridge len slices p (by omega) tail
      · have hl := p.length_eq
        have bound := slack_run_length tail
        simp [kept] at bound hl
        omega


open PEqualNP.CircuitLowerBounds

private def value {R : Type} (w : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map fun i => w.getD i (fun _ => false) r)

private def execute {R : Type} (gs : List Gate) (w : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun w g => w ++ [value w g]) w

private theorem evalAt {R : Type} (r : R) (gs : List Gate) (w : List (Wire R)) :
    (execute gs w).map (fun f => f r) = (Circuit.mk gs 0).wires (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [value w g])).map (fun f => f r) = _
    rw [ih]
    simp only [Circuit.wires, List.foldl_cons, List.map_append, List.map_singleton]
    congr 2
    unfold value
    apply congrArg (fun xs : List Bool => [g.op.eval xs])
    apply List.map_congr_left
    intro i _
    exact (List.getD_map w (fun _ => false) (fun f : Wire R => f r) (n := i)).symm

private def shape (g : Gate) : Prop :=
  (∃ a, g = ⟨.not, [a]⟩) ∨ (∃ a b, g = ⟨.and, [a,b]⟩ ∨ g = ⟨.or,[a,b]⟩)

private def marked (g : Gate) : Bool :=
  g.inputs.contains 0 || g.inputs.contains 9 || g.inputs.contains 10

private theorem get_available {R : Type} {w bank : List (Wire R)}
    (hs : supply bank w) (i : Nat) : Available bank (w.getD i (fun _ => false)) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : w[i]? with
  | none => exact Or.inr ⟨false,rfl⟩
  | some a => exact hs a (List.mem_of_getElem? he)

private theorem valueNot {R : Type} (w : List (Wire R)) (a : Nat) :
    value w ⟨.not,[a]⟩ = inv (w.getD a (fun _ => false)) := by
  rfl

private theorem valueAnd {R : Type} (w : List (Wire R)) (a b : Nat) :
    value w ⟨.and,[a,b]⟩ = combine false (w.getD a (fun _ => false)) (w.getD b (fun _ => false)) := by
  funext r
  simp [value, GateOp.eval, combine]

private theorem valueOr {R : Type} (w : List (Wire R)) (a b : Nat) :
    value w ⟨.or,[a,b]⟩ = combine true (w.getD a (fun _ => false)) (w.getD b (fun _ => false)) := by
  funext r
  simp [value, GateOp.eval, combine]

private theorem extendMarked {R : Type} {roots bank w : List (Wire R)} {p : Nat}
    (h : Reach roots p bank) (sup : supply bank w) (g : Gate) (sh : shape g)
    (pins : ∀ i : Nat, i = 0 ∨ i = 9 ∨ i = 10 → Constant (w.getD i (fun _ => false))) :
    ∃ q next, Reach roots q next ∧ supply next (w ++ [value w g]) ∧
      q ≤ p + (if marked g then 0 else 1) := by
  have finish (next : List (Wire R)) {q : Nat} (hn : Reach roots q next)
      (ha : Available next (value w g)) (inc : ∀ v, Available bank v → Available next v)
      (hq : q ≤ p + (if marked g then 0 else 1)) :
      ∃ q next, Reach roots q next ∧ supply next (w ++ [value w g]) ∧
        q ≤ p + (if marked g then 0 else 1) := by
    refine ⟨q,next,hn,?_,hq⟩
    intro v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact inc _ (sup _ hv)
    · exact ha
  rcases sh with ⟨a,rfl⟩ | ⟨a,b,hg⟩
  · by_cases hm : marked (⟨.not,[a]⟩ : Gate) = true
    · apply finish bank h _ (fun _ hs => hs) (by simp [hm])
      rw [valueNot]
      have hp : a = 0 ∨ a = 9 ∨ a = 10 := by
        simp [marked, or_assoc] at hm
        rcases hm with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inr (Or.inr h.symm)
      exact Or.inr (inv_constant (pins _ hp))
    · apply finish _ (Reach.one h (get_available sup a)) _ (fun _ hs => available_cons _ hs)
        (by simp [hm])
      rw [valueNot]
      exact Or.inl (by simp)
  · have bin (g : Gate) (d : Bool) (ins : g.inputs = [a,b])
        (hv : value w g = combine d (w.getD a (fun _ => false)) (w.getD b (fun _ => false))) :
        ∃ q next, Reach roots q next ∧ supply next (w ++ [value w g]) ∧
          q ≤ p + (if marked g then 0 else 1) := by
      -- Rebuild the local completion step with this arbitrary op tag.
      have push {q : Nat} {next : List (Wire R)} (hn : Reach roots q next)
          (ha : Available next (value w g)) (inc : ∀ v, Available bank v → Available next v)
          (hq : q ≤ p + (if marked g then 0 else 1)) :
          ∃ q next, Reach roots q next ∧ supply next (w ++ [value w g]) ∧
            q ≤ p + (if marked g then 0 else 1) := by
        refine ⟨q,next,hn,?_ ,hq⟩
        intro v hm
        simp only [List.mem_append,List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact inc _ (sup _ hm)
        · exact ha
      by_cases hm : marked g = true
      · apply push h _ (fun _ hs => hs) (by simp [hm])
        rw [hv]
        apply from_constant d _ (get_available sup a) (get_available sup b)
        have hs : (a = 0 ∨ a = 9 ∨ a = 10) ∨ (b = 0 ∨ b = 9 ∨ b = 10) := by
          simp only [marked, ins, List.contains_cons, List.contains_nil, Bool.or_false,
            Bool.or_eq_true, beq_iff_eq] at hm
          tauto
        exact hs.imp (pins a) (pins b)
      · apply push (Reach.two d h (get_available sup a) (get_available sup b)) _
          (fun _ hs => available_cons _ hs) (by simp [hm])
        rw [hv]
        exact Or.inl (by simp)
    rcases hg with rfl | rfl
    · exact bin _ false rfl (valueAnd w a b)
    · exact bin _ true rfl (valueOr w a b)

private theorem foldingCost {R : Type} (gs : List Gate) {roots w bank : List (Wire R)} {p : Nat}
    (h : Reach roots p bank) (sup : supply bank w) (hlen : 10 < w.length)
    (pins : ∀ i : Nat, i = 0 ∨ i = 9 ∨ i = 10 → Constant (w.getD i (fun _ => false)))
    (sh : ∀ g ∈ gs, shape g) :
    ∃ q next, Reach roots q next ∧ supply next (execute gs w) ∧
      q ≤ p + (gs.filter fun g => !marked g).length := by
  induction gs generalizing w bank p with
  | nil => exact ⟨p,bank,h,sup,by simp⟩
  | cons g gs ih =>
    obtain ⟨q,next,hq,hs,hqle⟩ := extendMarked h sup g (sh g (by simp)) pins
    have hlen' : 10 < (w ++ [value w g]).length := by simp; omega
    have pins' : ∀ i : Nat, i = 0 ∨ i = 9 ∨ i = 10 →
        Constant ((w ++ [value w g]).getD i (fun _ => false)) := by
      intro i hi
      rw [List.getD_append _ _ _ _ (by rcases hi with rfl | rfl | rfl <;> omega)]
      exact pins i hi
    obtain ⟨q',next',hq',hs',hle⟩ := ih hq hs hlen' pins' (fun x hx => sh x (by simp [hx]))
    refine ⟨q',next',hq',hs',?_⟩
    by_cases hm : marked g = true <;> simp [hm] at hqle ⊢ <;> omega


open PEqualNP.CircuitLowerBounds

private theorem marked_of_pin {g : Gate} {i : Nat}
    (pin : i = 0 ∨ i = 9 ∨ i = 10) (hi : i ∈ g.inputs) : marked g = true := by
  simp only [marked, Bool.or_eq_true, List.contains_iff_mem]
  rcases pin with rfl | rfl | rfl <;> tauto

private theorem twoMarked (gs : List Gate) (sh : ∀ g ∈ gs, shape g)
    (used : ∀ i : Nat, i = 0 ∨ i = 9 ∨ i = 10 → ∃ g ∈ gs, i ∈ g.inputs) :
    2 ≤ (gs.filter marked).length := by
  have find (i : Nat) (hi : i = 0 ∨ i = 9 ∨ i = 10) :
      ∃ g ∈ gs.filter marked, i ∈ g.inputs := by
    obtain ⟨g,hg,hi'⟩ := used i hi
    exact ⟨g,List.mem_filter.mpr ⟨hg,marked_of_pin hi hi'⟩,hi'⟩
  have h0 := find 0 (by simp)
  have h9 := find 9 (by simp)
  have h10 := find 10 (by simp)
  cases eq : gs.filter marked with
  | nil => simp [eq] at h0
  | cons g rest =>
    cases rest with
    | cons g' rest => simp
    | nil =>
      simp only [eq, List.mem_singleton, exists_eq_left] at h0 h9 h10
      have hg : g ∈ gs := (List.mem_filter.mp (show g ∈ gs.filter marked by simp [eq])).1
      rcases sh g hg with ⟨a,hg⟩ | ⟨a,b,hg | hg⟩ <;>
        simp only [hg,List.mem_cons,List.not_mem_nil,or_false] at h0 h9 h10
      · omega
      · rcases h0 with h0 | h0 <;> rcases h9 with h9 | h9 <;> rcases h10 with h10 | h10 <;> omega
      · rcases h0 with h0 | h0 <;> rcases h9 with h9 | h9 <;> rcases h10 with h10 | h10 <;> omega

private theorem eval_agree_tail (gs : List Gate) (a b : Bool) (xs : List Bool)
    (no : ∀ g ∈ gs, 0 ∉ g.inputs) :
    ∃ ys, (Circuit.mk gs 0).wires (a :: xs) = a :: ys ∧
      (Circuit.mk gs 0).wires (b :: xs) = b :: ys := by
  induction gs generalizing xs with
  | nil => exact ⟨xs,rfl,rfl⟩
  | cons g gs ih =>
    have eql : g.inputs.map (fun i => (a :: xs).getD i false) =
        g.inputs.map (fun i => (b :: xs).getD i false) := by
      apply List.map_congr_left
      intro i hi
      cases i with
      | zero => exact False.elim (no g (by simp) hi)
      | succ i => rfl
    obtain ⟨ys,ha,hb⟩ := ih
      (xs ++ [g.op.eval (g.inputs.map (fun i => (b :: xs).getD i false))])
      (fun h hh => no h (by simp [hh]))
    refine ⟨ys,?_,?_⟩
    · change (Circuit.mk gs 0).wires (a :: (xs ++ [_])) = _
      rw [eql]
      exact ha
    · exact hb

private def headA : Gate := ⟨.and,[0,1]⟩
private def headB : Gate := ⟨.and,[0,3]⟩

private def sample (r : Fin 256) (b : Bool) : Fin 9 → Bool := Fin.cases b (cube r)

private def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private theorem directUse (gs : List Gate) (o : Nat) (ho : o ≠ 0)
    (ev : ∀ x : Fin 9 → Bool, (Circuit.mk (headA::headB::gs) o).eval (List.ofFn x) = target x) :
    ∃ g ∈ gs, 0 ∈ g.inputs := by
  classical
  by_contra h
  push Not at h
  obtain ⟨ys,ha,hb⟩ := eval_agree_tail gs false true
    [false,false,false,true,false,false,false,true,false,false] h
  have h0 := ev (sample 136 false)
  have h1 := ev (sample 136 true)
  change ((Circuit.mk gs 0).wires (false :: [false,false,false,true,false,false,false,true,false,false])).getD o false = false at h0
  change ((Circuit.mk gs 0).wires (true :: [false,false,false,true,false,false,false,true,false,false])).getD o false = true at h1
  rw [ha] at h0
  rw [hb] at h1
  cases o with
  | zero => exact ho rfl
  | succ o =>
    rw [List.getD_cons_succ] at h0 h1
    exact Bool.false_ne_true (h0.symm.trans h1)

private theorem usedPins (gs : List Gate) (direct : ∃ g ∈ gs, 0 ∈ g.inputs)
    (live : ∀ j : Fin (headA::headB::gs).length, j.val + 1 < (headA::headB::gs).length →
      ∃ k : Fin (headA::headB::gs).length, j.val < k.val ∧
        9 + j.val ∈ ((headA::headB::gs).get k).inputs) :
    ∀ i : Nat, i = 0 ∨ i = 9 ∨ i = 10 → ∃ g ∈ gs, i ∈ g.inputs := by
  have hlen : 0 < gs.length := by
    obtain ⟨g,hg,_⟩ := direct
    exact List.length_pos_of_mem hg
  have occurs (i : Nat) (hi : i = 9 ∨ i = 10) (h : ∃ g ∈ headA::headB::gs, i ∈ g.inputs) :
      ∃ g ∈ gs, i ∈ g.inputs := by
    obtain ⟨g,hg,hi'⟩ := h
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · rcases hi with rfl | rfl <;> simp [headA] at hi'
    · rcases hi with rfl | rfl <;> simp [headB] at hi'
    · exact ⟨g,hg,hi'⟩
  have use9 : ∃ g ∈ gs, 9 ∈ g.inputs := by
    obtain ⟨k,_,hk⟩ := live ⟨0,by simp⟩ (by simp)
    exact occurs 9 (Or.inl rfl) ⟨_,List.get_mem _ _,hk⟩
  have use10 : ∃ g ∈ gs, 10 ∈ g.inputs := by
    obtain ⟨k,_,hk⟩ := live ⟨1,by simp⟩ (by simpa using hlen)
    exact occurs 10 (Or.inr rfl) ⟨_,List.get_mem _ _,hk⟩
  intro i hi
  rcases hi with rfl | rfl | rfl
  · exact direct
  · exact use9
  · exact use10

private theorem goal_agree {r s : Fin 256} (h : ∀ i, cube r i = cube s i) :
    goal r = goal s := by
  simp only [goal, h]

private theorem cube_essential (z : Option (Fin 8)) (i : Fin 8) (hi : z ≠ some i) :
    ∃ r s, slice z r ∧ slice z s ∧ cube r i ≠ cube s i ∧
      (∀ j, j ≠ i → cube r j = cube s j) ∧ goal r ≠ goal s := by
  obtain ⟨r,s,hr,hs,ha,hg⟩ := axis_essential z i hi
  refine ⟨r,s,hr,hs,?_,ha,hg⟩
  intro he
  apply hg (goal_agree ?_)
  intro j
  by_cases hj : j = i
  · simpa only [hj] using he
  · exact ha j hj

private theorem properties {R : Type} (z : Option (Fin 8)) (a : Fin 8 → Wire R)
    (f : Wire R) (ws : List (Wire R))
    (rep : ∀ w ∈ ws, ∃ i, z ≠ some i ∧ w = a i)
    (pick : (r : Fin 256) → slice z r → R)
    (bits : ∀ r h i, a i (pick r h) = cube r i)
    (vals : ∀ r h, f (pick r h) = goal r) :
    SlackEssential f ws ∧ SlackNoPair f ws := by
  constructor
  · intro w hw
    obtain ⟨i,hi,rfl⟩ := rep w hw
    obtain ⟨r,s,hr,hs,hd,ha,hg⟩ := cube_essential z i hi
    refine ⟨pick r hr,pick s hs,by simpa only [bits] using hd,?_,by simpa only [vals] using hg⟩
    intro v hv hn
    obtain ⟨j,_,rfl⟩ := rep v hv
    simpa only [bits] using ha j (fun e => hn (congrArg a e))
  · intro w v hn hw hv enc
    obtain ⟨i,hi,rfl⟩ := rep w hw
    obtain ⟨j,hj,rfl⟩ := rep v hv
    obtain ⟨r,s,hr,hs,ha,he,hg⟩ := pair_collision z i j (fun e => hn (congrArg a e)) hi hj enc
    refine ⟨pick r hr,pick s hs,by simpa only [bits] using he,?_,by simpa only [vals] using hg⟩
    intro u hu hne hne'
    obtain ⟨k,_,rfl⟩ := rep u hu
    simpa only [bits] using ha k (fun e => hne (congrArg a e)) (fun e => hne' (congrArg a e))

private def axis (i : Fin 8) : Wire (Fin 256) := fun r => cube r i
private def axes : List (Wire (Fin 256)) := List.ofFn axis

private theorem mem_axes (w : Wire (Fin 256)) (hw : w ∈ axes) : ∃ i, w = axis i := by
  have h : ∃ i, axis i = w := (List.mem_ofFn.mp hw)
  obtain ⟨i,hi⟩ := h
  exact ⟨i,hi.symm⟩

private theorem axis_injective : Function.Injective axis := by
  intro i j eq
  by_contra ne
  obtain ⟨r,s,_,_,hd,ha,_⟩ := cube_essential none i (by simp)
  apply hd
  exact congrFun eq r |>.trans ((ha j (Ne.symm ne)).trans (congrFun eq s).symm)

private theorem axes_nd : axes.Nodup := by
  simpa only [axes, List.ofFn_eq_map] using (List.nodup_finRange 8).map axis_injective

private theorem axes_len : axes.length = 8 := List.length_ofFn

private theorem axes_prop : SlackEssential goal axes ∧ SlackNoPair goal axes := by
  refine properties none axis goal axes ?_ (fun r _ => r) ?_ ?_
  · intro w hw
    obtain ⟨i,hi⟩ := mem_axes w hw
    exact ⟨i,by simp,hi⟩
  · intros; rfl
  · intros; rfl

private theorem sliced_axes : SlackTrueSlices goal axes := by
  classical
  intro z others p
  have hz : z ∈ axes := p.mem_iff.mp (by simp)
  obtain ⟨k,rfl⟩ := mem_axes z hz
  have nd := p.nodup_iff.mpr axes_nd
  let a := fun i : Fin 8 => restrictRows (slackTrueRows (axis k)) (axis i)
  have rep0 : ∀ w ∈ others, ∃ i, k ≠ i ∧ w = axis i := by
    intro w hw
    obtain ⟨i,rfl⟩ := mem_axes w (p.mem_iff.mp (by simp [hw]))
    exact ⟨i,fun e => (List.nodup_cons.mp nd).1 (e.symm ▸ hw),rfl⟩
  let pick : (r : Fin 256) → slice (some k) r → {r : Fin 256 // axis k r = true} :=
    fun r h => ⟨r,h⟩
  constructor
  · apply List.Nodup.map_on _ (List.nodup_cons.mp nd).2
    intro u hu v hv eq
    obtain ⟨i,hi,rfl⟩ := rep0 u hu
    obtain ⟨j,hj,rfl⟩ := rep0 v hv
    by_contra hne
    have hij : i ≠ j := fun e => hne (congrArg axis e)
    obtain ⟨r,s,hr,hs,hd,ha,_⟩ := cube_essential (some k) i (by simpa using hi)
    apply hd
    exact (congrFun eq (pick r hr)).trans ((ha j (Ne.symm hij)).trans
      ((congrFun eq (pick s hs)).symm))
  · refine properties (some k) a (restrictRows (slackTrueRows (axis k)) goal) _ ?_ pick ?_ ?_
    · intro w hw
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
      obtain ⟨i,hi,rfl⟩ := rep0 v hv
      exact ⟨i,by simpa using hi,rfl⟩
    · intros; rfl
    · intros; rfl

private theorem impossible8 {p : Nat} {bank : List (Wire (Fin 256))}
    (h : Reach axes p bank) (hit : Available bank goal) (hp : p ≤ 8) : False := by
  classical
  have ess := axes_prop.1
  have nc : ¬ Constant goal := by
    rintro ⟨b,hb⟩
    have hm : axis 0 ∈ axes := List.mem_ofFn.mpr ⟨0,rfl⟩
    obtain ⟨x,y,_,_,hg⟩ := ess _ hm
    exact hg (by rw [hb])
  obtain ⟨k,ws,hk,nd,sub,run⟩ := reachRun h hit nc
  have full : ∀ a ∈ axes, a ∈ ws := by
    intro a ha
    by_contra miss
    obtain ⟨x,y,_,agree,hg⟩ := ess _ ha
    apply hg (slack_run_agree run ?_)
    intro v hv
    exact agree v (sub _ hv) (fun eq => miss (eq ▸ hv))
  have perm : ws.Perm axes := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd axes_nd
    ext a
    simpa only [List.mem_toFinset] using (show a ∈ ws ↔ a ∈ axes from ⟨sub a,full a⟩)
  exact slackOne_impossible reachRun axes_len axes_nd ess axes_prop.2 sliced_axes (by omega)
    (Run.perm perm run)

private def zeroWire : Wire (Fin 256) := fun _ => false
private def initial : List (Wire (Fin 256)) := zeroWire :: axes
private def seeded : List (Wire (Fin 256)) := initial ++ [zeroWire,zeroWire]

private theorem head_values (gs : List Gate) :
    execute (headA::headB::gs) initial = execute gs seeded := by
  change execute gs ((initial ++ [value initial headA]) ++ [value (initial ++ [value initial headA]) headB]) = _
  have ha : value initial headA = zeroWire := by
    rw [headA,valueAnd]
    rfl
  rw [ha]
  have hb : value (initial ++ [zeroWire]) headB = zeroWire := by
    rw [headB,valueAnd]
    rfl
  rw [hb]
  simp [seeded,List.append_assoc]

private theorem evalInitial (r : Fin 256) : initial.map (fun a => a r) = List.ofFn (sample r false) := by
  rw [List.ofFn_succ]
  simp [initial,axes,axis,zeroWire,sample]

private theorem finishPrefix (gs : List Gate) (o : Nat) (small : (headA::headB::gs).length ≤ 12)
    (out : o + 1 = 9 + (headA::headB::gs).length)
    (ev : ∀ x : Fin 9 → Bool, (Circuit.mk (headA::headB::gs) o).eval (List.ofFn x) = target x)
    (sh : ∀ g ∈ gs, shape g)
    (live : ∀ j : Fin (headA::headB::gs).length, j.val + 1 < (headA::headB::gs).length →
      ∃ k : Fin (headA::headB::gs).length, j.val < k.val ∧
        9 + j.val ∈ ((headA::headB::gs).get k).inputs) : False := by
  have ho : o ≠ 0 := by simp at out; omega
  have used := usedPins gs (directUse gs o ho ev) live
  have count := twoMarked gs sh used
  have budget : (gs.filter fun g => !marked g).length ≤ 8 := by
    have count' := List.length_eq_length_filter_add (l := gs) marked
    simp at small
    omega
  have hs : supply axes seeded := by
    intro w hw
    simp only [seeded,initial,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (rfl | hw) | (rfl | rfl)
    · exact Or.inr ⟨false,rfl⟩
    · exact Or.inl hw
    all_goals exact Or.inr ⟨false,rfl⟩
  have hlen : 10 < seeded.length := by simp [seeded,initial,axes_len]
  have pins : ∀ i : Nat, i = 0 ∨ i = 9 ∨ i = 10 →
      Constant (seeded.getD i (fun _ => false)) := by
    intro i hi
    rcases hi with rfl | rfl | rfl <;> exact ⟨false,rfl⟩
  obtain ⟨q,bank,hq,hs,hle⟩ := foldingCost gs Reach.start hs hlen pins sh
  have result : (execute gs seeded).getD o zeroWire = goal := by
    funext r
    have hw := evalAt r (headA::headB::gs) initial
    rw [head_values,evalInitial] at hw
    have h := ev (sample r false)
    change ((Circuit.mk (headA::headB::gs) 0).wires _).getD o false = goal r at h
    rw [←hw] at h
    exact (List.getD_map (execute gs seeded) zeroWire (fun a => a r) (n := o)).symm.trans h
  exact impossible8 hq (result ▸ get_available hs o) (by omega)

end PEqualNP.Outside.L_meta_27237_aux

open PEqualNP.Outside.L_meta_27237_aux

theorem PEqualNP.Outside.L_meta_27237 :
¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩) := by
  intro hex
  obtain ⟨C,_,small,ev,out,sh,_,live,first,second⟩ := hex
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil => simp at first
  | cons a gs =>
    cases gs with
    | nil => simp at second
    | cons b gs =>
      have ea : a = headA := by simpa [headA] using first
      have eb : b = headB := by simpa [headB] using second
      subst a
      subst b
      apply finishPrefix gs o small out ev _ live
      intro g hg
      obtain ⟨j,hj⟩ := List.get_of_mem (show g ∈ headA::headB::gs by simp [hg])
      have legal := sh j
      rw [hj] at legal
      rcases legal with ⟨ho,a,hi,ha⟩ | ⟨ho,a,b,hab,hb,hi⟩
      · exact Or.inl ⟨a, by cases g; simp_all⟩
      · refine Or.inr ⟨a,b,?_⟩
        rcases ho with ho | ho
        · exact Or.inl (by cases g; simp_all)
        · exact Or.inr (by cases g; simp_all)
