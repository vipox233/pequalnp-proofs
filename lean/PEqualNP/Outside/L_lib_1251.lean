import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1251
namespace Salqueng1251
abbrev Feas {t m n : Nat} (row : Fin t → Fin m) (var : Fin t → Fin n) (sign : Fin t → Bool) (S : Finset (Fin t)) : Prop := (∀ i ∈ S, ∀ j ∈ S, row i = row j → i=j) ∧ ∃ val : Fin n → Bool, ∀ i ∈ S, val (var i) = sign i
noncomputable def Active {t : Nat} (f : Fin t → Nat) (k : Nat) : Finset Nat := (((Finset.univ : Finset (Fin t)).filter (fun i => i.val < k)).image f) ∩ (((Finset.univ : Finset (Fin t)).filter (fun i => k ≤ i.val)).image f)
abbrev Edge (t W : Nat) := Fin t → Fin W → Bool → Fin W → Prop
abbrev Accepts {t W : Nat} (start : Fin W) (finals : Finset (Fin W)) (edge : Edge t W) (S : Finset (Fin t)) : Prop := ∃ st : Fin (t+1) → Fin W, st 0=start ∧ st (Fin.last t) ∈ finals ∧ ∀ i : Fin t, edge i (st i.castSucc) (decide (i∈S)) (st i.succ)
noncomputable def Moves {t W : Nat} (edge : Edge t W) (i : Fin t) (a : Fin W) : Finset (Bool × Fin W) := by classical exact Finset.univ.filter (fun z => edge i a z.1 z.2)
def Reach {t W : Nat} (finals : Finset (Fin W)) (edge : Edge t W) (X : Finset (Fin t)) : List (Fin t) → Fin W → Nat → Prop
  | [], a, d => a ∈ finals ∧ d=0
  | i::is, a, d => ∃ b : Bool, ∃ c : Fin W, edge i a b c ∧ (b=true → i∈X) ∧ Reach finals edge X is c (if b then d-1 else d)
end Salqueng1251

namespace Salqueng1251
open Finset
noncomputable def Score {t m n : Nat} (row : Fin t → Fin m) (var : Fin t → Fin n) (sign : Fin t → Bool) (X : Finset (Fin t)) := (Finset.univ : Finset (Fin n → Bool)).sup (fun s => ((X.filter (fun i => s (var i)=sign i)).image row).card)
theorem score_iff {t m n : Nat} (row : Fin t → Fin m) (var : Fin t → Fin n) (sign : Fin t → Bool) (X : Finset (Fin t)) (d : Nat) : d ≤ Score row var sign X ↔ ∃ S ⊆ X, Feas row var sign S ∧ d≤S.card := by
  classical
  constructor
  · intro hd
    obtain ⟨val,_,hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Bool)) Finset.univ_nonempty (fun s => ((X.filter (fun i => s (var i)=sign i)).image row).card)
    let A := X.filter (fun i => val (var i)=sign i)
    have sur : (A : Set (Fin t)).SurjOn row (A.image row) := by
      intro r hr; obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp hr; exact ⟨i,hi,eq⟩
    obtain ⟨S,sub,inj,img⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ sur
    refine ⟨S,fun i hi => (Finset.mem_filter.mp (sub hi)).1, ⟨fun i hi j hj => inj hi hj, val, fun i hi => (Finset.mem_filter.mp (sub hi)).2⟩, ?_⟩
    change d≤(Finset.univ : Finset (Fin n → Bool)).sup _ at hd
    rw [hv] at hd
    have cnt := Finset.card_image_of_injOn inj
    change d≤(A.image row).card at hd
    rwa [←img,cnt] at hd
  · rintro ⟨S,sub,⟨inj,val,hval⟩,hd⟩
    have hinj : Set.InjOn row S := fun _ hi _ hj => inj _ hi _ hj
    let A := X.filter (fun i => val (var i)=sign i)
    have sa : S⊆A := fun i hi => Finset.mem_filter.mpr ⟨sub hi,hval i hi⟩
    have count : S.card ≤ (A.image row).card := by rw [←Finset.card_image_of_injOn hinj]; exact Finset.card_le_card (Finset.image_subset_image sa)
    exact (hd.trans count).trans (Finset.le_sup (f:=fun s : Fin n → Bool => ((X.filter (fun i => s (var i)=sign i)).image row).card) (Finset.mem_univ val))
theorem edge_total {t W : Nat} (edge : Edge t W) (deg : ∀ i a, (Moves edge i a).card ≤ 4) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ((Finset.univ : Finset (Fin t × Fin W × Bool × Fin W)).filter (fun z => edge z.1 z.2.1 z.2.2.1 z.2.2.2)).card ≤ 4*t*W := by
  classical
  let B := (Finset.univ : Finset (Fin t × Fin W))
  let pack := fun (p : Fin t × Fin W) => (Moves edge p.1 p.2).image (fun z => (p.1,p.2,z.1,z.2))
  have inc : (Finset.univ.filter (fun z : Fin t × Fin W × Bool × Fin W => edge z.1 z.2.1 z.2.2.1 z.2.2.2)) ⊆ B.biUnion pack := by
    intro z hz; obtain ⟨i,a,b,c⟩ := z
    exact Finset.mem_biUnion.mpr ⟨(i,a),Finset.mem_univ _,Finset.mem_image.mpr ⟨(b,c),Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩,rfl⟩⟩
  have bd : ∀ p : Fin t × Fin W, (pack p).card≤4 := fun p => Finset.card_image_le.trans (deg p.1 p.2)
  calc
    _ ≤ (B.biUnion pack).card := Finset.card_le_card inc
    _ ≤ ∑ p ∈ B, (pack p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ B, 4 := Finset.sum_le_sum (fun p _ => bd p)
    _ = _ := by simp [B]; ring
end Salqueng1251

namespace Salqueng1251
def Follows {t W : Nat} (finals : Finset (Fin W)) (edge : Edge t W) (S : Finset (Fin t)) : List (Fin t) → Fin W → Prop
  | [],a => a∈finals
  | i::is,a => ∃ c, edge i a (decide (i∈S)) c ∧ Follows finals edge S is c
private theorem follows_congr {t W} {F : Finset (Fin W)} {e : Edge t W} (xs : List (Fin t)) {S T : Finset (Fin t)} (same : ∀ i∈xs, i∈S ↔ i∈T) (a : Fin W) : Follows F e S xs a ↔ Follows F e T xs a := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    have eq : decide (i∈S) = decide (i∈T) := by simp [same i (by simp)]
    simp only [Follows,eq,ih (fun j hj => same j (by simp [hj]))]
theorem reach_iff_sel {t W} (F : Finset (Fin W)) (e : Edge t W) (X : Finset (Fin t)) (xs : List (Fin t)) (nd : xs.Nodup) (a : Fin W) (d : Nat) :
    Reach F e X xs a d ↔ ∃ S : Finset (Fin t), S⊆xs.toFinset ∧ S⊆X ∧ Follows F e S xs a ∧ d≤S.card := by
  classical
  induction xs generalizing a d with
  | nil => simp [Reach,Follows,and_comm,eq_comm]
  | cons i xs ih =>
    obtain ⟨fresh,tailnd⟩ := List.nodup_cons.mp nd
    constructor
    · rintro ⟨b,c,step,allowed,next⟩
      obtain ⟨S,sub,sx,path,card⟩ := (ih tailnd c _).1 next
      have hi : i ∉ S := fun h => fresh (List.mem_toFinset.mp (sub h))
      cases b with
      | false =>
        exact ⟨S,fun j h => by simpa using List.mem_cons_of_mem i (List.mem_toFinset.mp (sub h)),sx,⟨c,by simpa [hi] using step,path⟩,card⟩
      | true =>
        have keep : Follows F e (insert i S) xs c := (follows_congr xs (S:=S) (T:=insert i S) (fun j hj => by have ne : j≠i := fun eq => fresh (eq ▸ hj); simp [ne]) c).1 path
        refine ⟨insert i S, ?_, Finset.insert_subset (allowed rfl) sx, ⟨c,by simpa using step,keep⟩, ?_⟩
        · simpa using Finset.insert_subset_insert i sub
        · simp only [Finset.card_insert_of_notMem hi]; simp only [if_true] at card; omega
    · rintro ⟨S,sub,sx,⟨c,step,path⟩,card⟩
      have subtail : S.erase i ⊆ xs.toFinset := by
        intro j hj; obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hj
        rcases List.mem_cons.mp (List.mem_toFinset.mp (sub mem)) with eq|h
        · exact False.elim (ne eq)
        · exact List.mem_toFinset.mpr h
      have keep : Follows F e (S.erase i) xs c := (follows_congr xs (S:=S) (T:=S.erase i) (fun j hj => by have ne : j≠i := fun eq => fresh (eq ▸ hj); simp [ne]) c).1 path
      refine ⟨decide (i∈S),c,step,fun h => sx (of_decide_eq_true h),(ih tailnd c _).2 ⟨S.erase i,subtail,(Finset.erase_subset ..).trans sx,keep,?_⟩⟩
      by_cases mem : i∈S
      · simp [mem,Finset.card_erase_of_mem mem]; omega
      · simpa [mem] using card
private theorem follows_fn {t W} (F : Finset (Fin W)) (e : Edge t W) (S : Finset (Fin t)) {k : Nat} (f : Fin k → Fin t) (a : Fin W) :
    Follows F e S (List.ofFn f) a ↔ ∃ st : Fin (k+1) → Fin W, st 0=a ∧ st (Fin.last k)∈F ∧ ∀ j : Fin k, e (f j) (st j.castSucc) (decide (f j∈S)) (st j.succ) := by
  induction k generalizing a with
  | zero =>
    simp only [List.ofFn_zero,Follows]
    constructor
    · intro h; exact ⟨fun _ => a,rfl,h,fun j => j.elim0⟩
    · rintro ⟨st,ha,h,_⟩; simpa [show Fin.last 0 = 0 by rfl,ha] using h
  | succ k ih =>
    rw [List.ofFn_succ]; simp only [Follows,ih]
    constructor
    · rintro ⟨c,step,st,h0,hf,hs⟩
      refine ⟨Fin.cons a st,by simp,by simpa using hf,?_⟩
      intro j; refine Fin.cases ?_ (fun j => ?_) j
      · simpa [Fin.cons_zero,Fin.cons_succ,h0] using step
      · change e (f j.succ) (Fin.cons (α := fun _ => Fin W) a st j.castSucc.succ) _ (Fin.cons (α := fun _ => Fin W) a st j.succ.succ)
        simpa only [Fin.cons_succ] using hs j
    · rintro ⟨st,h0,hf,hs⟩
      refine ⟨st 1,by simpa [h0] using hs 0,fun j => st j.succ, rfl, ?_, ?_⟩
      · exact hf
      · intro j; exact hs j.succ
 theorem reach_accept {t W} (F : Finset (Fin W)) (e : Edge t W) (X : Finset (Fin t)) (a : Fin W) (d : Nat) :
    Reach F e X (List.finRange t) a d ↔ ∃ S ⊆ X, Accepts a F e S ∧ d≤S.card := by
  rw [reach_iff_sel F e X _ (List.nodup_finRange t)]
  have law (S : Finset (Fin t)) : Follows F e S (List.finRange t) a ↔ Accepts a F e S := by
    exact follows_fn F e S (fun i => i) a
  simp only [law]
  have allS : ∀ S : Finset (Fin t), S⊆(List.finRange t).toFinset := by intro S j _; simp
  simp [allS]
end Salqueng1251

namespace Salqueng1251
namespace Live1251
open scoped Classical

private theorem mem_live {t : Nat} {f : Fin t → Nat} {k x : Nat} :
    x ∈ Active f k ↔ (∃ p, p.val < k ∧ f p = x) ∧ (∃ q, k ≤ q.val ∧ f q = x) := by
  classical
  simp [Active, Finset.mem_image]

private abbrev Bits {t : Nat} (f : Fin t → Nat) (k : Nat) := (x : Active f k) → Bool
private abbrev D {t : Nat} (r v : Fin t → Nat) (k : Nat) := Bits r k × Bits v k

private noncomputable def rd {t : Nat} {f : Fin t → Nat} {k : Nat} (bits : Bits f k) (x : Nat) : Bool := by
  classical exact if h : x ∈ Active f k then bits ⟨x,h⟩ else false

private theorem rd_mem {t} {f : Fin t → Nat} {k x} (b : Bits f k) (h : x ∈ Active f k) : rd b x = b ⟨x,h⟩ := by
  simp [rd, h]

private noncomputable def encode {t w} {r v : Fin t → Nat}
    (bound : ∀ k, (Active r k).card + (Active v k).card ≤ w) (k : Nat) : D r v k ↪ Fin (2^w) := by
  classical
  apply (Fintype.equivFin _).toEmbedding.trans
  apply Fin.castLEEmb
  simpa [D, Bits, Fintype.card_fun, ← pow_add] using
    (Nat.pow_le_pow_right (by omega : 0 < 2) (bound k))

private noncomputable def choiceBit {t} {v : Fin t → Nat} (i : Fin t) (b : Bits v i.val) (g : Bool) : Bool := by
  classical exact if v i ∈ Active v i.val then rd b (v i) else g

private noncomputable def nxt {t} {r v : Fin t → Nat} (i : Fin t) (d : D r v i.val) (b g : Bool) : D r v (i.val+1) := by
  classical exact (fun x => rd d.1 x.val || (b && decide (r i = x.val)),
    fun x => if v i = x.val then choiceBit i d.2 g else rd d.2 x.val)

private abbrev Guard {t} {r v : Fin t → Nat} (s : Fin t → Bool) (i : Fin t) (d : D r v i.val) (b g : Bool) : Prop :=
  b = true → rd d.1 (r i) = false ∧ choiceBit i d.2 g = s i

private noncomputable def graph {t w} {r v : Fin t → Nat} (s : Fin t → Bool)
    (e : ∀ k, D r v k ↪ Fin (2^w)) : Edge t (2^w) :=
  fun i a b c => ∃ g : Bool, let d := Function.invFun (e i.val) a
    Guard s i d b g ∧ c = e (i.val+1) (nxt i d b g)

private theorem branches {t w} {r v : Fin t → Nat} (s : Fin t → Bool)
    (e : ∀ k, D r v k ↪ Fin (2^w)) (i : Fin t) (a : Fin (2^w)) : (Moves (graph s e) i a).card ≤ 4 := by
  classical
  let f : Bool × Bool → Bool × Fin (2^w) := fun z => (z.1, e (i.val+1) (nxt i (Function.invFun (e i.val) a) z.1 z.2))
  have h : Moves (graph s e) i a ⊆ Finset.univ.image f := by
    intro z hz
    obtain ⟨g, -, he⟩ := (Finset.mem_filter.mp hz).2
    exact Finset.mem_image.mpr ⟨(z.1,g), Finset.mem_univ _, Prod.ext rfl he.symm⟩
  exact (Finset.card_le_card h).trans ((Finset.card_image_le).trans (by decide))

private def Past {t} (S : Finset (Fin t)) (f : Fin t → Nat) (k x : Nat) : Prop :=
  ∃ j ∈ S, j.val < k ∧ f j = x

private noncomputable def snap {t} (S : Finset (Fin t)) (r v : Fin t → Nat) (val : Nat → Bool) (k : Nat) : D r v k := by
  classical exact (fun x => decide (Past S r k x.val), fun x => val x.val)

private theorem snap_row {t} {S : Finset (Fin t)} {r v : Fin t → Nat} {val : Nat → Bool} {k x : Nat}
    (hq : ∃ q, k ≤ q.val ∧ r q = x) : rd (snap S r v val k).1 x = decide (Past S r k x) := by
  classical
  by_cases hx : x ∈ Active r k
  · simp [rd_mem _ hx, snap]
  · have hn : ¬ Past S r k x := by
      rintro ⟨p, -, hp, hp'⟩
      exact hx (mem_live.mpr ⟨⟨p,hp,hp'⟩,hq⟩)
    simp [rd, hx, hn]

private theorem snap_choice {t} {S : Finset (Fin t)} {r v : Fin t → Nat} {val : Nat → Bool} (i : Fin t) :
    choiceBit i (snap S r v val i.val).2 (val (v i)) = val (v i) := by
  classical
  by_cases hx : v i ∈ Active v i.val <;> simp [choiceBit, hx, rd, snap]

private theorem snap_next {t} {S : Finset (Fin t)} {r v : Fin t → Nat} {val : Nat → Bool} (i : Fin t) :
    snap S r v val (i.val+1) = nxt i (snap S r v val i.val) (decide (i∈S)) (val (v i)) := by
  classical
  apply Prod.ext <;> funext x
  · rcases (mem_live.mp x.property).2 with ⟨q,hq,hqx⟩
    change decide (Past S r (i.val+1) x.val) = (rd _ _ || _)
    rw [snap_row ⟨q, by omega, hqx⟩]
    simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
    constructor
    · rintro ⟨j,hj,hlt,heq⟩
      by_cases h : j = i
      · subst j; exact Or.inr ⟨hj,heq⟩
      · exact Or.inl ⟨j,hj,by have := Fin.val_ne_of_ne h; omega,heq⟩
    · rintro (⟨j,hj,hl,he⟩ | ⟨hi,he⟩)
      · exact ⟨j,hj,by omega,he⟩
      · exact ⟨i,hi,by omega,he⟩
  · change val x.val = if v i = x.val then choiceBit i _ _ else rd _ _
    split
    · rename_i h; rw [snap_choice, h]
    · rename_i h
      obtain ⟨⟨p,hp,hpx⟩,q,hq,hqx⟩ := mem_live.mp x.property
      have hpi : p ≠ i := fun he => h (he ▸ hpx)
      have live : x.val ∈ Active v i.val := mem_live.mpr ⟨⟨p,by have := Fin.val_ne_of_ne hpi; omega,hpx⟩,q,by omega,hqx⟩
      rw [rd_mem _ live]; rfl

private theorem trace_sound {t} {r v : Fin t → Nat} {s : Fin t → Bool} {S : Finset (Fin t)}
    (d : (k : Fin (t+1)) → D r v k.val)
    (steps : ∀ i : Fin t, ∃ g, Guard s i (d i.castSucc) (decide (i ∈ S)) g ∧
      d i.succ = nxt i (d i.castSucc) (decide (i ∈ S)) g) :
    (∀ p ∈ S, ∀ q ∈ S, r p = r q → p = q) ∧
    (∀ p ∈ S, ∀ q ∈ S, v p = v q → s p = s q) := by
  classical
  have inv (k : Fin (t+1)) : ∀ p ∈ S, p.val < k.val → ∀ q : Fin t, k.val ≤ q.val →
      (r p = r q → rd (d k).1 (r p) = true) ∧ (v p = v q → rd (d k).2 (v p) = s p) := by
    induction k using Fin.induction with
    | zero => intro p hp hl; exact (Nat.not_lt_zero _ hl).elim
    | succ i ih =>
      intro p hp hl q hq
      obtain ⟨g,hguard,he⟩ := steps i
      have hpi : p.val ≤ i.val := Nat.lt_succ_iff.mp hl
      have hiq : i.val ≤ q.val := Nat.le_trans (Nat.le_succ _) hq
      constructor
      · intro h
        have live : r p ∈ Active r (i.val+1) := mem_live.mpr ⟨⟨p,hl,rfl⟩,q,hq,h.symm⟩
        rw [he,rd_mem _ live]
        change (rd _ (r p) || (decide (i ∈ S) && decide (r i = r p))) = true
        by_cases h' : p = i
        · subst p; simp [hp]
        · have hlt : p.val < i.val := lt_of_le_of_ne hpi (Fin.val_ne_of_ne h')
          rw [(ih p hp hlt q hiq).1 h]; rfl
      · intro h
        have live : v p ∈ Active v (i.val+1) := mem_live.mpr ⟨⟨p,hl,rfl⟩,q,hq,h.symm⟩
        rw [he, rd_mem _ live]
        change (if v i = v p then choiceBit i (d i.castSucc).2 g else rd _ _) = s p
        by_cases h' : p = i
        · subst p; simpa using (hguard (by simp [hp])).2
        · have hlt : p.val < i.val := lt_of_le_of_ne hpi (Fin.val_ne_of_ne h')
          have old := (ih p hp hlt q hiq).2 h
          have lv : v p ∈ Active v i.val := mem_live.mpr ⟨⟨p,hlt,rfl⟩,q,hiq,h.symm⟩
          split
          · rename_i heq; simpa [choiceBit,heq,lv] using old
          · exact old
  have pair (p q : Fin t) (hp : p ∈ S) (hq : q ∈ S) (hlt : p.val < q.val) :
      r p ≠ r q ∧ (v p = v q → s p = s q) := by
    obtain ⟨g,hg,-⟩ := steps q
    obtain ⟨hr,hv⟩ := hg (by simp [hq])
    obtain ⟨ir,iv⟩ := inv q.castSucc p hp hlt q (le_refl _)
    constructor
    · intro h; simpa [h,hr] using ir h
    · intro h
      have lv : v q ∈ Active v q.val := mem_live.mpr ⟨⟨p,hlt,h⟩,q,le_refl _,rfl⟩
      simp only [choiceBit, lv, ↓reduceIte] at hv
      exact (iv h).symm.trans (h ▸ hv)
  constructor <;> intro p hp q hq h
  · rcases lt_trichotomy p.val q.val with hl|he|hl
    · exact ((pair p q hp hq hl).1 h).elim
    · exact Fin.ext he
    · exact ((pair q p hq hp hl).1 h.symm).elim
  · rcases lt_trichotomy p.val q.val with hl|he|hl
    · exact (pair p q hp hq hl).2 h
    · exact congrArg s (Fin.ext he)
    · exact ((pair q p hq hp hl).2 h.symm).symm

end Live1251

open Live1251 in
theorem diagram {t m n w : Nat} (row : Fin t → Fin m) (var : Fin t → Fin n) (sign : Fin t → Bool)
    (hw : ∀ k, (Active (fun i => (row i).val) k).card + (Active (fun i => (var i).val) k).card ≤ w) :
    ∃ (start : Fin (2^w)) (finals : Finset (Fin (2^w))) (edge : Edge t (2^w)),
      (∀ S, Feas row var sign S ↔ Accepts start finals edge S) ∧ (∀ i a, (Moves edge i a).card ≤ 4) := by
  classical
  let r (i : Fin t) := (row i).val
  let v (i : Fin t) := (var i).val
  let e : ∀ k, D r v k ↪ Fin (2^w) := encode hw
  refine ⟨e 0 (fun _ => false,fun _ => false), Finset.univ, graph sign e, ?_, branches sign e⟩
  intro S
  constructor
  · rintro ⟨hr,asgn,hs⟩
    let val (x : Nat) := if h : x < n then asgn ⟨x,h⟩ else false
    let st (k : Fin (t+1)) := e k.val (snap S r v val k.val)
    refine ⟨st, ?_, Finset.mem_univ _, ?_⟩
    · apply congrArg (e 0)
      apply Prod.ext <;> funext x <;> obtain ⟨p,hp,-⟩ := (mem_live.mp x.property).1 <;> exact (Nat.not_lt_zero _ hp).elim
    · intro i
      refine ⟨val (v i), ?_⟩
      change Guard sign i (Function.invFun (e i.val) (e i.val (snap S r v val i.val))) _ _ ∧ _
      rw [Function.leftInverse_invFun (e i.val).injective]
      constructor
      · intro hb
        have hi : i ∈ S := of_decide_eq_true hb
        constructor
        · rw [snap_row ⟨i,le_refl _,rfl⟩]
          apply decide_eq_false
          rintro ⟨j,hj,hlt,he⟩
          exact (Nat.ne_of_lt hlt) (congrArg Fin.val (hr j hj i hi (Fin.ext he)))
        · rw [snap_choice]
          simpa [val,v] using hs i hi
      · apply congrArg (e (i.val+1))
        simp only [st, Fin.val_castSucc, Fin.val_succ]
        rw [Function.leftInverse_invFun (e i.val).injective (snap S r v val i.val)]
        exact snap_next i
  · rintro ⟨st,-,-,ht⟩
    let d (k : Fin (t+1)) : D r v k.val := Function.invFun (e k.val) (st k)
    have steps (i : Fin t) : ∃ g, Guard sign i (d i.castSucc) (decide (i∈S)) g ∧
        d i.succ = nxt i (d i.castSucc) (decide (i∈S)) g := by
      obtain ⟨g,hg,he⟩ := ht i
      refine ⟨g,hg,?_⟩
      change Function.invFun (e (i.val+1)) (st i.succ) = _
      rw [he]
      exact Function.leftInverse_invFun (e (i.val+1)).injective _
    obtain ⟨hr,hv⟩ := trace_sound d steps
    refine ⟨fun p hp q hq he => hr p hp q hq (congrArg Fin.val he), ?_⟩
    refine ⟨fun x => decide (∃ j ∈ S, var j = x ∧ sign j = true), ?_⟩
    intro i hi
    cases h : sign i with
    | false =>
      apply decide_eq_false
      rintro ⟨j,hj,he,hs⟩
      have hh := hv j hj i hi (congrArg Fin.val he)
      simp [hs,h] at hh
    | true => exact decide_eq_true ⟨i,hi,rfl,h⟩

end Salqueng1251

namespace Salqueng1251
namespace ThresholdCircuit
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private abbrev input {t : Nat} (X : Finset (Fin t)) := List.ofFn (fun i : Fin t => decide (i ∈ X)) ++ [false,true]
private abbrev circ (g : List Gate) : Circuit := ⟨g, 0⟩
private abbrev Good (t : Nat) (g : List Gate) : Prop :=
  FanInTwo (circ g) ∧ ReadsBack (t+2) (circ g) ∧ NotBracket.notCount (circ g) = 0
private def Rep {t : Nat} (g : List Gate) (w : Nat) (P : Finset (Fin t) → Prop) : Prop :=
  w < t+2+g.length ∧ ∀ X, (((circ g).wires (input X)).getD w false = true ↔ P X)
private abbrev Has {t : Nat} (g : List Gate) (P : Finset (Fin t) → Prop) := ∃ w, Rep g w P
private abbrev Ext (t : Nat) (g h : List Gate) := ∀ (w : Nat) (P : Finset (Fin t) → Prop), Rep g w P → Rep h w P
private theorem mapHas {t : Nat} {g h : List Gate} {P : Finset (Fin t) → Prop} (e : Ext t g h) (p : Has g P) : Has h P := by
  obtain ⟨w, hw⟩ := p
  exact ⟨w, e w P hw⟩
private theorem convHas {t : Nat} {g : List Gate} {P Q : Finset (Fin t) → Prop} (p : Has g P) (pq : ∀ X, P X ↔ Q X) : Has g Q := by
  obtain ⟨w, hw, he⟩ := p
  exact ⟨w, hw, fun X => (he X).trans (pq X)⟩
private theorem wireLen (g : List Gate) (v : List Bool) : ((circ g).wires v).length = v.length+g.length := by
  unfold Circuit.wires
  induction g generalizing v with
  | nil => simp
  | cons a s ih => change ((a::s).foldl _ v).length = _; rw [List.foldl_cons, ih]; simp; omega
private theorem snoc (g : List Gate) (a : Gate) (v : List Bool) : (circ (g++[a])).wires v =
    (circ g).wires v ++ [a.op.eval (a.inputs.map fun i => ((circ g).wires v).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]
private theorem snocExt {t : Nat} (g : List Gate) (a : Gate) : Ext t g (g++[a]) := by
  intro w P h
  obtain ⟨hw, hp⟩ := h
  refine ⟨by simp; omega, fun X => ?_⟩
  have hlen : w < ((circ g).wires (input X)).length := by simpa [wireLen, input] using hw
  simpa only [snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen] using hp X
private theorem snocGood {t : Nat} {g : List Gate} (hg : Good t g) (a : Gate)
    (hop : a.op = GateOp.and ∨ a.op = GateOp.or) (hlen : a.inputs.length ≤ 2)
    (hback : ∀ i ∈ a.inputs, i < t+2+g.length) : Good t (g++[a]) := by
  obtain ⟨hf, hb, hn⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro b h
    change b ∈ g ++ [a] at h
    rcases List.mem_append.1 h with h | h
    · exact hf b h
    · simp only [List.mem_singleton] at h
      subst b
      exact ⟨by rcases hop with h|h <;> simp [h], hlen⟩
  · intro j hj i hi
    change j < (g++[a]).length at hj
    change i ∈ ((g++[a]).getD j _).inputs at hi
    by_cases h : j < g.length
    · apply hb j h i
      simpa only [gateAt, circ, List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hi
    · have h' : j = g.length := by simp at hj; omega
      subst j
      apply hback
      simpa [List.getD_eq_getElem?_getD] using hi
  · change ((g++[a]).filter _).length = 0
    change (g.filter _).length = 0 at hn
    rcases hop with h|h <;> simp [h, hn]

private theorem emit {t : Nat} {g : List Gate} (hg : Good t g) (useAnd : Bool)
    {P Q : Finset (Fin t) → Prop} (hp : Has g P) (hq : Has g Q) :
    ∃ h, Good t h ∧ Ext t g h ∧ h.length = g.length+1 ∧
      Has h (fun X => if useAnd then P X ∧ Q X else P X ∨ Q X) := by
  obtain ⟨u, hu, hpu⟩ := hp
  obtain ⟨v, hv, hqv⟩ := hq
  let a : Gate := ⟨if useAnd then GateOp.and else GateOp.or, [u,v]⟩
  refine ⟨g++[a], snocGood hg a (by cases useAnd <;> simp [a]) (by simp [a]) ?_, snocExt g a, by simp,
    t+2+g.length, by simp, fun X => ?_⟩
  · intro i hi
    simp [a] at hi; rcases hi with rfl|rfl <;> assumption
  · have he : ((circ g).wires (input X)).length = t+2+g.length := by simp [wireLen,input]
    rw [snoc, ← he, List.getD_eq_getElem?_getD]
    simp only [List.getD_eq_getElem?_getD] at hpu hqv
    cases useAnd <;> simp [a, GateOp.eval, hpu X, hqv X]

private theorem inRep {t : Nat} (i : Fin t) : Rep [] i.val (fun X => i ∈ X) := by
  refine ⟨by simp; omega, fun X => ?_⟩
  have hi : i.val < (List.ofFn fun j : Fin t => decide (j∈X)).length := by simp
  simp [Circuit.wires,input,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
private theorem falseRep (t : Nat) : Rep (t:=t) [] t (fun _ => False) := by
  refine ⟨by simp, fun X => ?_⟩
  simp [Circuit.wires,input,List.getD_eq_getElem?_getD]
private theorem trueRep (t : Nat) : Rep (t:=t) [] (t+1) (fun _ => True) := by
  refine ⟨by simp, fun X => ?_⟩
  simp [Circuit.wires,input,List.getD_eq_getElem?_getD]

private theorem transExt {t : Nat} {g h k : List Gate} (a : Ext t g h) (b : Ext t h k) : Ext t g k :=
  fun w P hw => b w P (a w P hw)
private theorem idExt {t : Nat} {g : List Gate} : Ext t g g := fun _ _ hw => hw

private abbrev goalOf {t W : Nat} (finals : Finset (Fin W)) (edge : Edge t W)
    (is : List (Fin t)) (a : Fin W) (d : Nat) := fun X => Reach finals edge X is a d

private theorem cellMoves {t W m : Nat} {g : List Gate} (hg : Good t g) (eg : Ext t [] g)
    (finals : Finset (Fin W)) (edge : Edge t W) (is : List (Fin t))
    (table : ∀ a (d : Fin (m+1)), Has g (goalOf finals edge is a d.val))
    (i : Fin t) (d : Fin (m+1)) (s : Finset (Bool × Fin W)) :
    ∃ h, Good t h ∧ Ext t g h ∧ h.length ≤ g.length+2*s.card ∧
      Has h (fun X => ∃ z ∈ s, (z.1=true → i∈X) ∧
        Reach finals edge X is z.2 (if z.1 then d.val-1 else d.val)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨g, hg, idExt, by simp, convHas (mapHas eg ⟨_, falseRep t⟩) ?_⟩
    simp
  | @insert z s hz ih =>
    obtain ⟨h, hh, eh, lh, old⟩ := ih
    let d' : Fin (m+1) := ⟨if z.1 then d.val-1 else d.val, by
      have := d.isLt; split <;> omega⟩
    have enable : Has h (fun X => z.1=true → i∈X) := by
      cases heq : z.1 with
      | true => simpa using mapHas (transExt eg eh) ⟨_, inRep i⟩
      | false => simpa using mapHas (transExt eg eh) ⟨_, trueRep t⟩
    obtain ⟨h₁, hg₁, e₁, l₁, hv₁⟩ := emit hh true enable (mapHas eh (table z.2 d'))
    obtain ⟨h₂, hg₂, e₂, l₂, hv₂⟩ := emit hg₁ false hv₁ (mapHas e₁ old)
    refine ⟨h₂, hg₂, transExt eh (transExt e₁ e₂), ?_, convHas hv₂ ?_⟩
    · rw [Finset.card_insert_of_notMem hz]; omega
    · intro X
      simp [goalOf, d']

private theorem collect {t : Nat} {g : List Gate} {K : Type} [DecidableEq K]
    (hg : Good t g) (f : K → Finset (Fin t) → Prop)
    (build : ∀ k h, Good t h → Ext t g h →
      ∃ h', Good t h' ∧ Ext t h h' ∧ h'.length ≤ h.length+8 ∧ Has h' (f k))
    (s : Finset K) : ∃ h, Good t h ∧ Ext t g h ∧ h.length ≤ g.length+8*s.card ∧
      ∀ k ∈ s, Has h (f k) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, idExt, by simp, by simp⟩
  | @insert k s hk ih =>
    obtain ⟨h, hh, eh, lh, prev⟩ := ih
    obtain ⟨h', hh', eh', lh', next⟩ := build k h hh eh
    refine ⟨h', hh', transExt eh eh', ?_, fun j hj => ?_⟩
    · rw [Finset.card_insert_of_notMem hk]; omega
    · rcases Finset.mem_insert.1 hj with rfl|hj
      · exact next
      · exact mapHas eh' (prev _ hj)

private theorem layers {t W : Nat} (m : Nat) (finals : Finset (Fin W)) (edge : Edge t W)
    (deg : ∀ i a, (Moves edge i a).card ≤ 4) (is : List (Fin t)) :
    ∃ g, Good t g ∧ Ext t [] g ∧ g.length ≤ 8*is.length*(m+1)*W ∧
        ∀ a (d : Fin (m+1)), Has g (goalOf finals edge is a d.val) := by
  classical
  induction is with
  | nil =>
    refine ⟨[], ⟨by simp [FanInTwo], by simp [ReadsBack], rfl⟩, idExt, by simp, fun a d => ?_⟩
    by_cases ok : a ∈ finals ∧ d.val=0
    · exact convHas ⟨_, trueRep t⟩ (by simp [goalOf, Reach, ok])
    · exact convHas ⟨_, falseRep t⟩ (fun _ => ⟨False.elim, ok⟩)
  | cons i is ih =>
    obtain ⟨g, hg, eg, lg, tab⟩ := ih
    let f := fun k : Fin W × Fin (m+1) => goalOf finals edge (i::is) k.1 k.2.val
    have build : ∀ k h, Good t h → Ext t g h →
        ∃ h', Good t h' ∧ Ext t h h' ∧ h'.length ≤ h.length+8 ∧ Has h' (f k) := by
      intro k h hh eh
      obtain ⟨h', hg', e', l', hv⟩ := cellMoves hh (transExt eg eh) finals edge is
        (fun a d => mapHas eh (tab a d)) i k.2 (Moves edge i k.1)
      refine ⟨h', hg', e', by have := deg i k.1; omega, convHas hv ?_⟩
      intro X
      simp [Moves, f, Reach, Prod.exists]
    obtain ⟨h, hh, eh, lh, outputs⟩ := collect hg f build Finset.univ
    refine ⟨h, hh, transExt eg eh, ?_, fun a d => outputs (a,d) (Finset.mem_univ _)⟩
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at lh
    calc h.length ≤ 8*is.length*(m+1)*W + 8*(W*(m+1)) := by omega
         _ = 8*(i::is).length*(m+1)*W := by simp only [List.length_cons]; ring

end ThresholdCircuit

open ThresholdCircuit PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem compileThresholds {t W : Nat} (m : Nat) (start : Fin W) (finals : Finset (Fin W))
    (edge : Edge t W) (deg : ∀ i a, (Moves edge i a).card ≤ 4) :
    ∃ (C : Circuit) (outs : Fin (m+1) → Fin (t+2+C.size)),
      FanInTwo C ∧ ReadsBack (t+2) C ∧ C.output < t+2+C.size ∧
      NotBracket.notCount C = 0 ∧ C.size ≤ 8*t*(m+1)*W ∧
      ∀ (X : Finset (Fin t)) (l : Fin (m+1)),
        (C.wires (List.ofFn (fun i : Fin t => decide (i∈X)) ++ [false,true])).getD (outs l).val false = true ↔
          Reach finals edge X (List.finRange t) start l.val := by
  classical
  obtain ⟨g, ⟨hf, hb, hn⟩, _, lg, tab⟩ := layers m finals edge deg (List.finRange t)
  choose w hw using tab start
  refine ⟨circ g, fun l => ⟨w l, (hw l).1⟩, hf, hb, by change 0 < t+2+g.length; omega, hn, ?_,
    fun X l => (hw l).2 X⟩
  simpa [Circuit.size] using lg
end Salqueng1251

end PEqualNP.Outside.L_lib_1251

open PEqualNP.Outside.L_lib_1251.Salqueng1251

theorem PEqualNP.Outside.L_lib_1251 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (t m n w : Nat) (row : Fin t → Fin m) (var : Fin t → Fin n) (sign : Fin t → Bool),
  let feasible := fun (S : Finset (Fin t)) =>
    (∀ i ∈ S, ∀ j ∈ S, row i = row j → i=j) ∧
    ∃ val : Fin n → Bool, ∀ i ∈ S, val (var i) = sign i
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin t → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin t), feasible S ↔
      ∃ st : Fin (t+1) → Fin W, st 0=start ∧ st (Fin.last t) ∈ finals ∧
        ∀ i : Fin t, edge i (st i.castSucc) (decide (i∈S)) (st i.succ)
  let active := fun (f : Fin t → Nat) (k : Nat) =>
    (((Finset.univ : Finset (Fin t)).filter (fun i => i.val < k)).image f) ∩
    (((Finset.univ : Finset (Fin t)).filter (fun i => k ≤ i.val)).image f)
  let score := fun (X : Finset (Fin t)) =>
    (Finset.univ : Finset (Fin n → Bool)).sup (fun s =>
      ((X.filter (fun i => s (var i)=sign i)).image row).card)
  (∀ k, (active (fun i => (row i).val) k).card +
        (active (fun i => (var i).val) k).card ≤ w) →
  let W := 2^w
  (∃ (start : Fin W) (finals : Finset (Fin W)) (edge : Fin t → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge ∧
    ((Finset.univ : Finset (Fin t × Fin W × Bool × Fin W)).filter
      (fun z => edge z.1 z.2.1 z.2.2.1 z.2.2.2)).card ≤ 4*t*W) ∧
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : Fin (m+1) → Fin (t+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (t+2) C ∧
    C.output < t+2+C.size ∧ PEqualNP.NotBracket.notCount C = 0 ∧ C.size ≤ 8*t*(m+1)*W ∧
    ∀ (X : Finset (Fin t)) (l : Fin (m+1)),
      let input := List.ofFn (fun i : Fin t => decide (i ∈ X)) ++ [false,true]
      (C.wires input).getD (outs l).val false = true ↔ l.val ≤ score X) := by
  classical
  intro t m n w row var sign
  dsimp only
  intro hw
  have newActive (f : Fin t → Nat) (k : Nat) : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable; (((Finset.univ : Finset (Fin t)).filter (fun i => i.val < k)).image f) ∩ (((Finset.univ : Finset (Fin t)).filter (fun i => k ≤ i.val)).image f)) = Active f k := by
    ext; simp [Active]
  have memD (i : Fin t) (S : Finset (Fin t)) : @decide (i∈S) (Classical.propDecidable _) = decide (i∈S) :=
    congrArg (@decide (i∈S)) (Subsingleton.elim _ _)
  have hactive : ∀ k, (Active (fun i => (row i).val) k).card + (Active (fun i => (var i).val) k).card ≤ w := by
    intro k
    simpa only [newActive] using hw k
  obtain ⟨start,finals,edge,recog,degree⟩ := diagram row var sign hactive
  refine ⟨⟨start,finals,edge,?_,edge_total edge degree⟩,?_⟩
  · simpa only [Feas,Accepts,memD] using recog
  obtain ⟨C,outs,fan,rb,output,neg,bound,ok⟩ := compileThresholds m start finals edge degree
  refine ⟨C,outs,fan,rb,output,neg,bound,?_⟩
  intro X l
  have h := (ok X l).trans ((reach_accept finals edge X start l.val).trans
    ((show (∃ S ⊆ X, Accepts start finals edge S ∧ l.val≤S.card) ↔ ∃ S ⊆ X, Feas row var sign S ∧ l.val≤S.card by simp only [recog]).trans (score_iff row var sign X l.val).symm))
  have newScore : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable; (Finset.univ : Finset (Fin n → Bool)).sup (fun s => ((X.filter (fun i => s (var i)=sign i)).image row).card)) = Score row var sign X := by
    apply Finset.sup_congr (by ext; simp)
    intro s _
    apply congrArg Finset.card
    ext; simp
  simpa only [memD,newScore] using h
