import Mathlib

namespace PEqualNP.BoxFallOrder

variable {X J : Type} [SemilatticeInf X]

/-- The last tap in time is at the head. Each interval has an attainable lower and upper endpoint. -/
def follows (a b c d : J → X) (js : List J) : X → Prop :=
  List.rec (motive := fun _ => X → Prop) (fun _ => True)
    (fun j _ prev x => ∃ u v, prev u ∧ u ≤ v ∧ v ≤ x ∧
      a j ≤ u ∧ u ≤ b j ∧ c j ≤ v ∧ v ≤ d j) js

def localOK (a b c d : J → X) (x : X) (j : J) : Prop :=
  a j ≤ b j ∧ a j ≤ d j ∧ c j ≤ d j ∧ a j ≤ x ∧ c j ≤ x

def compatible (a b c d : J → X) (late early : J) : Prop :=
  a early ≤ b late ∧ a early ≤ d late ∧ c early ≤ b late ∧ c early ≤ d late

theorem criterion (a b c d : J → X) (js : List J) (x : X) :
    follows a b c d js x ↔
      (∀ j ∈ js, localOK a b c d x j) ∧ js.Pairwise (compatible a b c d) := by
  induction js generalizing x with
  | nil => simp [follows]
  | cons j js ih =>
    constructor
    · rintro ⟨u,v,old,uv,vx,au,ub,cv,vd⟩
      obtain ⟨good,pairs⟩ := (ih u).mp old
      refine ⟨?_,List.pairwise_cons.mpr ⟨?_,pairs⟩⟩
      · intro k mem
        rcases List.mem_cons.mp mem with eq | tail
        · subst k
          exact ⟨au.trans ub,au.trans (uv.trans vd),cv.trans vd,
            au.trans (uv.trans vx),cv.trans vx⟩
        · obtain ⟨h₁,h₂,h₃,ak,ck⟩ := good k tail
          exact ⟨h₁,h₂,h₃,ak.trans (uv.trans vx),ck.trans (uv.trans vx)⟩
      · intro k mem
        obtain ⟨_,_,_,ak,ck⟩ := good k mem
        exact ⟨ak.trans ub,ak.trans (uv.trans vd),ck.trans ub,ck.trans (uv.trans vd)⟩
    · rintro ⟨good,pairs⟩
      obtain ⟨cross,tail⟩ := List.pairwise_cons.mp pairs
      obtain ⟨ab,ad,cd,ax,cx⟩ := good j List.mem_cons_self
      let v := x ⊓ d j
      let u := v ⊓ b j
      refine ⟨u,v,(ih u).mpr ⟨?_,tail⟩,inf_le_left,inf_le_left,
        le_inf (le_inf ax ad) ab,inf_le_right,le_inf cx cd,inf_le_right⟩
      intro k mem
      obtain ⟨h₁,h₂,h₃,ak,ck⟩ := good k (List.mem_cons_of_mem _ mem)
      obtain ⟨kb,kd,lb,ld⟩ := cross k mem
      exact ⟨h₁,h₂,h₃,le_inf (le_inf ak kd) kb,le_inf (le_inf ck ld) lb⟩

/-- Forgetting the named sequence gives the usual numerical forced-packing predicate. -/
def pack (a b c d : J → X) (t : Nat) : X → Prop :=
  Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧
      a j ≤ u ∧ u ≤ b j ∧ c j ≤ v ∧ v ≤ d j) t

theorem lengths (a b c d : J → X) (t : Nat) (x : X) :
    pack a b c d t x ↔ ∃ js : List J, js.length=t ∧
      (∀ j ∈ js, localOK a b c d x j) ∧ js.Pairwise (compatible a b c d) := by
  have trace (l : Nat) (y : X) : pack a b c d l y ↔
      ∃ js : List J, js.length=l ∧ follows a b c d js y := by
    induction l generalizing y with
    | zero => simp [pack,follows]
    | succ l ih =>
      constructor
      · rintro ⟨u,v,j,prev,uv,vy,a₁,b₁,c₁,d₁⟩
        obtain ⟨js,sz,tr⟩ := (ih u).mp prev
        exact ⟨j::js,by simp [sz],u,v,tr,uv,vy,a₁,b₁,c₁,d₁⟩
      · rintro ⟨js,sz,tr⟩
        cases js with
        | nil => simp at sz
        | cons j js =>
          obtain ⟨u,v,prev,uv,vy,a₁,b₁,c₁,d₁⟩ := tr
          exact ⟨u,v,j,(ih u).mpr ⟨js,by simpa using sz,prev⟩,uv,vy,a₁,b₁,c₁,d₁⟩
  simpa only [criterion] using trace t x

section Graph

variable {n : Nat}

noncomputable def startMask (D : Fin n → Fin n → Prop) (j : Fin n) : Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun k => k≠j ∧ ¬ D k j)

theorem graph (D : Fin n → Fin n → Prop) (x : Finset (Fin n)) (t : Nat) :
    pack (fun _ => ∅) (startMask D) (fun j => {j}) (fun _ => Finset.univ) t x ↔
      ∃ js : List (Fin n), js.length=t ∧ (∀ j ∈ js, j∈x) ∧
        js.Pairwise (fun later earlier => earlier≠later ∧ ¬ D earlier later) := by
  classical
  rw [lengths]
  have rel : compatible (fun _ => ∅) (startMask D) (fun j => {j}) (fun _ => Finset.univ) =
      (fun later earlier => earlier≠later ∧ ¬ D earlier later) := by
    funext late early
    apply propext
    simp [compatible,startMask]
  simp [localOK,rel]

end Graph

end PEqualNP.BoxFallOrder
