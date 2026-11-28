import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46220

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277075688 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0800404280040944#64 ++ 0x102001010a001025#64 ++ 0xf414c0c7824c7ffe#64 ++ 0xf7d053031e0931ff#64 : BitVec 256),
   (0x700103190491a4a0#64 ++ 0x01c0040c64124692#64 ++ 0xef2b07398db3a4fd#64 ++ 0xefbcac1ce636ce93#64 : BitVec 256),
   (0x204c182c31c2c609#64 ++ 0x20813060b0c70b18#64 ++ 0x5ecc383e71c3c72b#64 ++ 0xdd7b30e0f9c70f1c#64 : BitVec 256),
   (0x40b02d805e037032#64 ++ 0x4502c0b601780dc0#64 ++ 0x3ff03fc07e03f827#64 ++ 0xbcffc0ff01f80fe0#64 : BitVec 256),
   (0x80fe80006b680003#64 ++ 0x8603fa0001ada000#64 ++ 0xfcffc0007ffc001f#64 ++ 0x83f3ff0001fff000#64 : BitVec 256),
   (0x01fff6f780000003#64 ++ 0xf807ffdbde000000#64 ++ 0xfdffffff80000000#64 ++ 0x7ff7fffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80000000 0x7ff7fffffe000000

def z1 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c7824c7ffe 0xf7d053031e0931ff

def z2 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71c3c72b 0xdd7b30e0f9c70f1c

def z3 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e03f827 0xbcffc0ff01f80fe0

def z4 : W := mkw 0x49fffff7de077977 0xfd27ffffdf781de5 0xfffffffffe4fffff 0xfffffffffff93fff

def z5 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db3a4fd 0xefbcac1ce636ce93

def z6 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc001f 0x83f3ff0001fff000

def z7 : W := mkw 0x604c192c7fc3f639 0x25813064b1ff0fd8 0x5ecc383e7fc3ff2f 0xdd7b30e0f9ff0ffc

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000001800024e0 0x6400000006000093

def z9 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xf4d4c000724c001e 0x83d3530001c93000

def z10 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0xfcffc0c7fffc7fff 0xf7f3ff031ffff1ff

def z11 : W := mkw 0xc0fead807f6b7033 0xc703fab601fdadc0 0xffffffc07ffff83f 0xbfffffff01ffffe0

def z12 : W := mkw 0x01fef4e680000003 0xf807fbd39a000000 0xfcfff8c600000000 0x13f3ffe318000000

def z13 : W := mkw 0x0000404280000000 0x100001010a000000 0xc004c00780000000 0x430013001e000000

def z14 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c7ffe 0xfff7fffffe0931ff

def z15 : W := mkw 0x2000080831c2c608 0x0080002020c70b18 0x0200000071c3c72b 0x8008000001c70f1c

def z16 : W := mkw 0x0000404280000000 0x100001010a000000 0xf414c0c7824c001e 0xf7d053031e093000

def z17 : W := mkw 0x2800586e9086cf4c 0x30a00161ba421b3d 0x020038ff8003ffe0 0x7c0800e3fe000fff

def z18 : W := mkw 0x0800404280040944 0x102001010a001025 0x8000c001800c00d0 0x0200030006003003

def z19 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x08eb00007db00001 0x0023ac0001f6c000

def z20 : W := mkw 0xa0fe982c7beac60b 0xa683fa60b1efab18 0xfefff83e7fffc73f 0xdffbffe0f9ffff1c

def z21 : W := mkw 0x014f923500000001 0xa8053e48d4000000 0x000b003800000000 0x00002c00e0000000

def z22 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x09eb3f3800000000 0x0827acfce0000000

def z23 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x03003fc00003f820 0x3c0c00ff00000fe0

def z24 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffffc001f 0xfff7fffffffff000

def z25 : W := mkw 0x284c586eb1c6cf4d 0x30a13161bac71b3d 0xfedcf8fff3cfffff 0xfffb73e3ffcf3fff

def z26 : W := mkw 0x60fc3dac7fc3f63b 0x6583f0f6b1ff0fd8 0x7ffc3ffe7fc3ff2f 0xfdfff0fff9ff0ffc

def z27 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff82007826 0xfff7fffffe0801e0

def z28 : W := mkw 0x0800404280040944 0x102001010a001025 0x1014c0c6024c5b02 0x104053031809316c

def z29 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0b2b07380db38001 0x082cac1ce036ce00

def z30 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfedcf83e73cfc73f 0xdffb73e0f9cf3f1c

def z31 : W := mkw 0xf0ff83196ff9a4a3 0x87c3fe0c65bfe692 0xffffc739ffffa4ff 0xefffff1ce7fffe93

def z32 : W := mkw 0x00b000004a000002 0x0402c00001280000 0x3cf000007e000007 0x80f3c00001f80000

def z33 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffff24c0002 0x7ff7ffffffc93000

def z34 : W := mkw 0x60b02d887fc3f63a 0x4582c0b621ff0fd8 0x3ff03fc07fc3ff2f 0xbcffc0ff01ff0ffc

def z35 : W := mkw 0x3001021900908480 0x00c0040864024212 0xed2b073981b004d8 0x6fb4ac1ce606c013

def z36 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003fff80000000 0x7c0400fffe000000

def z37 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0ac8383871838001 0x082b20e0e1c60e00

def z38 : W := mkw 0x40b02d8014037032 0x4102c0b600500dc0 0x3ff03fc00003f820 0x3cffc0ff00000fe0

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400000000000428 0xc510000000000010

def z40 : W := mkw 0x2800080831c6cf4c 0x00a0002020c71b3d 0x0200000073cfffff 0x8008000001cf3fff

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x341000c002007826 0xb4d04003000801e0

def z42 : W := mkw 0x70b12f995e93f4b2 0x45c2c4be657a4fd2 0x3ffb3ff87fb3f827 0xbcffecffe1fecfe0

def z43 : W := mkw 0x204c102c21c08609 0x20813040b0870218 0x400c003e01c00708 0x41003000f807001c

def z44 : W := mkw 0x40b025804e013032 0x4502c096013804c0 0x213007c00e003804 0x2084c01f003800e0

def z45 : W := mkw 0x2000000800808400 0x0080000020020210 0x4e08003801838429 0xcd382000e0060e10

def z46 : W := mkw 0x704d1b3d35d3e6a9 0x21c1346cf4d74f9a 0xffef3f3ffdf3e7ff 0xffffbcfcfff7cf9f

def z47 : W := mkw 0x7000090835d3e6a8 0x01c0002420d74f9a 0x020000007df3e7ff 0x8008000001f7cf9f

def z48 : W := mkw 0xa0fe982c7beac60b 0xa683fa60b1efab18 0x0aeb38387db38001 0x082bace0e1f6ce00

def z49 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x10d4c0007ffc001f 0x8043530001fff000

def z50 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc00000000000 0x03f3ff0000000000

def z51 : W := mkw 0x0800404280040944 0x102001010a001025 0x341000c782007fe6 0xf4d040031e0801ff

def z52 : W := mkw 0x21fffeffb1c2c60b 0xf887fffbfec70b18 0xfffffffff1c3c72b 0xffffffffffc70f1c

def z53 : W := mkw 0x00b0248000000002 0x4002c09200000000 0x3df03fc000000000 0x3cf7c0ff00000000

def z54 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398003a4e0 0x6fbcac1ce6000e93

def z55 : W := mkw 0x21fffeffb1c2c60b 0xf887fffbfec70b18 0xfffffffff1838001 0x7fffffffffc60e00

def z56 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x0200383e0003c720 0x5c0800e0f8000f1c

def z57 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdffff3800000000 0x0bf7fffce0000000

def z58 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x13d03fc07203f822 0x3c4f40ff01c80fe0

def z59 : W := mkw 0x0800404280040944 0x102001010a001025 0xc004c007804c07d8 0x430013001e01301f

def z60 : W := mkw 0x40b12f915e037032 0x4502c4be45780dc0 0xfffb3ff9fe03f827 0xffffecffe7f80fe0

def z61 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0300073800038000 0x080c001ce0000e00

def z62 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x7ff43fc67e43ff2f 0xfdffd0ff19f90ffc

def z63 : W := mkw 0x284c506ea1c48f4d 0x30a13141ba87123d 0xc00cc03f81cc07d8 0x43003300fe07301f

def z64 : W := mkw 0x48b06dc2de077976 0x5522c1b70b781de5 0xfff4ffc7fe4fffff 0xffffd3ff1ff93fff

def z65 : W := mkw 0x0800404280040944 0x102001010a001025 0x540400c780407fea 0xf55010031e0101ff

def z66 : W := mkw 0x41fffff794037033 0xf907ffffde500dc0 0xffffffff8003f820 0x7ffffffffe000fe0

def z67 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0xa033c0000e3c0014 0x0280cf000038f000

def z68 : W := mkw 0x804e800021680001 0x82013a000085a000 0xc00fc00001fc0018 0x03003f000007f000

def z69 : W := mkw 0x004d123500000001 0x20013448d4000000 0xfdef3f3f80000000 0x7ff7bcfcfe000000

def z70 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0xc10fffff80000000 0x7f043ffffe000000

def z71 : W := mkw 0x88fe80006b6c0947 0x8623fa0001adb025 0xfcffc0007ffc7fff 0x83f3ff0001fff1ff

def z72 : W := mkw 0x09b3e6d380040946 0xd826cf9b4e001025 0xf537c7c7824c7ffe 0xf7d4df1f1e0931ff

def z73 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03f007e038007 0x88ffc0fc01f80e00

def z74 : W := mkw 0x0800404280040944 0x102001010a001025 0x000000c780007fe0 0x740000031e0001ff

def z75 : W := mkw 0x00002c8010025010 0x400000b200400940 0x000038c000005800 0x100000e300000160

def z76 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x030007398003a4e0 0x6c0c001ce6000e93

def z77 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x10d4c000724c0002 0x0043530001c93000

def z78 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0xf4d4c0c7f24c7ffe 0xf7d353031fc931ff

def z79 : W := mkw 0x0000080010024000 0x0000002000400900 0x1ec038007003c023 0x9c7b00e001c00f00

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c000024c001e 0x83d0530000093000

def z81 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x09eb3fff80000000 0x7c27acfffe000000

def z82 : W := mkw 0x880000006b6c0944 0x0620000001adb025 0x000000007ffc7fff 0x8000000001fff1ff

def z83 : W := mkw 0x60003dac1483f638 0x618000f6b0520fd8 0x03003ffe0003ff20 0x7c0c00fff8000ffc

def z84 : W := mkw 0x48006dc294077974 0x512001b70a501de5 0xf714ffc7824ffffe 0xffdc53ff1e093fff

def z85 : W := mkw 0x71fff7ff8491a4a3 0xf9c7ffdffe124692 0xffffffff8db3a4fd 0xfffffffffe36ce93

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b00000db0001d 0x83b0ac000036c000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc3fc0000ffc001f 0x83f0ff00003ff000

def z88 : W := mkw 0x0001021100000000 0x0000040844000000 0xed2b0739800024fc 0xefb4ac1ce6000093

def z89 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0x10d4c00000000000 0x0043530000000000

def z90 : W := mkw 0x004c182431424209 0x2001306090c50908 0x10c4380670404302 0x104310e019c1010c

def z91 : W := mkw 0x710177ff8491a4a0 0x79c405dffe124692 0xef2b3fff8db3a4fd 0xffbcacfffe36ce93

def z92 : W := mkw 0x204d1a3d31c2c609 0x20813468f4c70b18 0xffef3f3ff1c3c72b 0xffffbcfcffc70f1c

def z93 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0x020000000db3a4fd 0x800800000036ce93

def z94 : W := mkw 0x710177ff8491a4a0 0x79c405dffe124692 0x03003fff8003a4e0 0x7c0c00fffe000e93

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400000000004022 0x9450000000000100

def z96 : W := mkw 0x50010311041120a0 0x0140040c44104482 0xa12307018c3020d4 0x22848c1c0630c083

def z97 : W := mkw 0x01b3e6d380000002 0xd806cf9b4e000000 0xa133c7c180000000 0x2284cf1f06000000

def z98 : W := mkw 0x89fff6f7eb6c0947 0xfe27ffdbdfadb025 0xfdfffffffffc7fff 0xfff7fffffffff1ff

def z99 : W := mkw 0x01fef4e680000003 0xf807fbd39a000000 0x10d4f8c600000000 0x104353e318000000

def z100 : W := mkw 0x0000080010024000 0x0000002000400900 0x0ac0380070038001 0x082b00e001c00e00

def z101 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff804c07d8 0x7ff7fffffe01301f

def z102 : W := mkw 0x010176f780000000 0x780405dbde000000 0xf514ffff80000000 0x7fd453fffe000000

def z103 : W := mkw 0x0800000000040944 0x0020000000001025 0x00000000024c7ffe 0x80000000000931ff

def z104 : W := mkw 0x004c080031424001 0x0001302000c50900 0x5ecc380071c3c02b 0x9d7b30e001c70f00

def z105 : W := mkw 0x21ffbebd31c2c60b 0xe887fefaf4c70b18 0x0beb3f3871838001 0x082facfce1c60e00

def z106 : W := mkw 0x010074e680000000 0x780401d39a000000 0x000038c600000000 0x100000e318000000

def z107 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0be03f007c038001 0x082f80fc01f00e00

def z108 : W := mkw 0x58014353841529e4 0x1160050d4e1054a7 0xa133c7c18e3c38d4 0x2284cf1f0638f0e3

def z109 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0x10d4c0c6724c5b02 0x1043530319c9316c

def z110 : W := mkw 0x600009087fc3f638 0x0580002421ff0fd8 0x020000007fc3ff2f 0x8008000001ff0ffc

def z111 : W := mkw 0x00b024804a000002 0x4402c09201280000 0x3df03fc07e000007 0xbcf7c0ff01f80000

def z112 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0xfcffc007fffc07df 0xc3f3ff001ffff01f

def z113 : W := mkw 0x41fffff7de037033 0xfd07ffffdf780dc0 0xfffffffffc038001 0x7ffffffffff00e00

def z114 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x50cc383e71c0470a 0x514330e0f9c7011c

def z115 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x2f2007398c03a4e5 0xecbc801ce6300e93

def z116 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xc9efff3f80000000 0x4b27bffcfe000000

def z117 : W := mkw 0x71fff7ff8491a4a3 0xf9c7ffdffe124692 0xffffffff8db38001 0x7ffffffffe36ce00

def z118 : W := mkw 0x0800404280040944 0x102001010a001025 0x5414c0c6024c5f2a 0xd55053031809317c

def z119 : W := mkw 0x204c102c21c08609 0x20813040b0870218 0x5ccc003e71c0070b 0xc1733000f9c7001c

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002007826 0x80000000000801e0

def z121 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c7804c07d8 0x77d053031e01301f

def z122 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xa9fbfff980000000 0x2aa7efffe6000000

def z123 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x00c0000070000000 0x0003000001c00000

def z124 : W := mkw 0x01fef4e680000003 0xf807fbd39a000000 0x5cdcf8fe00000000 0x5d7373e3f8000000

def z125 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0xa133ffff80000000 0x7e84cffffe000000

def z126 : W := mkw 0x00fe800021400003 0x8003fa0000850000 0xfcffc00071c0000b 0x83f3ff0001c70000

def z127 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x10d038c072005802 0x104340e301c80160

def z128 : W := mkw 0x804e800021680001 0x82013a000085a000 0xdccfc00071fc001b 0x83733f0001c7f000

def z129 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x1fc03fc07003f823 0xbc7f00ff01c00fe0

def z130 : W := mkw 0x800000006b680000 0x0600000001ada000 0xec2b00007ffc001f 0x83b0ac0001fff000

def z131 : W := mkw 0x800000006b680000 0x0600000001ada000 0x000000007ffc001f 0x8000000001fff000

def z132 : W := mkw 0x004c000021400001 0x0001300000850000 0x5ccc000071c0000b 0x8173300001c70000

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x540400060040472a 0xd55010001801011c

def z134 : W := mkw 0x3001021900908480 0x00c0040864024212 0xc00b003981b004d8 0x43002c00e606c013

def z135 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0xff3fc7ff8fffffff 0xfffcff1ffe3fffff

def z136 : W := mkw 0x400009005e037030 0x0500002401780dc0 0x2f2007007e03f827 0xacbc801c01f80fe0

def z137 : W := mkw 0x0800404280040944 0x102001010a001025 0x0010c0c0020c1800 0x0000430300083060

def z138 : W := mkw 0xf0ff83196ff9a4a3 0x87c3fe0c65bfe692 0xefeb0739fdb3a4fd 0xefbfac1ce7f6ce93

def z139 : W := mkw 0x50b12f915e1370b2 0x4542c4be45784dc2 0xbff33fc1fe33f8f7 0xbeffccff07f8cfe3

def z140 : W := mkw 0x01ffe6d380000003 0xd807ff9b4e000000 0xfdffc7c180000000 0x23f7ff1f06000000

def z141 : W := mkw 0x884ec042a16c0945 0x92213b010a85b025 0xf41fc0c783fc7ffe 0xf7d07f031e0ff1ff

def z142 : W := mkw 0x0800000000040944 0x0020000000001025 0x00000000020c38d4 0x00000000000830e3

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4000001800024fc 0xe790000006000093

def z144 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1acc383e71c3c303 0x186b30e0f9c70f0c

def z145 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0ac8383e7183c721 0x5c2b20e0f9c60f1c

def z146 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xe13fc7ff80000000 0x6384ff1ffe000000

def z147 : W := mkw 0x01b3e6d380000002 0xd806cf9b4e000000 0xbdf3ffc180000000 0x3ef7cfff06000000

def z148 : W := mkw 0x70b12f995e93f4b2 0x45c2c4be657a4fd2 0x3ff03ff9fe03fce7 0xfcffc0ffe7f80ff3

def z149 : W := mkw 0x21ffbebd31c2c60b 0xe887fefaf4c70b18 0x5fef3f3e71c3c72b 0xdd7fbcfcf9c70f1c

def z150 : W := mkw 0x40b025804e013032 0x4502c096013804c0 0x3df03fc00e003804 0x3cf7c0ff003800e0

def z151 : W := mkw 0x204c102c21c08609 0x20813040b0870218 0x5ccc383e01c00708 0x5d7330e0f807001c

def z152 : W := mkw 0x70b12f995e93f4b2 0x45c2c4be657a4fd2 0xfffb3ff9ffb3fcff 0xffffecffe7fecff3

def z153 : W := mkw 0x70012f991493f4b0 0x41c004be64524fd2 0xef2b3ff98db3fcfd 0xffbcacffe636cff3

def z154 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x3cfb00007fb00007 0x80f3ec0001fec000

def z155 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff800024fc 0xfff7fffffe000093

def z156 : W := mkw 0x2000080831c2c608 0x0080002020c70b18 0x0200000071838001 0x0008000001c60e00

def z157 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07c038001 0x3cffc0ff01f00e00

def z158 : W := mkw 0x41b3efd3de037032 0xdd06cfbf4f780dc0 0xbff3ffc1fe03f827 0xbeffcfff07f80fe0

def z159 : W := mkw 0x704d1b3d35d3e6a9 0x21c1346cf4d74f9a 0x0beb3f387db38001 0x082facfce1f6ce00

def z160 : W := mkw 0x20fc3cac7bc2d61b 0x6483f0f2b1ef0b58 0x5edc38fe73c3df2b 0xdd7b70e3f9cf0f7c

def z161 : W := mkw 0x4000090014037030 0x0100002400500dc0 0x020000000003f820 0x0008000000000fe0

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x540400000040000a 0x8150100000010000

def z163 : W := mkw 0x08b04042ca040946 0x1422c1010b281025 0xfcf4c0c7fe4c7fff 0xf7f3d3031ff931ff

def z164 : W := mkw 0xa04e982c31eac609 0xa2813a60b0c7ab18 0xdecff83e71ffc73b 0xdf7b3fe0f9c7ff1c

def z165 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc001fffc24ff 0xe7f3ff0007fff093

def z166 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x4ec8383871838429 0xcd3b20e0e1c60e10

def z167 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8040472a 0xfff7fffffe01011c

def z168 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0c07ffc783f 0xb7f3ff0301fff1e0

def z169 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff824c001e 0xfff7fffffe093000

def z170 : W := mkw 0x80feac807b6a5013 0xc603fab201eda940 0xfcfff8c07ffc581f 0x93f3ffe301fff160

def z171 : W := mkw 0x304d1a3d31d2c689 0x20c13468f4c74b1a 0xdecf383ff1f3c7fb 0xdf7b3ce0ffc7cf1f

def z172 : W := mkw 0x71b3e7db8491a4a2 0xd9c6cf9f6e124692 0xef3bc7f98db3a4fd 0xefbcef1fe636ce93

def z173 : W := mkw 0x204c182c1082c609 0x20813060b0420b18 0x5ecc383e0003c720 0x5d7b30e0f8000f1c

def z174 : W := mkw 0xf0ff83196ff9a4a3 0x87c3fe0c65bfe692 0x0beb07387db38001 0x082fac1ce1f6ce00

def z175 : W := mkw 0x0800404280040944 0x102001010a001025 0x1014c0c6024c7ffe 0x90405303180931ff

def z176 : W := mkw 0xc8feedc2ff6f7977 0xd723fbb70bfdbde5 0xffffffc7ffffffff 0xffffffff1fffffff

def z177 : W := mkw 0x41ffbfb55e037033 0xed07fefed5780dc0 0x3ffb3ff87e03f827 0xbcffecffe1f80fe0

def z178 : W := mkw 0x09fef4e680040947 0xf827fbd39a001025 0xf4d4f8c7824c7ffe 0xf7d353e31e0931ff

def z179 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1fe03f007c03c023 0x9c7f80fc01f00f00

def z180 : W := mkw 0x51fff7f7841120a3 0xf947ffdfde104482 0xfdffffff8c3020d4 0x7ff7fffffe30c083

def z181 : W := mkw 0x00b0248000000002 0x4002c09200000000 0x3df03fc002007826 0xbcf7c0ff000801e0

def z182 : W := mkw 0x0800000000040944 0x0020000000001025 0x0000000000007fe0 0x00000000000001ff

def z183 : W := mkw 0x704d1b3d35d3e6a9 0x21c1346cf4d74f9a 0xefeb3f39fdb3a4fd 0xefbfacfce7f6ce93

def z184 : W := mkw 0x004c182431424209 0x2001306090c50908 0x00c0380070000000 0x000300e001c00000

def z185 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfffb3fc07fb3f83f 0xbfffecff01fecfe0

def z186 : W := mkw 0x40b06dc2de037032 0x5502c1b70b780dc0 0xfff4ffc7fe03f827 0xffffd3ff1ff80fe0

def z187 : W := mkw 0x0800000000040944 0x0020000000001025 0x00000000024c5b02 0x000000000009316c

def z188 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07380db3801d 0x8bbcac1ce036ce00

def z189 : W := mkw 0xa0fe982c7beac60b 0xa683fa60b1efab18 0x5eef383e7df3c72b 0xdd7bbce0f9f7cf1c

def z190 : W := mkw 0x0000080010024000 0x0000002000400900 0x10c0380070004002 0x104300e001c00100

def z191 : W := mkw 0x704d031925d1a4a1 0x01c1340c64974692 0xffef0739fdf3a4ff 0xefffbc1ce7f7ce93

def z192 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xc20b00398db3a4fd 0xc3082c00e636ce93

def z193 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x18ffc0007ffc0003 0x0063ff0001fff000

def z194 : W := mkw 0x60fc3dac7fc3f63b 0x6583f0f6b1ff0fd8 0x0be83f387d838001 0x082fa0fce1f60e00

def z195 : W := mkw 0x0000000021400000 0x0000000000850000 0x0000000071c0000b 0x8000000001c70000

def z196 : W := mkw 0x09b3e6d380040946 0xd826cf9b4e001025 0xa133c7c1820c38d4 0x2284cf1f060830e3

def z197 : W := mkw 0x084c506680040945 0x302131419a001025 0xfcdcf8ff824c7ffe 0xfff373e3fe0931ff

def z198 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0x4e0800380db3a4fd 0xcd382000e036ce93

def z199 : W := mkw 0x010166d380000000 0x5804059b4e000000 0x010007c180000000 0x2004001f06000000

def z200 : W := mkw 0x400009005e037030 0x0500002401780dc0 0x020000007e03f827 0x8008000001f80fe0

def z201 : W := mkw 0x41fffff7de037033 0xfd07ffffdf780dc0 0xfffffffffe03f827 0xfffffffffff80fe0

def z202 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x4acc383e71c38709 0x492b30e0f9c70e1c

def z203 : W := mkw 0x0800404280040944 0x102001010a001025 0xa010c0c1820c38d4 0x22804303060830e3

def z204 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff820c38d4 0x7ff7fffffe0830e3

def z205 : W := mkw 0x0800404280040944 0x102001010a001025 0x000000c600005b00 0x100000031800016c

def z206 : W := mkw 0x004c182431424209 0x2001306090c50908 0x1ec438067043c323 0x9c7b10e019c10f0c

def z207 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x12c4383e7043c722 0x5c4b10e0f9c10f1c

def z208 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x030007398db3a4fd 0xec0c001ce636ce93

def z209 : W := mkw 0x284c506ea1c48f4d 0x30a13141ba87123d 0xf41cc0ff83cc7ffe 0xf7d07303fe0f31ff

def z210 : W := mkw 0x31fff6ff80908483 0xf8c7ffdbfe024212 0xfdffffff81b004d8 0x7ff7fffffe06c013

def z211 : W := mkw 0x71ffffffb5d3e6ab 0xf9c7fffffed74f9a 0xfffffffffdf3e7ff 0xfffffffffff7cf9f

def z212 : W := mkw 0x80ff82116b680003 0x8603fe0845ada000 0xfdffc739fffc001f 0xeff7ff1ce7fff000

def z213 : W := mkw 0x0001021100000000 0x0000040844000000 0xed2b073980000000 0x6fb4ac1ce6000000

def z214 : W := mkw 0x0800000000040944 0x0020000000001025 0xf414c000024c7ffe 0x83d05300000931ff

def z215 : W := mkw 0x09fef4e680040947 0xf827fbd39a001025 0x10d4f8c6024c5b02 0x104353e31809316c

def z216 : W := mkw 0x004c102400000001 0x2001304090000000 0x5ccc383e00000000 0x5d7330e0f8000000

def z217 : W := mkw 0x014ed06680000001 0xb8053b419a000000 0x0004c00600000000 0x0000130018000000

def z218 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfeef383e7df3c73f 0xdffbbce0f9f7cf1c

def z219 : W := mkw 0x70010b195e93f4b0 0x05c0042c657a4fd2 0xef2b0739ffb3fcff 0xefbcac1ce7fecff3

def z220 : W := mkw 0xf0fe81086ff9a4a3 0x87c3fa0421bfe692 0xfeffc0007fffa4ff 0x83fbff0001fffe93

def z221 : W := mkw 0x21fff6ff80808403 0xf887ffdbfe020210 0xffffffff81838429 0xfffffffffe060e10

def z222 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x3dfb3ff800000000 0x3cf7ecffe0000000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0xa02300000c300014 0x02808c000030c000

def z224 : W := mkw 0xf00001086ff9a4a0 0x07c0000421bfe692 0x020000007fffa4ff 0x8008000001fffe93

def z225 : W := mkw 0x40b001004e012022 0x0502c00401380480 0x3ff007007e03a027 0xacffc01c01f80e80

def z226 : W := mkw 0x01fefce6da025013 0xfc07fbf39b680940 0x10d4f8c672005802 0x104353e319c80160

def z227 : W := mkw 0x40002d805e037030 0x450000b601780dc0 0x03003fc07e03f827 0xbc0c00ff01f80fe0

def z228 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc000024c001e 0x83f3ff0000093000

def z229 : W := mkw 0x29fffeffb1c6cf4f 0xf8a7fffbfec71b3d 0xfffffffff3cfffff 0xffffffffffcf3fff

def z230 : W := mkw 0x004c182410024001 0x2001306090400900 0x5ecc383e7003c023 0xdd7b30e0f9c00f00

def z231 : W := mkw 0x7800414a8495ade4 0x11e001052a1256b7 0xf614c0c78fffffff 0xf7d853031e3fffff

def z232 : W := mkw 0x00b008005a024002 0x0402c02001680900 0x3ef038007e03c027 0x9cfbc0e001f80f00

def z233 : W := mkw 0x80fe98247b6a420b 0xa603fa6091eda908 0x10d4f806724c4302 0x104353e019c9310c

def z234 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c6024c5b1e 0x93d053031809316c

def z235 : W := mkw 0x50010311041120a0 0x0140040c44104482 0xed2b07398c3020d4 0x6fb4ac1ce630c083

def z236 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0x020000000003a4e0 0x0008000000000e93

def z237 : W := mkw 0x2000000800808400 0x0080000020020210 0x0200003800038420 0x4c080000e0000e10

def z238 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x1ec0383e7003c723 0xdc7b00e0f9c00f1c

def z239 : W := mkw 0x80fe90246b680003 0xa603fa4091ada000 0xfcfff83e7ffc001f 0xdff3ffe0f9fff000

def z240 : W := mkw 0x204c102c00808401 0x20813040b0020210 0x5ecc383e01838429 0xdd7b30e0f8060e10

def z241 : W := mkw 0xf1fff7ffeff9a4a3 0xffc7ffdfffbfe692 0xffffffffffffa4ff 0xfffffffffffffe93

def z242 : W := mkw 0x004c182431424209 0x2001306090c50908 0x54c438067040472a 0xd55310e019c1011c

def z243 : W := mkw 0x704d1b3d35d3e6a9 0x21c1346cf4d74f9a 0x5fcc3f3ff1c3e7eb 0xfd7f30fcffc70f9f

def z244 : W := mkw 0x0001021100000000 0x0000040844000000 0x092b073800000000 0x0824ac1ce0000000

def z245 : W := mkw 0x204c080831c2c609 0x0081302020c70b18 0x5ecc000071c3c72b 0x817b300001c70f1c

def z246 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xe03fc0000ffc001c 0x0380ff00003ff000

def z247 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xb1f7ffc780000000 0x32c7dfff1e000000

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000040472a 0x800000000001011c

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z250 : W := mkw 0xa04c182c7beac609 0x26813060b1efab18 0x5ecc383e7fffc73f 0xdd7b30e0f9ffff1c

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x1014c000024c0002 0x0040530000093000

def z252 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c5b02 0x7ff7fffffe09316c

def z253 : W := mkw 0x0000182410024208 0x2000006090400908 0x0000380600004300 0x100000e01800010c

def z254 : W := mkw 0x70b103194e91a4a2 0x05c2c40c653a4692 0xfffb0739ffb3a4ff 0xefffec1ce7fece93

def z255 : W := mkw 0x01feb4a400000003 0xe807fad290000000 0x00c0380000000000 0x000300e000000000

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x2d20070000000000 0x2cb4801c00000000

def z257 : W := mkw 0x014fd27780000001 0xb8053f49de000000 0xc00fc03f80000000 0x43003f00fe000000

def z258 : W := mkw 0x0800404280040944 0x102001010a001025 0x000000c7824c7ffe 0xf40000031e0931ff

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001800004d8 0x4300000006000013

def z260 : W := mkw 0xc0b2a5804e293032 0xc702ca960138a4c0 0xa133c7c00e3c3814 0x2284cf1f0038f0e0

def z261 : W := mkw 0x71fff7ff8491a4a3 0xf9c7ffdffe124692 0xffffffff8003a4e0 0x7ffffffffe000e93

def z262 : W := mkw 0x0000080010024000 0x0000002000400900 0x3ed038c07203f827 0xbcfb40e301c80fe0

def z263 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0xe60000018db3a4fd 0xe79800000636ce93

def z264 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x3df03fc072005802 0x3cf7c0ff01c80160

def z265 : W := mkw 0x68fc7deeffc7ff7f 0x75a3f1f7bbff1ffd 0xfffcffffffcfffff 0xfffff3ffffff3fff

def z266 : W := mkw 0xf04f831925f9a4a1 0x83c13e0c6497e692 0xef2fc7398dffa4fd 0xefbcbf1ce637fe93

def z267 : W := mkw 0x090176f780040944 0x782405dbde001025 0x01003fff80007fe0 0x7c0400fffe0001ff

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b000000000000 0x03b0ac0000000000

def z269 : W := mkw 0x00fc34a400000003 0x6003f0d290000000 0x7dfc3ffe00000000 0x7df7f0fff8000000

def z270 : W := mkw 0x21fffeff9082c60b 0xf887fffbfe420b18 0xffffffff8003c720 0x7ffffffffe000f1c

def z271 : W := mkw 0x81b3e6d3ca280002 0xde06cf9b4f28a000 0xa133c7c18e3c0014 0x2284cf1f0638f000

def z272 : W := mkw 0x0000404280000000 0x100001010a000000 0xa010c0c180000000 0x2280430306000000

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4040007804067fe 0xf7d010001e01019f

def z274 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c08000001800009 0x8130200000060000

def z275 : W := mkw 0x0800404280040944 0x102001010a001025 0xfc3fc0c78ffc7fff 0xf7f0ff031e3ff1ff

def z276 : W := mkw 0x51b3e7d3841120a2 0xd946cf9f4e104482 0xa133c7c18c3020d4 0x2284cf1f0630c083

def z277 : W := mkw 0x704c192c35d3e6a9 0x21c13064b0d74f9a 0x5ecc383e7df3e7ff 0xdd7b30e0f9f7cf9f

def z278 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xcb2b07398db384d9 0x4b2cac1ce636ce13

def z279 : W := mkw 0x40fc3da45e037033 0x6503f0f691780dc0 0x7ffc3ffe7e03f827 0xfdfff0fff9f80fe0

def z280 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc000724c0002 0x03f3ff0001c93000

def z281 : W := mkw 0x604c3dac35c3f639 0x618130f6b0d70fd8 0x5fcc3ffe71c3ff2b 0xfd7f30fff9c70ffc

def z282 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfecc383ff1c3e7ff 0xfffb30e0ffc70f9f

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0000070000003 0x8073000001c00000

def z284 : W := mkw 0x4000010004012020 0x0100000400100480 0x212007000c002004 0x2084801c00300080

def z285 : W := mkw 0x0800000000040944 0x0020000000001025 0xe4000001824c7ffe 0xe7900000060931ff

def z286 : W := mkw 0x20fe982c31c2c60b 0xa083fa60b0c70b18 0xfefff83e71c3c72b 0xdffbffe0f9c70f1c

def z287 : W := mkw 0x88004042eb6c0944 0x162001010badb025 0xf414c0c7fffc7fff 0xf7d053031ffff1ff

def z288 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xab2b07398db3a0d5 0x2aacac1ce636ce83

def z289 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff4ffc07e4ff83f 0xbfffd3ff01f93fe0

def z290 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0be03fc07c03f821 0x3c2f80ff01f00fe0

def z291 : W := mkw 0x304d123d21d08689 0x20c13448f487421a 0xc00f003f81f007d8 0x43003c00fe07c01f

def z292 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x5def3f3e00000000 0x5d77bcfcf8000000

def z293 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3b07f98fb3fcff 0xfffcec1fe63ecff3

def z294 : W := mkw 0x50010311041120a0 0x0140040c44104482 0xaf2307018c33a0f5 0xaebc8c1c0630ce83

def z295 : W := mkw 0x50010311041120a0 0x0140040c44104482 0x01000701800020c0 0x2004001c06000083

def z296 : W := mkw 0xc0b2ad805e2b7032 0xc702cab60178adc0 0xbff3ffc07e3ff837 0xbeffcfff01f8ffe0

def z297 : W := mkw 0x700009085e93f4b0 0x05c00024217a4fd2 0x020000007fb3fcff 0x8008000001fecff3

def z298 : W := mkw 0x0103c25380000000 0x98040f094e000000 0x8003c00180000000 0x02000f0006000000

def z299 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x7edc38fe73c3ff2f 0xfdfb70e3f9cf0ffc

def z300 : W := mkw 0x48006dc294077974 0x512001b70a501de5 0x03003fc78003ffe0 0x7c0c00ff1e000fff

def z301 : W := mkw 0x21fff6ffa1c0860b 0xf887ffdbfe870218 0xfdffffff81c00708 0x7ff7fffffe07001c

def z302 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x11d4ffff80000000 0x7c4753fffe000000

def z303 : W := mkw 0x40b025804e013032 0x4502c096013804c0 0x012007000c000000 0x0004801c00300000

def z304 : W := mkw 0x0800404280040944 0x102001010a001025 0x000000c1800038c0 0x20000003060000e3

def z305 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdfffffffe000007 0xfff7fffffff80000

def z306 : W := mkw 0x0800404280040944 0x102001010a001025 0xe40000c780007ffc 0xf79000031e0001ff

def z307 : W := mkw 0x800000006b680000 0x0600000001ada000 0xf414c0007ffc001f 0x83d0530001fff000

def z308 : W := mkw 0xb04f821921f88481 0x82c13e086487e212 0xc00fc03981fc04d8 0x43003f00e607f013

def z309 : W := mkw 0x0801425380040944 0x102005094e001025 0xfd3fc7ff824c7ffe 0xfff4ff1ffe0931ff

def z310 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0x09eb3f387db00001 0x0827acfce1f6c000

def z311 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x00c0380070000000 0x000300e001c00000

def z312 : W := mkw 0x204c586eb1c2c609 0x30813161bac70b18 0xfedcf8fff1c3c72b 0xfffb73e3ffc70f1c

def z313 : W := mkw 0x094fd27780040945 0xb8253f49de001025 0xc00fc03f804c07d8 0x43003f00fe01301f

def z314 : W := mkw 0x0001425380000000 0x100005094e000000 0xfd3fc7ff80000000 0x7ff4ff1ffe000000

def z315 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xd0dff8ff80000000 0x53437fe3fe000000

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c001824c24fe 0xe7d0530006093093

def z317 : W := mkw 0x0800000000040944 0x0020000000001025 0x00000000004c07d8 0x000000000001301f

def z318 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x5cef00007df0000b 0x8173bc0001f7c000

def z319 : W := mkw 0x204c102c21c08609 0x20813040b0870218 0x540c003e01c0472a 0xd5503000f807011c

def z320 : W := mkw 0x004c000021400001 0x0001300000850000 0x400c000001c00008 0x0100300000070000

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000600004720 0x540000001800011c

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x101000c002005802 0x1040400300080160

def z323 : W := mkw 0x88b2c042ca2c0946 0x9622cb010b28b025 0xa033c0c18e3c38d4 0x2280cf030638f0e3

def z324 : W := mkw 0x40b025804e013032 0x4502c096013804c0 0x3df007c07e003807 0xa0f7c01f01f800e0

def z325 : W := mkw 0x0800404280040944 0x102001010a001025 0xe404c007804c27fc 0xe79013001e01309f

def z326 : W := mkw 0x0800404280040944 0x102001010a001025 0x1014c0c7824c7fe2 0x744053031e0931ff

def z327 : W := mkw 0x0000404280000000 0x100001010a000000 0xf414c0c78040472a 0xf7d053031e01011c

def z328 : W := mkw 0x200008081082c608 0x0080002020420b18 0x020000000003c720 0x0008000000000f1c

def z329 : W := mkw 0x480009005e077974 0x0520002401781de5 0x020000007e4fffff 0x8008000001f93fff

def z330 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff03fc1fe03fcff 0xffffc0ff07f80ff3

def z331 : W := mkw 0x780103190495ade4 0x01e0040c641256b7 0xef2b07398fffffff 0xefbcac1ce63fffff

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000c000007820 0x34000003000001e0

def z333 : W := mkw 0x2800404a80848d44 0x10a001012a021235 0xfe1cc0ff83cfffff 0xfff87303fe0f3fff

def z334 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c1824c38de 0xa3d05303060930e3

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c08003800000000 0x4d302000e0000000

def z336 : W := mkw 0x804e80006b680001 0x86013a0001ada000 0xc00fc0007ffc001f 0x83003f0001fff000

def z337 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0be03f007e03f827 0x882f80fc01f80fe0

def z338 : W := mkw 0x714fd37f8491a4a1 0xb9c53f4dfe124692 0xef2fc73f8db3a4fd 0xefbcbf1cfe36ce93

def z339 : W := mkw 0x01fef4e680000003 0xf807fbd39a000000 0xf4d4f8c780000000 0x77d353e31e000000

def z340 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0xbcf3c0007e3c0017 0x82f3cf0001f8f000

def z341 : W := mkw 0x2000080831c2c608 0x0080002020c70b18 0x4e08003871c3c72b 0xcd382000e1c70f1c

def z342 : W := mkw 0x81fff6f7a1680003 0xfa07ffdbde85a000 0xfdffffff81fc0018 0x7ff7fffffe07f000

def z343 : W := mkw 0x41017ff794037030 0x790405ffde500dc0 0x03003fff8003f820 0x7c0c00fffe000fe0

def z344 : W := mkw 0x800000006b680000 0x0600000001ada000 0x00000000724c0002 0x0000000001c93000

def z345 : W := mkw 0x40b009005e037032 0x0502c02401780dc0 0x3ef000007e03f827 0x80fbc00001f80fe0

def z346 : W := mkw 0x800000006b680000 0x0600000001ada000 0x000000007db00001 0x0000000001f6c000

def z347 : W := mkw 0x804c00006b680001 0x0601300001ada000 0x5ccc00007ffc001f 0x8173300001fff000

def z348 : W := mkw 0x4000010004012020 0x0100000400100480 0x020000000c03a025 0x8008000000300e80

def z349 : W := mkw 0x70012f991493f4b0 0x41c004be64524fd2 0x03003ff98003fce0 0x7c0c00ffe6000ff3

def z350 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x31f03fc07e007806 0x30c7c0ff01f801e0

def z351 : W := mkw 0x71ffffffde93f4b3 0xfdc7ffffff7a4fd2 0xffffffffffb3fcff 0xfffffffffffecff3

def z352 : W := mkw 0x804e800021680001 0x82013a000085a000 0x000b000001b00000 0x00002c000006c000

def z353 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xc30b073981b3a4f8 0x6f0c2c1ce606ce93

def z354 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x03003f0000038000 0x080c00fc00000e00

def z355 : W := mkw 0xf0ff83196ff9a4a3 0x87c3fe0c65bfe692 0xffffc7387fff801f 0x8bffff1ce1fffe00

def z356 : W := mkw 0x4000090014036020 0x0100002400500d80 0x3fe03f007c03e027 0xbcff80fc01f00f80

def z357 : W := mkw 0x0001021100000000 0x0000040844000000 0xed2b07398db0001d 0xefb4ac1ce636c000

def z358 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffdb00001 0x7ff7fffffff6c000

def z359 : W := mkw 0x00b1269100000002 0x4002c49a44000000 0xfdfb3ff980000000 0x7ff7ecffe6000000

def z360 : W := mkw 0xa1fffefffbeac60b 0xfe87fffbffefab18 0xffffffffffffc73f 0xffffffffffffff1c

def z361 : W := mkw 0x0800404280040944 0x102001010a001025 0xd014c0c7824c5fda 0x534053031e09317f

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004000600400708 0x410010001801001c

def z363 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x5cdcc00073cc000b 0x8173730001cf3000

def z364 : W := mkw 0xb0ff82196bf88483 0x86c3fe0865afe212 0xfcffc039fffc04df 0xc3f3ff00e7fff013

def z365 : W := mkw 0x4001031104012020 0x0100040c44100480 0xef2b07398c03a025 0xefbcac1ce6300e80

def z366 : W := mkw 0x40b025804e013032 0x4502c096013804c0 0x2f3007c00e03b825 0xacbcc01f00380ee0

def z367 : W := mkw 0x4000010004012020 0x0100000400100480 0x2f2007000c03a025 0xacbc801c00300e80

def z368 : W := mkw 0x214d7effb1c2c609 0x788535fbfec70b18 0x5fcc3ffff1c3c72b 0xfd7f30ffffc70f1c

def z369 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0xef2b07ff8db3fffd 0xffbcac1ffe36cfff

def z370 : W := mkw 0x00fe902400000003 0xa003fa4090000000 0xfcfff83e00000000 0x5ff3ffe0f8000000

def z371 : W := mkw 0x80fec042eb680003 0x9603fb010bada000 0xfcffc0c7fffc001f 0xf7f3ff031ffff000

def z372 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0x030007ff8003ffe0 0x7c0c001ffe000fff

def z373 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383871c3800b 0x897b30e0e1c70e00

def z374 : W := mkw 0x70b127990491a4a2 0x41c2c49e64124692 0xfffb3ff98db3a4fd 0xffffecffe636ce93

def z375 : W := mkw 0x00fe80004a000003 0x8403fa0001280000 0xfcffc0007e000007 0x83f3ff0001f80000

def z376 : W := mkw 0x50010311041120a0 0x0140040c44104482 0xed2b07018db020dd 0xa3b4ac1c0636c083

def z377 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8db0001d 0xfff7fffffe36c000

def z378 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x08eb00007ffc001f 0x8023ac0001fff000

def z379 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xc8efc0007dfc0019 0x0323bf0001f7f000

def z380 : W := mkw 0x60b02d885e83f432 0x4582c0b6217a0fd0 0x7ff83ff87f83fc2f 0xfdffe0ffe1fe0ff0

def z381 : W := mkw 0x004c000021400001 0x0001300000850000 0xfcef00007df0001f 0x83f3bc0001f7c000

def z382 : W := mkw 0x014d76f780000001 0x780535dbde000000 0x5dcc3fff80000000 0x7d7730fffe000000

def z383 : W := mkw 0x0000404280000000 0x100001010a000000 0xf414c0c780000000 0x77d053031e000000

def z384 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007db00001 0x03f3ff0001f6c000

def z385 : W := mkw 0x004c102421400209 0x2001304090850008 0x0004000600400300 0x000010001801000c

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0xf41000c182007cfe 0xf7d04003060801f3

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x1004000600404302 0x104010001801010c

def z388 : W := mkw 0x00b000004a000002 0x0402c00001280000 0xfcfb00007fb0001f 0x83f3ec0001fec000

def z389 : W := mkw 0x81ffe6d3eb680003 0xde07ff9b4fada000 0xfdffc7c1fffc001f 0xa3f7ff1f07fff000

def z390 : W := mkw 0xc1fffff7ff6b7033 0xff07ffffdffdadc0 0xfffffffffffff83f 0xffffffffffffffe0

def z391 : W := mkw 0x2000000800808400 0x0080000020020210 0x5e0c003e01c3c72b 0xdd783000f8070f1c

def z392 : W := mkw 0x00b02c8010024002 0x4002c0b200400900 0x3ff03fc07003c023 0xbcffc0ff01c00f00

def z393 : W := mkw 0x80fea4806b680003 0xc603fa9201ada000 0xfdffffc07ffc001f 0xbff7ffff01fff000

def z394 : W := mkw 0x40b025804e013032 0x4502c096013804c0 0x353007c00e007826 0xb4d4c01f003801e0

def z395 : W := mkw 0xf0ffaf997ffbf4b3 0xc7c3febe65ffefd2 0xfffffff9fffffcff 0xffffffffe7fffff3

def z396 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0b2b07398db3a4e1 0x6c2cac1ce636ce93

def z397 : W := mkw 0x0000404280000000 0x100001010a000000 0xf414c0c782007826 0xf7d053031e0801e0

def z398 : W := mkw 0x000008005a025010 0x0400002001680940 0x0000000072005802 0x0000000001c80160

def z399 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x12d038c07e03f827 0x904b40e301f80fe0

def z400 : W := mkw 0xa04e902c21e88609 0xa2813a40b087a218 0xc00fc03e01fc0718 0x43003f00f807f01c

def z401 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db38001 0x6fbcac1ce636ce00

def z402 : W := mkw 0x004c000000000001 0x0001300000000000 0x5ccc000000000000 0x0173300000000000

def z403 : W := mkw 0x090176f780040944 0x782405dbde001025 0xf514ffff824c7ffe 0xffd453fffe0931ff

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0380000000000 0x1c7300e000000000

def z405 : W := mkw 0x004c102400000001 0x2001304090000000 0x400c003e00000000 0x41003000f8000000

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000001800020d4 0x2280000006000083

def z407 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0xfcffc0c67ffc5b1f 0x93f3ff0319fff16c

def z408 : W := mkw 0x284c586eb1c6cf4d 0x30a13161bac71b3d 0x5ecc38fff1c3ffeb 0xfd7b30e3ffc70fff

def z409 : W := mkw 0x88b2c042ca2c0946 0x9622cb010b28b025 0xf437c0c78e7c7ffe 0xf7d0df031e39f1ff

def z410 : W := mkw 0xc0fead807f6b7033 0xc703fab601fdadc0 0x0beb3f007db38001 0x082facfc01f6ce00

def z411 : W := mkw 0x48b02d805e077976 0x4522c0b601781de5 0x3ff03fc07e4fffff 0xbcffc0ff01f93fff

def z412 : W := mkw 0x0000102400000000 0x2000004090000000 0x0000383e00000000 0x5c0000e0f8000000

def z413 : W := mkw 0x094fd27780040945 0xb8253f49de001025 0xf41fc0ff824c7ffe 0xf7d07f03fe0931ff

def z414 : W := mkw 0x0001021100000000 0x0000040844000000 0x0100073980000000 0x6c04001ce6000000

def z415 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xa32307398c33a4f4 0x6e8c8c1ce630ce93

def z416 : W := mkw 0x004c182431424209 0x2001306090c50908 0x5ccc380671c0430b 0x917330e019c7010c

def z417 : W := mkw 0x70011b3d1493e6a8 0x21c0046cf4524f9a 0xef2b3f3f8db3e7fd 0xffbcacfcfe36cf9f

def z418 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff2f073f8df3e7ff 0xfffcbc1cfe37cf9f

def z419 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0xef2fc73f8dffa7fd 0xefbcbf1cfe37fe9f

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004c000004c0018 0x0300130000013000

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0xe40000000000001c 0x8390000000000000

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0x5404000600000000 0x5550100018000000

def z423 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0b2b07380db3a4fd 0x882cac1ce036ce93

def z424 : W := mkw 0x0001021100000000 0x0000040844000000 0xa123070180000000 0x22848c1c06000000

def z425 : W := mkw 0x000000004a000000 0x0400000001280000 0x000000007e000007 0x8000000001f80000

def z426 : W := mkw 0x0000000000000000 0x0000000000000000 0x341000c000000000 0x34d0400300000000

def z427 : W := mkw 0x81fef4e6eb680003 0xfe07fbd39bada000 0x10d4f8c6724c0002 0x104353e319c93000

def z428 : W := mkw 0x2000182c31c2c608 0x20800060b0c70b18 0x0200383e71c3c72b 0xdc0800e0f9c70f1c

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x3410000002000006 0x80d0400000080000

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x2400000000002024 0xa490000000000080

def z431 : W := mkw 0x00ff821100000003 0x8003fe0844000000 0xfdffc73980000000 0x6ff7ff1ce6000000

def z432 : W := mkw 0x004c102421400001 0x2001304090850000 0x5ccc383e71c0000b 0xdd7330e0f9c70000

def z433 : W := mkw 0x004c000021400001 0x0001300000850000 0x08c8000071800001 0x0023200001c60000

def z434 : W := mkw 0x0800404280040944 0x102001010a001025 0xe410c0c1820c3cfc 0xe7904303060830f3

def z435 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0x08eb000000000000 0x0023ac0000000000

def z436 : W := mkw 0x60fc3dac7fc3f63b 0x6583f0f6b1ff0fd8 0x3ff83ff87f83f827 0xbcffe0ffe1fe0fe0

def z437 : W := mkw 0x78b16fdbde97fdf6 0x55e2c5bf6f7a5ff7 0xffffffffffffffff 0xffffffffffffffff

def z438 : W := mkw 0x01fffef790024003 0xf807fffbde400900 0xfffffffff003c023 0xffffffffffc00f00

def z439 : W := mkw 0x1001021100100080 0x0040040844004002 0x80030001803000d0 0x02000c000600c003

def z440 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x34d038c072007826 0xb4d340e301c801e0

def z441 : W := mkw 0x00b024804a001012 0x4402c09201280040 0x001000c002001800 0x0000400300080060

def z442 : W := mkw 0x010176f780000000 0x780405dbde000000 0xed2b3fff80000000 0x7fb4acfffe000000

def z443 : W := mkw 0x004c102400000001 0x2001304090000000 0x5ccc383e0040472a 0xdd7330e0f801011c

def z444 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x5604383e0043c72a 0xdd5810e0f8010f1c

def z445 : W := mkw 0x2000000800808400 0x0080000020020210 0x4008003801800408 0x41002000e0060010

def z446 : W := mkw 0x48004942de077974 0x152001250b781de5 0xf614c0c7fe4fffff 0xf7d853031ff93fff

def z447 : W := mkw 0x50010311041120a0 0x0140040c44104482 0x012307000c300000 0x00048c1c0030c000

def z448 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x37103fc00203f826 0xbcdc40ff00080fe0

def z449 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71838001 0x5d7b30e0f9c60e00

def z450 : W := mkw 0x2000000800808400 0x0080000020020210 0xee0800398183a4fd 0xefb82000e6060e93

def z451 : W := mkw 0xa0fe982c7beac60b 0xa683fa60b1efab18 0xfefff8387fff801f 0x8bfbffe0e1fffe00

def z452 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff80007fe0 0x7ff7fffffe0001ff

def z453 : W := mkw 0x79fff7ff8495ade7 0xf9e7ffdffe1256b7 0xffffffff8fffffff 0xfffffffffe3fffff

def z454 : W := mkw 0x01b2e4c280000002 0xd806cb930a000000 0x0010c0c000000000 0x0000430300000000

def z455 : W := mkw 0x00b0000000000002 0x0002c00000000000 0x3cf0000000000000 0x00f3c00000000000

def z456 : W := mkw 0x814fd277a1680001 0xba053f49de85a000 0xc00fc03f81fc0018 0x43003f00fe07f000

def z457 : W := mkw 0xa0fe902c6be8860b 0xa683fa40b1afa218 0xfcffc03e7ffc071f 0xc3f3ff00f9fff01c

def z458 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0xfdffff387ffc001f 0x8bf7fffce1fff000

def z459 : W := mkw 0x004c182431424209 0x2001306090c50908 0x5ccc383e70404302 0x5d7330e0f9c1010c

def z460 : W := mkw 0xc0b02d807f6b7032 0x4702c0b601fdadc0 0x3ff03fc07ffff83f 0xbcffc0ff01ffffe0

def z461 : W := mkw 0x08b06cc2da065956 0x5422c1b30b681965 0xf4d4f8c7f24c7ffe 0xf7d353e31fc931ff

def z462 : W := mkw 0x61ffffffffc3f63b 0xfd87ffffffff0fd8 0xffffffffffc3ff2f 0xffffffffffff0ffc

def z463 : W := mkw 0x2001021900808400 0x0080040864020210 0xef2b073981838429 0xefbcac1ce6060e10

def z464 : W := mkw 0x70b02d885e93f4b2 0x45c2c0b6217a4fd2 0x3ff03fc07fb3fcff 0xbcffc0ff01fecff3

def z465 : W := mkw 0x4000010004012020 0x0100000400100480 0xef2b07000db3a03d 0xafbcac1c0036ce80

def z466 : W := mkw 0x804e800021680001 0x82013a000085a000 0xf41fc00003fc001e 0x83d07f00000ff000

def z467 : W := mkw 0x0800404280040944 0x102001010a001025 0x00000007800007c0 0x400000001e00001f

def z468 : W := mkw 0x60b03dac5e83f63a 0x6582c0f6b17a0fd8 0x3ff03ffe7e03ff27 0xfcffc0fff9f80ffc

def z469 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x3cf4c0007e4c0007 0x80f3d30001f93000

def z470 : W := mkw 0x01b176f780000002 0x7806c5dbde000000 0x3df03fff80000000 0x7cf7c0fffe000000

def z471 : W := mkw 0x2000000800808400 0x0080000020020210 0x0a08003801838001 0x08282000e0060e00

def z472 : W := mkw 0x004c000021400001 0x0001300000850000 0x5ccc000671c0472b 0xd573300019c7011c

def z473 : W := mkw 0x804e800021680001 0x82013a000085a000 0xec2fc0000dfc001d 0x83b0bf000037f000

def z474 : W := mkw 0x80b280006b680002 0x8602ca0001ada000 0xa033c0007ffc001f 0x8280cf0001fff000

def z475 : W := mkw 0x804e800021680001 0x82013a000085a000 0x0004c000004c0000 0x0000130000013000

def z476 : W := mkw 0x3001021900908480 0x00c0040864024212 0x00000039800004c0 0x40000000e6000013

def z477 : W := mkw 0x2000102c00808608 0x20800040b0020218 0x0000003e00000700 0x40000000f800001c

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x741400c602407f2e 0xf5d05003180901fc

def z479 : W := mkw 0x00fea48000000003 0xc003fa9200000000 0xfdffffc000000000 0x3ff7ffff00000000

def z480 : W := mkw 0xd0b383114e3920a2 0x8742ce0c4538e482 0xa133c7018e3c20d4 0x2284cf1c0638f083

def z481 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x2bf03fc07e03b805 0x28afc0ff01f80ee0

def z482 : W := mkw 0x08b06cc2da065956 0x5422c1b30b681965 0x10d4f8c6724c5b02 0x104353e319c9316c

def z483 : W := mkw 0x004c102400000001 0x2001304090000000 0x10c4380600000000 0x104310e018000000

def z484 : W := mkw 0xa0fe88087beac60b 0x8683fa2021efab18 0xfeffc0007fffc73f 0x83fbff0001ffff1c

def z485 : W := mkw 0x0001021100000000 0x0000040844000000 0xc00b003980000000 0x43002c00e6000000

def z486 : W := mkw 0xe0febdac7febf63b 0xe783faf6b1ffafd8 0xfffffffe7fffff3f 0xfffffffff9fffffc

def z487 : W := mkw 0x01fffef7da025013 0xfc07fffbdf680940 0xfdfffffff2005802 0x7ff7ffffffc80160

def z488 : W := mkw 0x3001021900908480 0x00c0040864024212 0xec2b00398db004dd 0xc3b0ac00e636c013

def z489 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0xf714c7ff824ffffe 0xffdc531ffe093fff

def z490 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x2f203fc00c03f825 0xbcbc80ff00300fe0

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010c000020c0014 0x0280430000083000

def z492 : W := mkw 0x014fd27780000001 0xb8053f49de000000 0xdccff83f80000000 0x5f733fe0fe000000

def z493 : W := mkw 0xa00008087beac608 0x0680002021efab18 0x020000007fffc73f 0x8008000001ffff1c

def z494 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x4e08383e0183c729 0xdd3820e0f8060f1c

def z495 : W := mkw 0x0800404280040944 0x102001010a001025 0xa010c0c1824c7ffe 0xa2804303060931ff

def z496 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0x002300000c300000 0x00008c000030c000

def z497 : W := mkw 0x80fe98247b6a420b 0xa603fa6091eda908 0xfcfff8067ffc431f 0x93f3ffe019fff10c

def z498 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c007824c07de 0xc3d053001e09301f

def z499 : W := mkw 0xa0fe80086be88403 0x8683fa0021afa210 0xfeffc0387fff843f 0xcffbff00e1fffe10

def z500 : W := mkw 0x004c000021400001 0x0001300000850000 0x10c4000070400002 0x0043100001c10000

def z501 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x2f2b07380db3a025 0xacbcac1ce036ce80

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400000180000000 0x6790000006000000

def z503 : W := mkw 0x81ffd277eb680003 0xbe07ff49dfada000 0xfcffc03ffffc001f 0xc3f3ff00fffff000

def z504 : W := mkw 0x70b127994e91b4b2 0x45c2c49e653a46d2 0xef3b07f98fb3bcfd 0xefbcec1fe63ecef3

def z505 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x12c4380671c3c72b 0x904b10e019c70f1c

def z506 : W := mkw 0x41b17ff7de037032 0x7d06c5ffdf780dc0 0x3ff03ffffe03f827 0xfcffc0fffff80fe0

def z507 : W := mkw 0x3801425b80948dc4 0x10e005096e025237 0xc00fc03f81fc07d8 0x43003f00fe07f01f

def z508 : W := mkw 0x8002800000280000 0x82000a000000a000 0x8003c000003c0010 0x02000f000000f000

def z509 : W := mkw 0x200008081082c400 0x0080002020420b10 0x5ec838387183c42b 0xdd7b20e0e1c60f10

def z510 : W := mkw 0x00b000004a000002 0x0402c00001280000 0x10d0000072000002 0x0043400001c80000

def z511 : W := mkw 0x400009005e037030 0x0500002401780dc0 0x1ec038007e03f827 0x9c7b00e001f80fe0

def z512 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xedeb3f3980000000 0x6fb7acfce6000000

def z513 : W := mkw 0x600001080481a420 0x0180000420120690 0x6f2807380d83a42d 0xedbca01ce0360e90

def z514 : W := mkw 0x014fd27780000001 0xb8053f49de000000 0xed2fc73f80000000 0x6fb4bf1cfe000000

def z515 : W := mkw 0x41fefde6de037033 0xfd07fbf79b780dc0 0x3ff4ffc67e03f827 0xbcffd3ff19f80fe0

def z516 : W := mkw 0x3001021900908480 0x00c0040864024212 0x000b003801b00000 0x00002c00e006c000

def z517 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3fc7398fffa4ff 0xeffcff1ce63ffe93

def z518 : W := mkw 0x704d133d25d1a6a9 0x21c1344cf497469a 0xef2f073f8df3a7fd 0xefbcbc1cfe37ce9f

def z519 : W := mkw 0x58014353841529e4 0x1160050d4e1054a7 0xf537c7c78e7c7ffe 0xf7d4df1f1e39f1ff

def z520 : W := mkw 0x084c4042a1440945 0x102131010a851025 0xfcdcc0c7f3cc7fff 0xf7f373031fcf31ff

def z521 : W := mkw 0x21fefceeb1c2c60b 0xf887fbf3bac70b18 0x5edcf8fe71c3c72b 0xdd7b73e3f9c70f1c

def z522 : W := mkw 0x704d133d0491a4a1 0x21c1344cf4124692 0xffef3f3f8db3a4fd 0xffffbcfcfe36ce93

def z523 : W := mkw 0x0800404280040944 0x102001010a001025 0xc004c007824c7ffe 0xc30013001e0931ff

def z524 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c7824c5b02 0x77d053031e09316c

def z525 : W := mkw 0x704d1b3d35d3e6a9 0x21c1346cf4d74f9a 0x5fef3f3e7df3c72b 0xdd7fbcfcf9f7cf1c

def z526 : W := mkw 0x48b065c2ce053976 0x5522c1970b3814e5 0xa130c7c18e0c38d4 0x2284c31f063830e3

def z527 : W := mkw 0x0800404280040944 0x102001010a001025 0x3414c0c6024c7b26 0xb4d05303180931ec

def z528 : W := mkw 0xc00009007f6b7030 0x0700002401fdadc0 0x020000007ffff83f 0x8008000001ffffe0

def z529 : W := mkw 0x0000080010024000 0x0000002000400900 0x020000007003c023 0x8008000001c00f00

def z530 : W := mkw 0x50b127914e1130b2 0x4542c49e453844c2 0xa13307c18e3038d4 0x2284cc1f0638c0e3

def z531 : W := mkw 0x400009005e037030 0x0500002401780dc0 0x020000007c038001 0x0008000001f00e00

def z532 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xe70007398003a4fc 0xef9c001ce6000e93

def z533 : W := mkw 0x70fd3fbd7fd3f6bb 0x65c3f4fef5ff4fda 0xffff3ffffff3ffff 0xfffffcffffffcfff

def z534 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0xec3bc0000fbc001d 0x83b0ef00003ef000

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c006024c473e 0xd7d053001809311c

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c2000000c000005 0x80b0800000300000

def z537 : W := mkw 0x70b12f995e93f4b2 0x45c2c4be657a4fd2 0x0beb3f387db38001 0x082facfce1f6ce00

def z538 : W := mkw 0x01ffd27780000003 0xb807ff49de000000 0xfcffc03f80000000 0x43f3ff00fe000000

def z539 : W := mkw 0x41b3e7d3ce013032 0xdd06cf9f4f3804c0 0xa133c7c18e003804 0x2284cf1f063800e0

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c0c0024c783e 0xb7d05303000931e0

def z541 : W := mkw 0x80fe88007b6a4003 0x8603fa2001eda900 0xfefff8007fffc03f 0x9ffbffe001ffff00

def z542 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x3cf038c07e005807 0x90f3c0e301f80160

def z543 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0xee2b00000db3a4fd 0x83b8ac000036ce93

def z544 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0067ffc473f 0xd7f3ff0019fff11c

def z545 : W := mkw 0x3001021900908480 0x00c0040864024212 0xe40b003981b024fc 0xe7902c00e606c093

def z546 : W := mkw 0x4000258004013030 0x41000096001004c0 0x010007c000003800 0x2004001f000000e0

def z547 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xa32307018db3a4fd 0xa28c8c1c0636ce93

def z548 : W := mkw 0x40b0258004012022 0x4102c09600100480 0x3ff03fc00c03a025 0xbcffc0ff00300e80

def z549 : W := mkw 0xc0fea5806f693033 0xc703fa9601bda4c0 0xfdffc7c07ffc381f 0xa3f7ff1f01fff0e0

def z550 : W := mkw 0x204c102c21c08609 0x20813040b0870218 0x4e0c003e01c38729 0xcd383000f8070e1c

def z551 : W := mkw 0x71ffb7bd0491a4a3 0xe9c7fedef4124692 0x0beb3f380db38001 0x082facfce036ce00

def z552 : W := mkw 0x010136b500000000 0x680404dad4000000 0x01003f3800000000 0x080400fce0000000

def z553 : W := mkw 0x2000000821c08608 0x0080000020870218 0x0000000001c00708 0x000000000007001c

def z554 : W := mkw 0x70b12f995e93f4b2 0x45c2c4be657a4fd2 0xefeb3f39fdb3a4fd 0xefbfacfce7f6ce93

def z555 : W := mkw 0x00b0248000000002 0x4002c09200000000 0x09e03f0000000000 0x082780fc00000000

def z556 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0x2f2007000db3a4fd 0xacbc801c0036ce93

def z557 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x23303fc00e03f824 0x3c8cc0ff00380fe0

def z558 : W := mkw 0x4000010004012020 0x0100000400100480 0x0b2007000c038001 0x082c801c00300e00

def z559 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1bf03fc07e03d803 0x186fc0ff01f80f60

def z560 : W := mkw 0x00fc3ca47b42521b 0x6403f0f291ed0948 0x10d438c672405b02 0x104350e319c9016c

def z561 : W := mkw 0x084c5866b1464b4d 0x302131619ac5192d 0xf4d4f8c7f24c7ffe 0xf7d353e31fc931ff

def z562 : W := mkw 0x204c000821c08401 0x0081300020870210 0x5ecc003871c3842b 0xcd7b3000e1c70e10

def z563 : W := mkw 0x004c102400000001 0x2001304090000000 0x08c8383800000000 0x082320e0e0000000

def z564 : W := mkw 0x70ff83190491a4a3 0x81c3fe0c64124692 0xffffc7398db3a4fd 0xefffff1ce636ce93

def z565 : W := mkw 0xf00103196ff9a4a0 0x07c0040c65bfe692 0xef2b0739ffffa4ff 0xefbcac1ce7fffe93

def z566 : W := mkw 0x60fc3dac7fc3f63b 0x6583f0f6b1ff0fd8 0x5fec3f3e7dc3c72b 0xdd7fb0fcf9f70f1c

def z567 : W := mkw 0x204c102c21c08609 0x20813040b0870218 0x0008003801800000 0x00002000e0060000

def z568 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0ac8383871c3c72b 0x882b20e0e1c70f1c

def z569 : W := mkw 0xc0fead807f6b7033 0xc703fab601fdadc0 0xffffff007fff801f 0x8bfffffc01fffe00

def z570 : W := mkw 0x0800404280040944 0x102001010a001025 0xb410c0c1820c78f6 0xb6d04303060831e3

def z571 : W := mkw 0x20fc182c7bc2c60b 0x2483f060b1ef0b18 0x7efc383e7fc3c72f 0xddfbf0e0f9ff0f1c

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x082b00000db00001 0x0020ac000036c000

def z573 : W := mkw 0x214fd27fa1c08609 0xb8853f49fe870218 0xc00fc03f81c00708 0x43003f00fe07001c

def z574 : W := mkw 0x01fefce6b142420b 0xf807fbf39ac50908 0x10d4f8c670404302 0x104353e319c1010c

def z575 : W := mkw 0x08b064c280040946 0x5022c1930a001025 0xfdf4ffc7824c7ffe 0xfff7d3ff1e0931ff

def z576 : W := mkw 0x00b000004a000002 0x0402c00001280000 0x203000000e000004 0x0080c00000380000

def z577 : W := mkw 0x0800404280040944 0x102001010a001025 0xe014c0c7824c3fdc 0x638053031e0930ff

def z578 : W := mkw 0x40fc2d807f437033 0x4503f0b601fd0dc0 0x7ffc3fc07fc3f82f 0xbdfff0ff01ff0fe0

def z579 : W := mkw 0x50000100041120a0 0x0140000400104482 0x000000000c3020d4 0x000000000030c083

def z580 : W := mkw 0x884ec042a16c0945 0x92213b010a85b025 0xc00fc00781fc07d8 0x43003f001e07f01f

def z581 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xd0dfc00073fc001a 0x03437f0001cff000

def z582 : W := mkw 0x70011b3d1493e6a8 0x21c0046cf4524f9a 0x03003f3f8003e7e0 0x7c0c00fcfe000f9f

def z583 : W := mkw 0x01b3a69100000002 0xc806ce9a44000000 0x0123070000000000 0x00048c1c00000000

def z584 : W := mkw 0x084c5866b1464b4d 0x302131619ac5192d 0x10d4f8c6724c5b02 0x104353e319c9316c

def z585 : W := mkw 0x4000010004012020 0x0100000400100480 0xef2007018c03a4fd 0xefbc801c06300e93

def z586 : W := mkw 0xd0ff83116f7920a3 0x8743fe0c45bde482 0xfdffc701fffc20df 0xa3f7ff1c07fff083

def z587 : W := mkw 0x3801425b80948dc4 0x10e005096e025237 0xf41fc0ff83fc7ffe 0xf7d07f03fe0ff1ff

def z588 : W := mkw 0x80b000006b680002 0x0602c00001ada000 0x3cf000007ffc001f 0x80f3c00001fff000

def z589 : W := mkw 0x48b06dc2de077976 0x5522c1b70b781de5 0x3ff4ffc67e4ffb27 0xbcffd3ff19f93fec

def z590 : W := mkw 0x8000000021680000 0x020000000085a000 0x0000000001fc0018 0x000000000007f000

def z591 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0xfcffc0c1fffc38df 0xa3f3ff0307fff0e3

def z592 : W := mkw 0x40fead805e037033 0xc503fab601780dc0 0xffffffc07e03f827 0xbfffffff01f80fe0

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x201000c002003804 0x20804003000800e0

def z594 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0xf437c0000e7c001e 0x83d0df000039f000

def z595 : W := mkw 0x0800000000040944 0x0020000000001025 0x341000c0024c7ffe 0xb4d04003000931ff

def z596 : W := mkw 0x004e800000000001 0x80013a0000000000 0xc00fc00000000000 0x03003f0000000000

def z597 : W := mkw 0x7001435b8491a4a0 0x11c0050d6e124692 0xff3fc7ff8db3a4fd 0xfffcff1ffe36ce93

def z598 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xa8fbc0007fbc0015 0x02a3ef0001fef000

def z599 : W := mkw 0x00b000004a000002 0x0402c00001280000 0x08e000007c000001 0x0023800001f00000

def z600 : W := mkw 0x41fff7f7ce013033 0xfd07ffdfdf3804c0 0xfdffffff8e003804 0x7ff7fffffe3800e0

def z601 : W := mkw 0x4800414284052964 0x112001050a1014a5 0xff34c7c78e4fffff 0xfffcd31f1e393fff

def z602 : W := mkw 0x400001004e013030 0x05000004013804c0 0x000000000e003804 0x00000000003800e0

def z603 : W := mkw 0x2000080831c2c608 0x0080002020c70b18 0x1ec0380071c3c72b 0x9c7b00e001c70f1c

def z604 : W := mkw 0xf8ffc35beffdade7 0x97e3ff0d6fbff6b7 0xffffc7ffffffffff 0xffffff1fffffffff

def z605 : W := mkw 0x2000000800808400 0x0080000020020210 0x0200000001838429 0x8008000000060e10

def z606 : W := mkw 0x4000010004012020 0x0100000400100480 0x030007000003a020 0x2c0c001c00000e80

def z607 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdfffffff1c0000b 0xfff7ffffffc70000

def z608 : W := mkw 0x00b064c280000002 0x5002c1930a000000 0xfdf4ffc780000000 0x7ff7d3ff1e000000

def z609 : W := mkw 0x780001080495ade4 0x01e00004201256b7 0x020000000fffffff 0x80080000003fffff

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00b000001b00018 0x03002c000006c000

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c00000000000 0x03d0530000000000

def z612 : W := mkw 0xa0fe982c7beac60b 0xa683fa60b1efab18 0x5edcf83e73cfc72b 0xdd7b73e0f9cf3f1c

def z613 : W := mkw 0x0000248000000000 0x4000009200000000 0x01003fc000000000 0x3c0400ff00000000

def z614 : W := mkw 0x604c192c35c3e629 0x21813064b0d70f98 0x7fec3f3e7dc3e72f 0xfdffb0fcf9f70f9c

def z615 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1ec838387183c023 0x9c7b20e0e1c60f00

def z616 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xeceb00007db0001d 0x83b3ac0001f6c000

def z617 : W := mkw 0x0800484290064944 0x102001210a401925 0xfed4f8c7f24fffff 0xfffb53e31fc93fff

def z618 : W := mkw 0x0800000000040944 0x0020000000001025 0x54040006024c7ffe 0xd5501000180931ff

def z619 : W := mkw 0x214fda7fb1c2c609 0xb8853f69fec70b18 0xdecff83ff1c3c72b 0xdf7b3fe0ffc70f1c

def z620 : W := mkw 0x004c506680000001 0x300131419a000000 0xfcdcf8ff80000000 0x7ff373e3fe000000

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b00018db024fd 0xe7b0ac000636c093

def z622 : W := mkw 0x80fe80004a280003 0x8603fa000128a000 0xfcffc0000e3c0014 0x03f3ff000038f000

def z623 : W := mkw 0x004c000021400001 0x0001300000850000 0xfcdcc00073cc001f 0x83f3730001cf3000

def z624 : W := mkw 0x48b06dc2de077976 0x5522c1b70b781de5 0xbff0ffc1fe0ff8f7 0xbeffc3ff07f83fe3

def z625 : W := mkw 0x48b06dc2de077976 0x5522c1b70b781de5 0x3ff03fc7fe03ffe7 0xfcffc0ff1ff80fff

def z626 : W := mkw 0xc0fead807f6b7033 0xc703fab601fdadc0 0x3ffb3fc07fb3f827 0xbcffecff01fecfe0

def z627 : W := mkw 0x400009005e037030 0x0500002401780dc0 0x361000c07e03f827 0xb4d8400301f80fe0

def z628 : W := mkw 0x0000080010024000 0x0000002000400900 0x020038000003c020 0x1c0800e000000f00

def z629 : W := mkw 0x81fff6f7ca280003 0xfe07ffdbdf28a000 0xfdffffff8e3c0014 0x7ff7fffffe38f000

def z630 : W := mkw 0x3001021900908480 0x00c0040864024212 0xce0b003981b384f9 0xcf382c00e606ce13

def z631 : W := mkw 0x4000010004012020 0x0100000400100480 0x3f3007c00e03f827 0xbcfcc01f00380fe0

def z632 : W := mkw 0x700001080491a4a0 0x01c0000420124692 0x020000000db38001 0x000800000036ce00

def z633 : W := mkw 0x0000404280000000 0x100001010a000000 0x000000c780000000 0x740000031e000000

def z634 : W := mkw 0x00b000004a000002 0x0402c00001280000 0xfcf4c0007e4c001f 0x83f3d30001f93000

def z635 : W := mkw 0x0800404280040944 0x102001010a001025 0xa010c0c7820c7ff4 0x768043031e0831ff

def z636 : W := mkw 0x00b2800000000002 0x8002ca0000000000 0xa033c00000000000 0x0280cf0000000000

def z637 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c7820c38d4 0x77d053031e0830e3

def z638 : W := mkw 0x01b3e6d380000002 0xd806cf9b4e000000 0xf537c7c780000000 0x77d4df1f1e000000

def z639 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xe12b07398db024dc 0x6384ac1ce636c093

def z640 : W := mkw 0x314fd27f80908481 0xb8c53f49fe024212 0xc00fc03f81b004d8 0x43003f00fe06c013

def z641 : W := mkw 0x2000000800808400 0x0080000020020210 0xee2b00380db3843d 0xcfb8ac00e036ce10

def z642 : W := mkw 0x284c586eb1c6cf4d 0x30a13161bac71b3d 0xdeccf83ff1cfc7fb 0xdf7b33e0ffc73f1f

def z643 : W := mkw 0x0800404280040944 0x102001010a001025 0xc004c0c7804c7ff8 0x770013031e0131ff

def z644 : W := mkw 0x0000080010024000 0x0000002000400900 0x5ec438067043c72b 0xdd7b10e019c10f1c

def z645 : W := mkw 0x71ffb7bd0491a4a3 0xe9c7fedef4124692 0xefeb3f398db3a4fd 0xefbfacfce636ce93

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000024fc 0x8000000000000093

def z647 : W := mkw 0x20fc3cac31c2c60b 0x6083f0f2b0c70b18 0x7ffc3ffe71c3c72b 0xfdfff0fff9c70f1c

def z648 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc0000db0001d 0x83f3ff000036c000

def z649 : W := mkw 0x014fd27780000001 0xb8053f49de000000 0xf41fc0ff80000000 0x77d07f03fe000000

def z650 : W := mkw 0x40fc3da47f43723b 0x6503f0f691fd0dc8 0x3ff43fc67e43fb27 0xbcffd0ff19f90fec

def z651 : W := mkw 0x2000080831c2c608 0x0080002020c70b18 0x5604000671c3c72b 0xd558100019c70f1c

def z652 : W := mkw 0x00fec04280000003 0x9003fb010a000000 0xfcffc0c780000000 0x77f3ff031e000000

def z653 : W := mkw 0x0000404280000000 0x100001010a000000 0x1014c0c600000000 0x1040530318000000

def z654 : W := mkw 0x81fef4e6eb680003 0xfe07fbd39bada000 0xfcfff8c67ffc001f 0x93f3ffe319fff000

def z655 : W := mkw 0x284c182c31c6cf4d 0x20a13060b0c71b3d 0x5ecc383e73cfffff 0xdd7b30e0f9cf3fff

def z656 : W := mkw 0x41ffbfb55e037033 0xed07fefed5780dc0 0x0beb3f387c038001 0x082facfce1f00e00

def z657 : W := mkw 0x0101527780000000 0x38040549de000000 0x0000003f80000000 0x40000000fe000000

def z658 : W := mkw 0x50010311041120a0 0x0140040c44104482 0xe52307018c3024fc 0xe7948c1c0630c093

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000024c001e 0x8000000000093000

def z660 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c780007fe0 0x77d053031e0001ff

def z661 : W := mkw 0x41fff7f784012023 0xf907ffdfde100480 0xffffffff8c03a025 0xfffffffffe300e80

def z662 : W := mkw 0x800000004a280000 0x060000000128a000 0x000000000e3c0014 0x000000000038f000

def z663 : W := mkw 0xc0fe89007f6b7033 0x8703fa2401fdadc0 0xfeffc0007ffff83f 0x83fbff0001ffffe0

def z664 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x0200383800038000 0x080800e0e0000e00

def z665 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xb0f7c0007e7c0016 0x02c3df0001f9f000

def z666 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0xef3bc7f98fbfbcfd 0xefbcef1fe63efef3

def z667 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x420c003e71c3c72b 0xc1083000f9c70f1c

def z668 : W := mkw 0x08fec04280040947 0x9023fb010a001025 0xfcffc0c7824c7ffe 0xf7f3ff031e0931ff

def z669 : W := mkw 0xf0ff9b3d7ffbe6ab 0xa7c3fe6cf5ffef9a 0xffffff3fffffe7ff 0xfffffffcffffff9f

def z670 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0x0010c000020c0000 0x0000430000083000

def z671 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x233007c07e03f827 0xa08cc01f01f80fe0

def z672 : W := mkw 0x0800404280040944 0x102001010a001025 0x0004c006004c0300 0x000013001801300c

def z673 : W := mkw 0x284c586eb1c6cf4d 0x30a13161bac71b3d 0x5edcf8fe73cfdf2b 0xdd7b73e3f9cf3f7c

def z674 : W := mkw 0x01fffef7b142420b 0xf807fffbdec50908 0xfdfffffff0404302 0x7ff7ffffffc1010c

def z675 : W := mkw 0xf0b383194eb9a4a2 0x87c2ce0c653ae692 0xef3bc7398fbfa4fd 0xefbcef1ce63efe93

def z676 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x2fe03f007c03a025 0xacbf80fc01f00e80

def z677 : W := mkw 0xc0fead807f6b7033 0xc703fab601fdadc0 0x3ff4ffc07e4ff827 0xbcffd3ff01f93fe0

def z678 : W := mkw 0x21017eff9082c608 0x788405fbfe420b18 0x03003fff8003c720 0x7c0c00fffe000f1c

def z679 : W := mkw 0x00b0248000000002 0x4002c09200000000 0x10d038c000000000 0x104340e300000000

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000db0001d 0x800000000036c000

def z681 : W := mkw 0xa8fed86efbeecf4f 0xb6a3fb61bbefbb3d 0xfefff8ffffffffff 0xfffbffe3ffffffff

def z682 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x420c383e01c3c728 0x5d0830e0f8070f1c

def z683 : W := mkw 0x48b065c2ce053976 0x5522c1970b3814e5 0xf534c7c78e4c7ffe 0xf7d4d31f1e3931ff

def z684 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x4f2b07380db38429 0xcd3cac1ce036ce10

def z685 : W := mkw 0x0800404280040944 0x102001010a001025 0xb014c0c7824c7bd6 0x32c053031e0931ef

def z686 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x19fffffe00000000 0x1867fffff8000000

def z687 : W := mkw 0x80fe800021680003 0x8203fa000085a000 0xfcffc00001fc0018 0x03f3ff000007f000

def z688 : W := mkw 0x784d5b7fb5d7efed 0x31e1356dfed75fbf 0xffffffffffffffff 0xffffffffffffffff

def z689 : W := mkw 0x00fc00006b400003 0x0403f00001ad0000 0x7cfc00007fc0000f 0x81f3f00001ff0000

def z690 : W := mkw 0x2800484ab1c6cf4c 0x10a001212ac71b3d 0xf614c0c7f3cfffff 0xf7d853031fcf3fff

def z691 : W := mkw 0xc0fe81006f692023 0x8703fa0401bda480 0xffffc7007fffa03f 0xafffff1c01fffe80

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e00000000038021 0x8c38000000000e00

def z693 : W := mkw 0x00b0248000000002 0x4002c09200000000 0x213007c000000000 0x2084c01f00000000

def z694 : W := mkw 0x00b000004a000002 0x0402c00001280000 0x3cf000c07e007827 0xb4f3c00301f801e0

def z695 : W := mkw 0x0000404280000000 0x100001010a000000 0xf414c0c7800024fc 0xf7d053031e000093

def z696 : W := mkw 0x01b3e6d380000002 0xd806cf9b4e000000 0xed3bc7f980000000 0x6fb4ef1fe6000000

def z697 : W := mkw 0x01fef4e680000003 0xf807fbd39a000000 0x3df4ffc600000000 0x3cf7d3ff18000000

def z698 : W := mkw 0x70010b1935d3e6a8 0x01c0042c64d74f9a 0xef2b0739fdf3e7ff 0xefbcac1ce7f7cf9f

def z699 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x1ed038c07203d823 0x9c7b40e301c80f60

def z700 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x4f0807398183a4e9 0xed3c201ce6060e93

def z701 : W := mkw 0x3000000800908480 0x00c0000020024212 0x0000000001b004d8 0x000000000006c013

def z702 : W := mkw 0x2800586e9086cf4c 0x30a00161ba421b3d 0xf614f8ff824ffffe 0xffd853e3fe093fff

def z703 : W := mkw 0x80feac807b6a5013 0xc603fab201eda940 0x10d4f8c0724c5802 0x104353e301c93160

def z704 : W := mkw 0x0000080031424208 0x0000002000c50908 0x0000000070404302 0x0000000001c1010c

def z705 : W := mkw 0x70010b191493e4a0 0x01c0042c64524f92 0xffeb3f39fdb3e4ff 0xffffacfce7f6cf93

def z706 : W := mkw 0x0800404280040944 0x102001010a001025 0xd404c007804c47fa 0xd75013001e01311f

def z707 : W := mkw 0x21b3eedbb1c2c60a 0xd886cfbb6ec70b18 0xa333c7c1f1c3c72b 0xa28ccf1f07c70f1c

def z708 : W := mkw 0x09ffb6b500040947 0xe827fedad4001025 0x09eb3f38024c7ffe 0x8827acfce00931ff

def z709 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x3dfb3ff802007826 0xbcf7ecffe00801e0

def z710 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0x09eb3f3870000000 0x0827acfce1c00000

def z711 : W := mkw 0x80fe90246b680003 0xa603fa4091ada000 0xfcffc03e7ffc001f 0xc3f3ff00f9fff000

def z712 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff824c0002 0x7ff7fffffe093000

def z713 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e03d807 0x98ffc0ff01f80f60

def z714 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3fc7398db3a4fd 0xeffcff1ce636ce93

def z715 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3f07ff8ff3ffff 0xfffcfc1ffe3fcfff

def z716 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdffffffffbc0015 0x7ff7fffffffef000

def z717 : W := mkw 0x004c182410024001 0x2001306090400900 0x5ecc383e7043c72b 0xdd7b30e0f9c10f1c

def z718 : W := mkw 0x81fff6f7ca280003 0xfe07ffdbdf28a000 0xfdfffffffe3c0017 0xfff7fffffff8f000

def z719 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1ecc383e71c3c323 0x9c7b30e0f9c70f0c

def z720 : W := mkw 0x090176f780040944 0x782405dbde001025 0x01003fff80005b00 0x7c0400fffe00016c

def z721 : W := mkw 0x010136b500000000 0x680404dad4000000 0xed2b3f3980000000 0x6fb4acfce6000000

def z722 : W := mkw 0x00b1269100000002 0x4002c49a44000000 0xfdfb3ff982007cfe 0xfff7ecffe60801f3

def z723 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffffc473f 0xfff7fffffffff11c

def z724 : W := mkw 0x48b06dc2de077976 0x5522c1b70b781de5 0xcbe4ff07fc4f87d9 0x4b2f93fc1ff13e1f

def z725 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff804c0300 0x7ff7fffffe01300c

def z726 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff80005b00 0x7ff7fffffe00016c

def z727 : W := mkw 0x0800404280040944 0x102001010a001025 0xfcd4c0c7f24c7fff 0xf7f353031fc931ff

def z728 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8040000a 0xfff7fffffe010000

def z729 : W := mkw 0x700009085e93f4b0 0x05c00024217a4fd2 0x020000007db3a4fd 0x8008000001f6ce93

def z730 : W := mkw 0xf0fe89087ffbe6ab 0x87c3fa2421ffef9a 0xfeffc0007fffe7ff 0x83fbff0001ffff9f

def z731 : W := mkw 0x014d76f780000001 0x780535dbde000000 0x11c43fff80000000 0x7c4710fffe000000

def z732 : W := mkw 0xf00009087ffbe6a8 0x07c0002421ffef9a 0x020000007fffe7ff 0x8008000001ffff9f

def z733 : W := mkw 0x010136b500000000 0x680404dad4000000 0x01003f3e00000000 0x5c0400fcf8000000

def z734 : W := mkw 0x01b176f7ca000002 0x7c06c5dbdf280000 0x3df03ffffe000007 0xfcf7c0fffff80000

def z735 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff2f073f8db3a4fd 0xfffcbc1cfe36ce93

def z736 : W := mkw 0x7000090835d3e6a8 0x01c0002420d74f9a 0xf6040007fdf3e7ff 0xf7d810001ff7cf9f

def z737 : W := mkw 0x810176f7eb680000 0x7e0405dbdfada000 0x01003ffffffc001f 0xfc0400fffffff000

def z738 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c5fda 0x7ff7fffffe09317f

def z739 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffff3f80000000 0x4bf7fffcfe000000

def z740 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc001fffc04df 0xc3f3ff0007fff013

def z741 : W := mkw 0x7801435b8495ade4 0x11e0050d6e1256b7 0x1b3fc7fe0fffdb03 0x186cff1ff83fff6c

def z742 : W := mkw 0x504d1b35355362a9 0x2141346cd4d54d8a 0xb1e73f07fc7063d6 0x32c79cfc1ff1c18f

def z743 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffff9fffc001f 0xabf7ffffe7fff000

def z744 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x4acc383e71c3c729 0x5d2b30e0f9c70f1c

def z745 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3b07f98db3a4fd 0xfffcec1fe636ce93

def z746 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x7ff43fc67e03f827 0xfdffd0ff19f80fe0

def z747 : W := mkw 0x700009085e93f4b0 0x05c00024217a4fd2 0x020000007fb3f827 0x8008000001fecfe0

def z748 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0ac8383e71838701 0x482b20e0f9c60e1c

def z749 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x19ffff3800000000 0x0867fffce0000000

def z750 : W := mkw 0x0800404280040944 0x102001010a001025 0xd014c0c7824c7ffe 0xd34053031e0931ff

def z751 : W := mkw 0x81fff6f7ca280003 0xfe07ffdbdf28a000 0xfdffffff8c300000 0x7ff7fffffe30c000

def z752 : W := mkw 0x0800404280040944 0x102001010a001025 0xfc3fc0c7824c7ffe 0xf7f0ff031e0931ff

def z753 : W := mkw 0x60fc35ac6fc1b63b 0x6583f0d6b1bf06d8 0x613c07fe0fc03f0c 0x6184f01ff83f00fc

def z754 : W := mkw 0x700009081493f4b0 0x01c0002420524fd2 0x020000000db3fcfd 0x800800000036cff3

def z755 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x0ac0383e7003c721 0x5c2b00e0f9c00f1c

def z756 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x02c0383e7003c720 0x5c0b00e0f9c00f1c

def z757 : W := mkw 0x81ffb6b54a280003 0xee07fedad528a000 0x09eb3f380c300000 0x0827acfce030c000

def z758 : W := mkw 0x30b12e995a92d492 0x44c2c4ba656a4b52 0xd0db38f9f3b05cda 0x53436ce3e7cec173

def z759 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff2b07398db3e4ff 0xfffcac1ce636cf93

def z760 : W := mkw 0x284c586eb1c6cf4d 0x30a13161bac71b3d 0xaad8f8f9f38fb8d5 0x2aab63e3e7ce3ee3

def z761 : W := mkw 0x00b166d380000002 0x5002c59b4e000000 0xfdffffff80000000 0x7ff7fffffe000000

def z762 : W := mkw 0x01fff6f7a140020b 0xf807ffdbde850008 0xfdffffff80400300 0x7ff7fffffe01000c

def z763 : W := mkw 0x00b02c805a025012 0x4402c0b201680940 0x3ff03fc07203d823 0xbcffc0ff01c80f60

def z764 : W := mkw 0x00b034a400000002 0x6002c0d290000000 0x3df03ffe00000000 0x7cf7c0fff8000000

def z765 : W := mkw 0x0001123500000000 0x20000448d4000000 0xed2b3f3f80000000 0x7fb4acfcfe000000

def z766 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0be03fc07c03d801 0x182f80ff01f00f60

def z767 : W := mkw 0x014d36b500000001 0x680534dad4000000 0x5dcc3f3e00000000 0x5d7730fcf8000000

def z768 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x29fb3ff800000000 0x28a7ecffe0000000

def z769 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xeb2b07398db3a4dd 0x6bacac1ce636ce93

def z770 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0067ffc431f 0x93f3ff0019fff10c

def z771 : W := mkw 0x81ffb6b54a280003 0xee07fedad528a000 0xa9fbff380e3c0014 0x0aa7effce038f000

def z772 : W := mkw 0x804e80006b680001 0x86013a0001ada000 0xdccfc0007ffc001f 0x83733f0001fff000

def z773 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff4ffc07e03f827 0xbfffd3ff01f80fe0

def z774 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x5cffc0007ffc000b 0x8173ff0001fff000

def z775 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003fff800024e0 0x7c0400fffe000093

def z776 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfedcf83e71c3c72b 0xdffb73e0f9c70f1c

def z777 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c7bd6 0x7ff7fffffe0931ef

def z778 : W := mkw 0xa04e982c31eac609 0xa2813a60b0c7ab18 0x5eccf83e71cfc72b 0xdd7b33e0f9c73f1c

def z779 : W := mkw 0x094ff6f780040945 0xf8253fdbde001025 0xc10fffff804c7ff8 0x7f043ffffe0131ff

def z780 : W := mkw 0x80b280006b680002 0x8602ca0001ada000 0xa033c0007fbc0015 0x0280cf0001fef000

def z781 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db3a4e1 0x6fbcac1ce636ce93

def z782 : W := mkw 0x80fea4806b681013 0xc603fa9201ada040 0xfcffc0c07ffc181f 0x83f3ff0301fff060

def z783 : W := mkw 0x010176f780000000 0x780405dbde000000 0x55043fff80000000 0x7d5410fffe000000

def z784 : W := mkw 0x0800404280040944 0x102001010a001025 0xf41fc0c783fc7ffe 0xf7d07f031e0ff1ff

def z785 : W := mkw 0x11fff6f780100083 0xf847ffdbde004002 0xfdffffff803000d0 0x7ff7fffffe00c003

def z786 : W := mkw 0x80fea4806b680003 0xc603fa9201ada000 0xfdffffc07ffc783f 0xbff7ffff01fff1e0

def z787 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc473f 0x83f3ff0001fff11c

def z788 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db3a0dd 0xabbcac1ce636ce83

def z789 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0xa133fff980000000 0x2a84cfffe6000000

def z790 : W := mkw 0x090176f780040944 0x782405dbde001025 0xc104ffff804c07d8 0x7f0413fffe01301f

def z791 : W := mkw 0x0800404280040944 0x102001010a001025 0xb014c0c7824c7ff6 0x76c053031e0931ff

def z792 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff820c0014 0x7ff7fffffe083000

def z793 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffdf0000b 0xfff7fffffff7c000

def z794 : W := mkw 0x010176f780000000 0x780405dbde000000 0xe5003fff80000000 0x7f9400fffe000000

def z795 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffff0000000 0x7ff7ffffffc00000

def z796 : W := mkw 0x0800404280040944 0x102001010a001025 0xfe14c0c7824fffff 0xfff853031e093fff

def z797 : W := mkw 0x0800404280040944 0x102001010a001025 0xfc34c0c78e4c7fff 0xf7f0d3031e3931ff

def z798 : W := mkw 0x40b02d8014037032 0x4102c0b600500dc0 0x3ff03fc07003f823 0xbcffc0ff01c00fe0

def z799 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffffc0003 0x7ff7fffffffff000

def z800 : W := mkw 0x88fec042eb6c0947 0x9623fb010badb025 0x08eb00c7fdb07fe1 0x7423ac031ff6c1ff

def z801 : W := mkw 0x40002d805e037030 0x450000b601780dc0 0x1fc03fc07e03f827 0xbc7f00ff01f80fe0

def z802 : W := mkw 0x81ffb6b521680003 0xea07fedad485a000 0xc9efff3801fc0018 0x0b27bffce007f000

def z803 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x5def3f3e0040472a 0xdd77bcfcf801011c

def z804 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80000428 0xfff7fffffe000010

def z805 : W := mkw 0x010176f780000000 0x780405dbde000000 0xa1233fff80000000 0x7e848cfffe000000

def z806 : W := mkw 0x0800404280040944 0x102001010a001025 0xd014c0c7824c7ffa 0x774053031e0931ff

def z807 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8000001c 0xfff7fffffe000000

def z808 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffdb0001d 0xfff7fffffff6c000

def z809 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffe7ffc001f 0x9bf7fffff9fff000

def z810 : W := mkw 0x010136b500000000 0x680404dad4000000 0x01003ff800000000 0x3c0400ffe0000000

def z811 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e4ff83f 0xbcffc0ff01f93fe0

def z812 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff804c7ff8 0x7ff7fffffe0131ff

def z813 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff82003804 0x7ff7fffffe0800e0

def z814 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffffc783f 0xfff7fffffffff1e0

def z815 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdfffff980000000 0x2bf7ffffe6000000

def z816 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdffff3980000000 0x6ff7fffce6000000

def z817 : W := mkw 0x010176f780000000 0x780405dbde000000 0xed2b3fff8db0001d 0xffb4acfffe36c000

def z818 : W := mkw 0x01b176f780000002 0x7806c5dbde000000 0x21303fff80000000 0x7c84c0fffe000000

def z819 : W := mkw 0x800280006b680000 0x86000a0001ada000 0x8003c0007ffc001f 0x82000f0001fff000

def z820 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x11d4fffe00000000 0x184753fff8000000

def z821 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdef3f3f80000000 0x7ff7bcfcfe000000

def z822 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x37d03fc07203f826 0xbcdf40ff01c80fe0

def z823 : W := mkw 0x81feb4a46b680003 0xee07fad291ada000 0xfcfff8007ffc001f 0x83f3ffe001fff000

def z824 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c78ffc7fff 0xf7d053031e3ff1ff

def z825 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff820c78f6 0xfff7fffffe0831e3

def z826 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c7fe2 0x7ff7fffffe0931ff

def z827 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xedeb3f3800000000 0x0bb7acfce0000000

def z828 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef3b07f98fb3bcfd 0xefbcec1fe63ecef3

def z829 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x4f2b07398db3a4e9 0xed3cac1ce636ce93

def z830 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xd1dfffff80000000 0x7f477ffffe000000

def z831 : W := mkw 0x00b1269100000002 0x4002c49a44000000 0x3df03ff980000000 0x7cf7c0ffe6000000

def z832 : W := mkw 0x414fdb77de037031 0xbd053f6ddf780dc0 0xc20fc03ffe03f827 0xc3083f00fff80fe0

def z833 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x7edc383e73c3c72f 0xddfb70e0f9cf0f1c

def z834 : W := mkw 0x010176f780000000 0x780405dbde000000 0xfd3fffff80000000 0x7ff4fffffe000000

def z835 : W := mkw 0x800000006b680000 0x0600000001ada000 0xfc3fc0007ffc001f 0x83f0ff0001fff000

def z836 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x12c0383e7003c722 0x5c4b00e0f9c00f1c

def z837 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71c3e7ff 0xdd7b30e0f9c70f9f

def z838 : W := mkw 0x700009081493f4b0 0x01c0002420524fd2 0x020000000003fce0 0x0008000000000ff3

def z839 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e43ff2f 0xbcffc0ff01f90ffc

def z840 : W := mkw 0x014d76f780000001 0x780535dbde000000 0xfdef3fff80000000 0x7ff7bcfffe000000

def z841 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xf0ffc0007ffc001e 0x03c3ff0001fff000

def z842 : W := mkw 0xc04ead80356b7031 0xc3013ab600d5adc0 0xc30fffc001fff838 0x3f0c3fff0007ffe0

def z843 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398fb3fcff 0xefbcac1ce63ecff3

def z844 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x19fb3ff800000000 0x1867ecffe0000000

def z845 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfffb3fc07e03f827 0xbfffecff01f80fe0

def z846 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x2bf03fc07e03f827 0xa8afc0ff01f80fe0

def z847 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x7ecc383e71c3e72f 0xfdfb30e0f9c70f9c

def z848 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffdfc0019 0x7ff7fffffff7f000

def z849 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0x0104ffff80000000 0x7c0413fffe000000

def z850 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xb0f7c0007ffc001f 0x82c3df0001fff000

def z851 : W := mkw 0x01fd76f780000003 0x7807f5dbde000000 0x7dfc3fff80000000 0x7df7f0fffe000000

def z852 : W := mkw 0x704c090835d3e6a9 0x01c1302420d74f9a 0xfeef00007df3e7ff 0x83fbbc0001f7cf9f

def z853 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xbdfbfff980000000 0x3ef7efffe6000000

def z854 : W := mkw 0x804e80006b680001 0x86013a0001ada000 0xf41fc0007ffc001f 0x83d07f0001fff000

def z855 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x33f03fc07e03f827 0xb0cfc0ff01f80fe0

def z856 : W := mkw 0x004d123500000001 0x20013448d4000000 0xedeb3f3980000000 0x6fb7acfce6000000

def z857 : W := mkw 0x81fff6f7a1680003 0xfa07ffdbde85a000 0xfdffffff83fc001e 0xfff7fffffe0ff000

def z858 : W := mkw 0x600009085e83f430 0x05800024217a0fd0 0x020000007f83fc2f 0x8008000001fe0ff0

def z859 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x2deb3f3800000000 0x2cb7acfce0000000

def z860 : W := mkw 0x01b176f780000002 0x7806c5dbde000000 0xfdf4ffff80000000 0x7ff7d3fffe000000

def z861 : W := mkw 0x81fff6f780280003 0xfa07ffdbde00a000 0xfdffffff803c0010 0x7ff7fffffe00f000

def z862 : W := mkw 0x89fff6f7a16c0947 0xfa27ffdbde85b025 0xfdffffff83fc7ffe 0xfff7fffffe0ff1ff

def z863 : W := mkw 0x680009087fc7ff7c 0x05a0002421ff1ffd 0x020000007fcfffff 0x8008000001ff3fff

def z864 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0c1fffc7cff 0xf7f3ff0307fff1f3

def z865 : W := mkw 0xa04c182c31eac609 0x22813060b0c7ab18 0x5ecc383e71ffc73b 0xdd7b30e0f9c7ff1c

def z866 : W := mkw 0x090176f780040944 0x782405dbde001025 0x1114ffff824c5b02 0x7c4453fffe09316c

def z867 : W := mkw 0x084d527780040945 0x30213549de001025 0xfdffffff824c7ffe 0xfff7fffffe0931ff

def z868 : W := mkw 0x00b02c8010024002 0x4002c0b200400900 0x3ff03fc07203f827 0xbcffc0ff01c80fe0

def z869 : W := mkw 0x004d123500000001 0x20013448d4000000 0xfdef3f3f804067fe 0xfff7bcfcfe01019f

def z870 : W := mkw 0x09b3f6f780040946 0xf826cfdbde001025 0xa133ffff820c7ff4 0x7e84cffffe0831ff

def z871 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5eef383e7df3c72b 0xdd7bbce0f9f7cf1c

def z872 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff820c1800 0x7ff7fffffe083060

def z873 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0xf51fffff80000000 0x7fd47ffffe000000

def z874 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x03c03fc07003f820 0x3c0f00ff01c00fe0

def z875 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0c67ffc7f3f 0xf7f3ff0319fff1fc

def z876 : W := mkw 0x01b3b6b500000002 0xe806cedad4000000 0x01233f3800000000 0x08048cfce0000000

def z877 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc24ff 0x83f3ff0001fff093

def z878 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x89ebff3980000000 0x0a27affce6000000

def z879 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003fff80004720 0x7c0400fffe00011c

def z880 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xdeccf83e71cfc73b 0xdf7b33e0f9c73f1c

def z881 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ffb3fc07fb3f827 0xbcffecff01fecfe0

def z882 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1ec8383e7183c723 0xdc7b20e0f9c60f1c

def z883 : W := mkw 0xf0ff83196ff9a4a3 0x87c3fe0c65bfe692 0x13d4c739f24fa4e2 0x6c4f531ce7c93e93

def z884 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc001fffc20df 0xa3f3ff0007fff083

def z885 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffe4c0007 0xfff7fffffff93000

def z886 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c5f2a 0xfff7fffffe09317c

def z887 : W := mkw 0x00fc34a400000003 0x6003f0d290000000 0x7dfc3ffe02407f2e 0xfdf7f0fff80901fc

def z888 : W := mkw 0x014d76f7a1400001 0x780535dbde850000 0x5dcc3ffff1c0000b 0xfd7730ffffc70000

def z889 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db384dd 0xcbbcac1ce636ce13

def z890 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0xc10fff3f80000000 0x4b043ffcfe000000

def z891 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c07de 0xfff7fffffe09301f

def z892 : W := mkw 0xe0fe89087febf63b 0x8783fa2421ffafd8 0xfeffc0007fffff3f 0x83fbff0001fffffc

def z893 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5acc383e71c3c70b 0x596b30e0f9c70f1c

def z894 : W := mkw 0xe00009087febf638 0x0780002421ffafd8 0x020000007fffff3f 0x8008000001fffffc

def z895 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0x19ffff38724c0002 0x0867fffce1c93000

def z896 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x7ff83ff87e03f827 0xfdffe0ffe1f80fe0

def z897 : W := mkw 0x71fef5ee8491a4a3 0xf9c7fbd7ba124692 0x12d4f8c60db3a4fd 0x904b53e31836ce93

def z898 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff820c7ff4 0x7ff7fffffe0831ff

def z899 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x5dfffffe00000000 0x5d77fffff8000000

def z900 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3fc7f98ffffcff 0xfffcff1fe63ffff3

def z901 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e03b805 0x3cffc0ff01f80ee0

def z902 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xf5d4ffff80000000 0x7fd753fffe000000

def z903 : W := mkw 0x0001021100000000 0x0000040844000000 0xfdeb3f3980000000 0x7ff7acfce6000000

def z904 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff2f07398df3a4ff 0xeffcbc1ce637ce93

def z905 : W := mkw 0x0800404280040944 0x102001010a001025 0x3414c0c7824c7fe6 0xf4d053031e0931ff

def z906 : W := mkw 0x7800494ab5d7efec 0x11e001252ad75fbf 0xf614c0c7ffffffff 0xf7d853031fffffff

def z907 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x5def3f3800000000 0x0977bcfce0000000

def z908 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0c07ffc001f 0xb7f3ff0301fff000

def z909 : W := mkw 0x004c000021400001 0x0001300000850000 0xfcffc0007ffc001f 0x83f3ff0001fff000

def z910 : W := mkw 0xf00009087ffbf4b0 0x07c0002421ffefd2 0x020000007ffffcff 0x8008000001fffff3

def z911 : W := mkw 0x80fe90246b680003 0xa603fa4091ada000 0xfcfff83e7ffc473f 0xdff3ffe0f9fff11c

def z912 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8db024fd 0xfff7fffffe36c093

def z913 : W := mkw 0x81fff6f7a1680003 0xfa07ffdbde85a000 0xfdfffffff1fc001b 0xfff7ffffffc7f000

def z914 : W := mkw 0x0800404280040944 0x102001010a001025 0x5414c0c7824c7fea 0xf55053031e0931ff

def z915 : W := mkw 0x014d76f780000001 0x780535dbde000000 0x09c83fff80000000 0x7c2720fffe000000

def z916 : W := mkw 0x80feb4a46b680003 0xe603fad291ada000 0xfdfffffe7ffc001f 0xfff7fffff9fff000

def z917 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x13c03fc07003f822 0x3c4f00ff01c00fe0

def z918 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xffffffc07ffff83f 0xbfffffff01ffffe0

def z919 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x52cc383e71c3c72a 0x5d4b30e0f9c70f1c

def z920 : W := mkw 0x50b02d805e1370b2 0x4542c0b601784dc2 0x3ff03fc07e33f8f7 0xbcffc0ff01f8cfe3

def z921 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0x09eb3ffffdb00001 0x7c27acfffff6c000

def z922 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xc9efffff80000000 0x7f27bffffe000000

def z923 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x3cffc0007ffc0007 0x80f3ff0001fff000

def z924 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c7b26 0xfff7fffffe0931ec

def z925 : W := mkw 0x00fc34a46b400003 0x6403f0d291ad0000 0x7dfc3ffe7fc0000f 0xfdf7f0fff9ff0000

def z926 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1bf03fc07e03f827 0x986fc0ff01f80fe0

def z927 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e73cfc73f 0xdd7b30e0f9cf3f1c

def z928 : W := mkw 0x6800494affc7ff7c 0x15a001252bff1ffd 0xf614c0c7ffcfffff 0xf7d853031fff3fff

def z929 : W := mkw 0x80b280004a280002 0x8602ca000128a000 0xfcfbc0007fbc001f 0x83f3ef0001fef000

def z930 : W := mkw 0xc0b2ad805e2b7032 0xc702cab60178adc0 0x3ff0ffc07e0ff827 0xbcffc3ff01f83fe0

def z931 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e03fcff 0xbcffc0ff01f80ff3

def z932 : W := mkw 0x09b176f780040946 0x7826c5dbde001025 0xfdf4ffff824c7ffe 0xfff7d3fffe0931ff

def z933 : W := mkw 0x0800404280040944 0x102001010a001025 0xb014c0c7824c7ffe 0xb2c053031e0931ff

def z934 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdffffffffb00007 0xfff7fffffffec000

def z935 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff81800009 0xfff7fffffe060000

def z936 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdfffffffdf0001f 0xfff7fffffff7c000

def z937 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdfffffe00000000 0x1bf7fffff8000000

def z938 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff81b00018 0x7ff7fffffe06c000

def z939 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xffeb0739fdb3a4ff 0xefffac1ce7f6ce93

def z940 : W := mkw 0x81fff6f7a1680003 0xfa07ffdbde85a000 0xfdffffff8dfc001d 0xfff7fffffe37f000

def z941 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x1deb3f3800000000 0x1c77acfce0000000

def z942 : W := mkw 0xa0b2982c5aaac60a 0xa682ca60b16aab18 0xa233f83e0e3fc734 0x5e88cfe0f838ff1c

def z943 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2fc7398dffa4fd 0xefbcbf1ce637fe93

def z944 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x33f03fc07e03f826 0x3ccfc0ff01f80fe0

def z945 : W := mkw 0x80b280006b680002 0x8602ca0001ada000 0xf437c0007ffc001f 0x83d0df0001fff000

def z946 : W := mkw 0x00fc74e680000003 0x7003f1d39a000000 0xfdfcffff80000000 0x7ff7f3fffe000000

def z947 : W := mkw 0x804e80006b680001 0x86013a0001ada000 0xc00fc0007dfc0019 0x03003f0001f7f000

def z948 : W := mkw 0x81b3f6f7ca280002 0xfe06cfdbdf28a000 0xa133ffff8e3c0014 0x7e84cffffe38f000

def z949 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xe8ffc0007ffc001d 0x03a3ff0001fff000

def z950 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc1fe03fce7 0xfcffc0ff07f80ff3

def z951 : W := mkw 0x00ff923500000003 0xa003fe48d4000000 0xfdffff3f80000000 0x7ff7fffcfe000000

def z952 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc783f 0x83f3ff0001fff1e0

def z953 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x3dfb3fff80000000 0x7cf7ecfffe000000

def z954 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0xfdfffff87ffc001f 0xbff7ffffe1fff000

def z955 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xdecc383ff1c3c7fb 0xdf7b30e0ffc70f1f

def z956 : W := mkw 0x804e80006b680001 0x86013a0001ada000 0xec2fc0007ffc001f 0x83b0bf0001fff000

def z957 : W := mkw 0x010176f780000000 0x780405dbde000000 0x35103fff82007826 0xfcd440fffe0801e0

def z958 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0xbdf3ffff80000000 0x7ef7cffffe000000

def z959 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff8ffc7fff 0xfff7fffffe3ff1ff

def z960 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x09eb3ff980000000 0x2827acffe6000000

def z961 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e7043c722 0x5d7b30e0f9c10f1c

def z962 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0x11d4fffff24c0002 0x7c4753ffffc93000

def z963 : W := mkw 0x004d527780000001 0x30013549de000000 0xfdffffff80000000 0x7ff7fffffe000000

def z964 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x08fbc0007fbc0001 0x0023ef0001fef000

def z965 : W := mkw 0x89fff6f7eb6c0947 0xfe27ffdbdfadb025 0xfdfffffffffc5b1f 0xfff7fffffffff16c

def z966 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff43fc67e43fb27 0xbcffd0ff19f90fec

def z967 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0x19fffffe024c5b02 0x1867fffff809316c

def z968 : W := mkw 0x600009087fc3f638 0x0580002421ff0fd8 0x761400c67fc3ff2f 0xf5d8500319ff0ffc

def z969 : W := mkw 0x2000182c31c2c608 0x20800060b0c70b18 0x1ec0383e71c3c72b 0xdc7b00e0f9c70f1c

def z970 : W := mkw 0x010176f780000000 0x780405dbde000000 0x4d083fff80000000 0x7d3420fffe000000

def z971 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3fc73f8fffe7ff 0xfffcff1cfe3fff9f

def z972 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xffffffff80038021 0xfffffffffe000e00

def z973 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x88ebc0007dbc0011 0x0223af0001f6f000

def z974 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff804c27fc 0xfff7fffffe01309f

def z975 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff80007ffc 0xfff7fffffe0001ff

def z976 : W := mkw 0x700009085e93f4b0 0x05c00024217a4fd2 0x020000007db38001 0x0008000001f6ce00

def z977 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffe7c0016 0x7ff7fffffff9f000

def z978 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xbcfbc0007fbc0017 0x82f3ef0001fef000

def z979 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff82005802 0x7ff7fffffe080160

def z980 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x09eb3f3f80000000 0x4827acfcfe000000

def z981 : W := mkw 0x80fea4806b680003 0xc603fa9201ada000 0xfdffff007ffc001f 0x8bf7fffc01fff000

def z982 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xffeb3f398db3a4fd 0xffffacfce636ce93

def z983 : W := mkw 0x89fff6f7eb6c0947 0xfe27ffdbdfadb025 0xfdfffffffffc07df 0xfff7fffffffff01f

def z984 : W := mkw 0x80ff92356b680003 0xa603fe48d5ada000 0xfdffff3ffffc001f 0xfff7fffcfffff000

def z985 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5edc38fe73c3df2b 0xdd7b70e3f9cf0f7c

def z986 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff824c783e 0xfff7fffffe0931e0

def z987 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003ffe00000000 0x180400fff8000000

def z988 : W := mkw 0x700009081493e4a0 0x01c0002420524f92 0x020000007db3e4ff 0x8008000001f6cf93

def z989 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xdecf383e71f3c73b 0xdf7b3ce0f9c7cf1c

def z990 : W := mkw 0x090176f780040944 0x782405dbde001025 0xed2b3fff80007ffc 0xffb4acfffe0001ff

def z991 : W := mkw 0x81ffb6b521680003 0xea07fedad485a000 0x09eb3f3801b00000 0x0827acfce006c000

def z992 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x13d03fc07e03f827 0xbc4f40ff01f80fe0

def z993 : W := mkw 0x294fd27fa1c48f4d 0xb8a53f49fe87123d 0xc00fc03f81cc07d8 0x43003f00fe07301f

def z994 : W := mkw 0x0800404280040944 0x102001010a001025 0xf014c0c7824c7fde 0x73c053031e0931ff

def z995 : W := mkw 0x80ffa6916b680003 0xc603fe9a45ada000 0xfdfffff9fffc001f 0xfff7ffffe7fff000

def z996 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff4ffc1fe4ffcff 0xffffd3ff07f93ff3

def z997 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1ec4383e7043c723 0xdc7b10e0f9c10f1c

def z998 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xcb2b07398db3a4fd 0xcb2cac1ce636ce93

def z999 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xa9fbfff9820c38d4 0x2aa7efffe60830e3

def z1000 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71c38709 0x5d7b30e0f9c70e1c

def z1001 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c38de 0xfff7fffffe0930e3

def z1002 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc38fe71c3ff2b 0xfd7b30e3f9c70ffc

def z1003 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdffffff81c00008 0x7ff7fffffe070000

def z1004 : W := mkw 0x01fff6f7ca001013 0xfc07ffdbdf280040 0xfdffffff82001800 0x7ff7fffffe080060

def z1005 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xb1f7ffff80000000 0x7ec7dffffe000000

def z1006 : W := mkw 0xf0fe89087ffbf4b3 0x87c3fa2421ffefd2 0xfeffc0007ffffcff 0x83fbff0001fffff3

def z1007 : W := mkw 0x81fff6f7ca280003 0xfe07ffdbdf28a000 0xfdffffff8fbc001d 0xfff7fffffe3ef000

def z1008 : W := mkw 0x01b176f780000002 0x7806c5dbde000000 0x11d03fff80000000 0x7c4740fffe000000

def z1009 : W := mkw 0x000034a400000000 0x600000d290000000 0x01003ffe00000000 0x7c0400fff8000000

def z1010 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xe32b07398db3a4fc 0x6f8cac1ce636ce93

def z1011 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdfb3ff980000000 0x7ff7ecffe6000000

def z1012 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc043f 0xc7f3ff0001fff010

def z1013 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71c3c30b 0x997b30e0f9c70f0c

def z1014 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x09eb3f380db00001 0x0827acfce036c000

def z1015 : W := mkw 0x80fea4806b680003 0xc603fa9201ada000 0xfdffc7c07ffc001f 0xa3f7ff1f01fff000

def z1016 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5edcf83e73cfc72b 0xdd7b73e0f9cf3f1c

def z1017 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x08efc0007dfc0001 0x0023bf0001f7f000

def z1018 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc001fffc001f 0xe7f3ff0007fff000

def z1019 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xc9efff3ffdfc0019 0x4b27bffcfff7f000

def z1020 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xf5d4ffff824c7ffe 0xffd753fffe0931ff

def z1021 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x2fe03fc07c03f825 0xbcbf80ff01f00fe0

def z1022 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdffff3ffffc001f 0xcbf7fffcfffff000

def z1023 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff03fc07e03f83f 0xbfffc0ff01f80fe0

def z1024 : W := mkw 0x81fff6f7a1680003 0xfa07ffdbde85a000 0xfdffffff804c0000 0x7ff7fffffe013000

def z1025 : W := mkw 0x0800404280040944 0x102001010a001025 0xe014c0c7824c7ffe 0xe38053031e0931ff

def z1026 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfeef383e71c3c72b 0xdffbbce0f9c70f1c

def z1027 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xa9fbfff9ffbc0015 0x2aa7efffe7fef000

def z1028 : W := mkw 0x600009087fc3f638 0x0580002421ff0fd8 0x020000007f83f827 0x8008000001fe0fe0

def z1029 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xc9eb3f3980000000 0x4b27acfce6000000

def z1030 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfefff83e7fffc73f 0xdffbffe0f9ffff1c

def z1031 : W := mkw 0x49b3e7d3ce053976 0xdd26cf9f4f3814e5 0xa133c7c18e0c38d4 0x2284cf1f063830e3

def z1032 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdffff3e00000000 0x5ff7fffcf8000000

def z1033 : W := mkw 0x6000090835c3f638 0x0180002420d70fd8 0x0200000071c3ff2b 0x8008000001c70ffc

def z1034 : W := mkw 0x09b3f6f780040946 0xf826cfdbde001025 0xf537ffff824c7ffe 0xffd4dffffe0931ff

def z1035 : W := mkw 0x004c182431424209 0x2001306090c50908 0x5ecc383e7043c323 0xdd7b30e0f9c10f0c

def z1036 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff03fc1fe03f827 0xffffc0ff07f80fe0

def z1037 : W := mkw 0x80b280006b680002 0x8602ca0001ada000 0xec3bc0007ffc001f 0x83b0ef0001fff000

def z1038 : W := mkw 0x004c34a400000001 0x600130d290000000 0x5dcc3ffe00000000 0x7d7730fff8000000

def z1039 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1fe03fc07c03f823 0xbc7f80ff01f00fe0

def z1040 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdfffffff1c0472b 0xfff7ffffffc7011c

def z1041 : W := mkw 0x01fef4e680000003 0xf807fbd39a000000 0x7dfcfffe00000000 0x7df7f3fff8000000

def z1042 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcfff8007ffc001f 0x9ff3ffe001fff000

def z1043 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x12c4383e71c3c72b 0xdc4b10e0f9c70f1c

def z1044 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07fb3f83f 0xbcffc0ff01fecfe0

def z1045 : W := mkw 0x004d123500000001 0x20013448d4000000 0x5def3f3e00000000 0x5d77bcfcf8000000

def z1046 : W := mkw 0x010176f780000000 0x780405dbde000000 0xe5003fff800024fc 0xff9400fffe000093

def z1047 : W := mkw 0x89fff6f7eb6c0947 0xfe27ffdbdfadb025 0xfdfffffff24c5b02 0x7ff7ffffffc9316c

def z1048 : W := mkw 0x09fff6f7a1440947 0xf827ffdbde851025 0xfdfffffff3cc7fff 0xfff7ffffffcf31ff

def z1049 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xe9ffffff80000000 0x6ba7fffffe000000

def z1050 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0xed2fffff80000000 0x7fb4bffffe000000

def z1051 : W := mkw 0x090176f780040944 0x782405dbde001025 0x01003fff800007c0 0x7c0400fffe00001f

def z1052 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07c03f821 0x3cffc0ff01f00fe0

def z1053 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3bf03fc07e03f807 0x38efc0ff01f80fe0

def z1054 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x09eb3f3980000000 0x6c27acfce6000000

def z1055 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x3dfffffe00000000 0x3cf7fffff8000000

def z1056 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff824c24fe 0xfff7fffffe093093

def z1057 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c3fdc 0x7ff7fffffe0930ff

def z1058 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfecc383ff1c3c72b 0xfffb30e0ffc70f1c

def z1059 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x3fe03fc07c03f827 0xbcff80ff01f00fe0

def z1060 : W := mkw 0x0800404280040944 0x102001010a001025 0xf414c0c7824c7fe2 0x77d053031e0931ff

def z1061 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdffffffffb0001f 0xfff7fffffffec000

def z1062 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfedcf8fe73cfff3f 0xfffb73e3f9cf3ffc

def z1063 : W := mkw 0x304c182c31d2c689 0x20c13060b0c74b1a 0x5ecc383e71f3c7fb 0xdd7b30e0f9c7cf1f

def z1064 : W := mkw 0x7000090835d3e6a8 0x01c0002420d74f9a 0x020000007db3a4fd 0x8008000001f6ce93

def z1065 : W := mkw 0x010176f780000000 0x780405dbde000000 0x092b3fff80000000 0x7c24acfffe000000

def z1066 : W := mkw 0x700009085e93f4b0 0x05c00024217a4fd2 0xf61000c1ffb3fcff 0xf7d8400307fecff3

def z1067 : W := mkw 0x090176f780040944 0x782405dbde001025 0xa110ffff820c38d4 0x7e8443fffe0830e3

def z1068 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x7ff43fc07e43f82f 0xbdffd0ff01f90fe0

def z1069 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xd8ffc0007ffc001b 0x0363ff0001fff000

def z1070 : W := mkw 0x81fff6f7a1680003 0xfa07ffdbde85a000 0xfdffffff81b00000 0x7ff7fffffe06c000

def z1071 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71c3c303 0x5d7b30e0f9c70f0c

def z1072 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0xedeb3f39fdb0001d 0xefb7acfce7f6c000

def z1073 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff800024e0 0x7ff7fffffe000093

def z1074 : W := mkw 0x6000090835c3e628 0x0180002420d70f98 0x020000007dc3e72f 0x8008000001f70f9c

def z1075 : W := mkw 0x0001269100000000 0x4000049a44000000 0x01003ff980000000 0x7c0400ffe6000000

def z1076 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x09efff3e00000000 0x0827bffcf8000000

def z1077 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff800020d4 0x7ff7fffffe000083

def z1078 : W := mkw 0x0800404280040944 0x102001010a001025 0xfc1cc0c783cc7fff 0xf7f073031e0f31ff

def z1079 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff82407f2e 0xfff7fffffe0901fc

def z1080 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0x11d4ffff824c7fe2 0x7c4753fffe0931ff

def z1081 : W := mkw 0x81fff6f7ca280003 0xfe07ffdbdf28a000 0xfdffffff820c0000 0x7ff7fffffe083000

def z1082 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0ac8383e7183c301 0x182b20e0f9c60f0c

def z1083 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0067ffc001f 0xd7f3ff0019fff000

def z1084 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff82000006 0xfff7fffffe080000

def z1085 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80007820 0x7ff7fffffe0001e0

def z1086 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80404302 0x7ff7fffffe01010c

def z1087 : W := mkw 0x01b176f780000002 0x7806c5dbde000000 0x09e03fff80000000 0x7c2780fffe000000

def z1088 : W := mkw 0x89fff6f7ca2c0947 0xfe27ffdbdf28b025 0xfdffffff8e3c38d4 0x7ff7fffffe38f0e3

def z1089 : W := mkw 0x014d76f780000001 0x780535dbde000000 0x410c3fff80000000 0x7d0430fffe000000

def z1090 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e03b807 0xa8ffc0ff01f80ee0

def z1091 : W := mkw 0x010176f780000000 0x780405dbde000000 0xc104ffff80000000 0x7f0413fffe000000

def z1092 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0x010b3fff80000000 0x7c042cfffe000000

def z1093 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x4ec8383e7183c729 0xdd3b20e0f9c60f1c

def z1094 : W := mkw 0x094d76f780040945 0x782535dbde001025 0xfddcffff824c7ffe 0xfff773fffe0931ff

def z1095 : W := mkw 0xc0b02d805e2b7032 0x4702c0b60178adc0 0x3ff03fc07e3ff837 0xbcffc0ff01f8ffe0

def z1096 : W := mkw 0x0103f6f780000000 0xf8040fdbde000000 0x8103ffff80000000 0x7e040ffffe000000

def z1097 : W := mkw 0x7000090835d3e6a8 0x01c0002420d74f9a 0x0200000071c3e7eb 0x8008000001c70f9f

def z1098 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x8b2b07398db380d1 0x0a2cac1ce636ce03

def z1099 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff820c3cfc 0xfff7fffffe0830f3

def z1100 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007dfc0019 0x03f3ff0001f7f000

def z1101 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdfffff800000000 0x3ff7ffffe0000000

def z1102 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc007fffc67ff 0xf7f3ff001ffff19f

def z1103 : W := mkw 0x01b176f780000002 0x7806c5dbde000000 0xfdfb3fff80000000 0x7ff7ecfffe000000

def z1104 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0387ffc001f 0xcff3ff00e1fff000

def z1105 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383ff1c3e7eb 0xfd7b30e0ffc70f9f

def z1106 : W := mkw 0x89fff6f7a16c0947 0xfa27ffdbde85b025 0xfdffffff81fc07d8 0x7ff7fffffe07f01f

def z1107 : W := mkw 0x7800090835d7efec 0x01e0002420d75fbf 0x020000007fffffff 0x8008000001ffffff

def z1108 : W := mkw 0x600009085e83f638 0x05800024217a0fd8 0x020000007e03ff27 0x8008000001f80ffc

def z1109 : W := mkw 0x80fe90246b680003 0xa603fa4091ada000 0xfcfff8387ffc001f 0x8bf3ffe0e1fff000

def z1110 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x7dff3ffe00000000 0x7df7fcfff8000000

def z1111 : W := mkw 0x00fd36b500000003 0x6003f4dad4000000 0xfdff3fff80000000 0x7ff7fcfffe000000

def z1112 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0ac8383e71c3c72b 0xdc2b20e0f9c70f1c

def z1113 : W := mkw 0x00fc34a400000003 0x6003f0d290000000 0x5dec3f3e00000000 0x5d77b0fcf8000000

def z1114 : W := mkw 0x090176f780040944 0x782405dbde001025 0xfd3fffff824c7ffe 0xfff4fffffe0931ff

def z1115 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xff3b07398fb3a4ff 0xeffcec1ce63ece93

def z1116 : W := mkw 0x01fff6f7eb400003 0xfc07ffdbdfad0000 0xfdffffffffc0000f 0xfff7ffffffff0000

def z1117 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0x0110ffff80000000 0x7c0443fffe000000

def z1118 : W := mkw 0x014d36b500000001 0x680534dad4000000 0x09c83f3800000000 0x082720fce0000000

def z1119 : W := mkw 0x01ffb6b54a000003 0xec07fedad5280000 0x09eb3f387c000001 0x0827acfce1f00000

def z1120 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc403f 0x97f3ff0001fff100

def z1121 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfeef383ffdf3e7ff 0xfffbbce0fff7cf9f

def z1122 : W := mkw 0x01ffb6b521400003 0xe807fedad4850000 0x09eb3f3871800001 0x0827acfce1c60000

def z1123 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x01c03fff80000000 0x7c0700fffe000000

def z1124 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdfffffff0000003 0xfff7ffffffc00000

def z1125 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xc9efff3800000000 0x0b27bffce0000000

def z1126 : W := mkw 0x78016fdb9497fdf4 0x51e005bf6e525ff7 0x03003fff8003ffe0 0x7c0c00fffe000fff

def z1127 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xd9ffffff80000000 0x5b67fffffe000000

def z1128 : W := mkw 0x010176f780000000 0x780405dbde000000 0x35103fff80000000 0x7cd440fffe000000

def z1129 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffff3cc000b 0xfff7ffffffcf3000

def z1130 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x52cc383e71c3c72b 0xd14b30e0f9c70f1c

def z1131 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1ff03fc07e03d823 0x9c7fc0ff01f80f60

def z1132 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x49ef3f3e00000000 0x4927bcfcf8000000

def z1133 : W := mkw 0x010176f780000000 0x780405dbde000000 0x55043fff8040472a 0xfd5410fffe01011c

def z1134 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x4acc383e71c3c72b 0xc92b30e0f9c70f1c

def z1135 : W := mkw 0x014ff6f780000001 0xf8053fdbde000000 0xddcfffff80000000 0x7f773ffffe000000

def z1136 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0xf537ffff80000000 0x7fd4dffffe000000

def z1137 : W := mkw 0x00b000004a000002 0x0402c00001280000 0xfcffc0007ffc001f 0x83f3ff0001fff000

def z1138 : W := mkw 0x89fff6f7eb6c0947 0xfe27ffdbdfadb025 0xfdfffffffffc38df 0xfff7fffffffff0e3

def z1139 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003ff980000000 0x280400ffe6000000

def z1140 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xedefff3f80000000 0x6fb7bffcfe000000

def z1141 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0be03fc07c03b801 0x282f80ff01f00ee0

def z1142 : W := mkw 0x700009087fd3f6b8 0x05c0002421ff4fda 0x020000007ff3ffff 0x8008000001ffcfff

def z1143 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xe32b07398db3a4fd 0xe38cac1ce636ce93

def z1144 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff800007c0 0x7ff7fffffe00001f

def z1145 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003f3f80000000 0x480400fcfe000000

def z1146 : W := mkw 0xc0b2ad805e2b7032 0xc702cab60178adc0 0xfff7ffc07e7ff83f 0xbfffdfff01f9ffe0

def z1147 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x5ddcffff80000000 0x7d7773fffe000000

def z1148 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff824c473e 0xfff7fffffe09311c

def z1149 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffffffc24ff 0xfff7fffffffff093

def z1150 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff804c0018 0x7ff7fffffe013000

def z1151 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8c000005 0xfff7fffffe300000

def z1152 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8c300014 0x7ff7fffffe30c000

def z1153 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0xfdffff39fffc001f 0xeff7fffce7fff000

def z1154 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xc9efff3f804c07d8 0x4b27bffcfe01301f

def z1155 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x09fbfff800000000 0x0827efffe0000000

def z1156 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x3dfb3f3800000000 0x08f7ecfce0000000

def z1157 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0x19fffffe7ffc0003 0x1867fffff9fff000

def z1158 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef3bc7398fbfa4fd 0xefbcef1ce63efe93

def z1159 : W := mkw 0x00b0248000000002 0x4002c09200000000 0x7df83ff800000000 0x7df7e0ffe0000000

def z1160 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x09eb3ffe00000000 0x1827acfff8000000

def z1161 : W := mkw 0x60fc09087fc3f63b 0x0583f02421ff0fd8 0x7efc00007fc3ff2f 0x81fbf00001ff0ffc

def z1162 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80004720 0x7ff7fffffe00011c

def z1163 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xab2b07398db3a4f5 0x6eacac1ce636ce93

def z1164 : W := mkw 0x4000090014036020 0x0100002400500d80 0x3ff03fc07e03f827 0xbcffc0ff01f80fe0

def z1165 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8ffc001f 0xfff7fffffe3ff000

def z1166 : W := mkw 0x204e982c31c2c609 0xa0813a60b0c70b18 0xdecff83e71c3c72b 0xdf7b3fe0f9c70f1c

def z1167 : W := mkw 0x004d123521400001 0x20013448d4850000 0xfdef3f3ffdf0001f 0xfff7bcfcfff7c000

def z1168 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xa9fbffff80000000 0x7ea7effffe000000

def z1169 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07f98db3fcfd 0xffbcac1fe636cff3

def z1170 : W := mkw 0xa04e982c31eac609 0xa2813a60b0c7ab18 0x5ecf383e71f3c72b 0xdd7b3ce0f9c7cf1c

def z1171 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff824c5b1e 0xfff7fffffe09316c

def z1172 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff4ffc67e4fff3f 0xffffd3ff19f93ffc

def z1173 : W := mkw 0x0001269100000000 0x4000049a44000000 0xed2b3ff980000000 0x7fb4acffe6000000

def z1174 : W := mkw 0x7800494ade97fdf4 0x15e001252b7a5ff7 0xf614c0c7ffffffff 0xf7d853031fffffff

def z1175 : W := mkw 0x80b280006b680002 0x8602ca0001ada000 0xbcf3c0007ffc001f 0x82f3cf0001fff000

def z1176 : W := mkw 0x00b1269100000002 0x4002c49a44000000 0x3dfb3ff800000000 0x3cf7ecffe0000000

def z1177 : W := mkw 0x600009087fc3f638 0x0580002421ff0fd8 0x020000007dc3c72b 0x8008000001f70f1c

def z1178 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xa9eb3f3980000000 0x2aa7acfce6000000

def z1179 : W := mkw 0x004c102400000001 0x2001304090000000 0x7dec3f3e00000000 0x7df7b0fcf8000000

def z1180 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xaf2b07398db3a0f5 0xaebcac1ce636ce83

def z1181 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdfffffff0400002 0x7ff7ffffffc10000

def z1182 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xbff33fc07e33f837 0xbeffccff01f8cfe0

def z1183 : W := mkw 0xa04e982c31eac609 0xa2813a60b0c7ab18 0xfedff83e73ffc73f 0xdffb7fe0f9cfff1c

def z1184 : W := mkw 0x094d76f780040945 0x782535dbde001025 0x5dcc3fff80407fea 0xfd7730fffe0101ff

def z1185 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80002024 0xfff7fffffe000080

def z1186 : W := mkw 0x00b1269100000002 0x4002c49a44000000 0x09eb3f3800000000 0x0827acfce0000000

def z1187 : W := mkw 0x094ff6f780040945 0xf8253fdbde001025 0xf51fffff824c7ffe 0xffd47ffffe0931ff

def z1188 : W := mkw 0x090176f780040944 0x782405dbde001025 0x01003fff824c7ffe 0xfc0400fffe0931ff

def z1189 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e7183c721 0x5d7b30e0f9c60f1c

def z1190 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0x5def3f3e7df0000b 0xdd77bcfcf9f7c000

def z1191 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdfffffffe007827 0xfff7fffffff801e0

def z1192 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff82007cfe 0xfff7fffffe0801f3

def z1193 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xb8ffc0007ffc0017 0x02e3ff0001fff000

def z1194 : W := mkw 0x0800404280040944 0x102001010a001025 0xe014c0c7824c7ffc 0x778053031e0931ff

def z1195 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0b2b07398db3a4fd 0xec2cac1ce636ce93

def z1196 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07203f822 0x3cffc0ff01c80fe0

def z1197 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x0acc383e71c38301 0x082b30e0f9c70e0c

def z1198 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0x3dfb3ff87fb00007 0xbcf7ecffe1fec000

def z1199 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xddefff3f80000000 0x5f77bffcfe000000

def z1200 : W := mkw 0x010176f780000000 0x780405dbde000000 0x2d203fff80000000 0x7cb480fffe000000

def z1201 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1acc383e71c3c723 0x5c6b30e0f9c70f1c

def z1202 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xd0dfc0007ffc001f 0x83437f0001fff000

def z1203 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0xfdffff3e7ffc001f 0xdff7fffcf9fff000

def z1204 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc0003 0x03f3ff0001fff000

def z1205 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc67e03ff27 0xfcffc0ff19f80ffc

def z1206 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xbff0ffc07e0ff837 0xbeffc3ff01f83fe0

def z1207 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0c07ffc581f 0x93f3ff0301fff160

def z1208 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0x09eb3fff80007fe0 0x7c27acfffe0001ff

def z1209 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xc8efc0007ffc001f 0x8323bf0001fff000

def z1210 : W := mkw 0x010136b500000000 0x680404dad4000000 0x01003f3980000000 0x6c0400fce6000000

def z1211 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfeffc0007fff803f 0x8ffbff0001fffe00

def z1212 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfedc38fff3c3ffff 0xfffb70e3ffcf0fff

def z1213 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0bf03fc07e039801 0x082fc0ff01f80e60

def z1214 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007fbc0015 0x03f3ff0001fef000

def z1215 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0007ffc203f 0xa7f3ff0001fff080

def z1216 : W := mkw 0x600009087fc3f638 0x0580002421ff0fd8 0x020000007d838001 0x0008000001f60e00

def z1217 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0b2b07398db3a0c1 0x282cac1ce636ce83

def z1218 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x0be03fc07e03f827 0xbc2f80ff01f80fe0

def z1219 : W := mkw 0x010176f780000000 0x780405dbde000000 0xf514ffff824c001e 0xffd453fffe093000

def z1220 : W := mkw 0x7000090835d3e6a8 0x01c0002420d74f9a 0x020000007df3c72b 0x8008000001f7cf1c

def z1221 : W := mkw 0x0800404280040944 0x102001010a001025 0xfcd4f8c7824c7ffe 0xfff353e31e0931ff

def z1222 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e7df3c73f 0xdd7b30e0f9f7cf1c

def z1223 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x0b2b07398db384c1 0x482cac1ce636ce13

def z1224 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b073f8db3e7fd 0xffbcac1cfe36cf9f

def z1225 : W := mkw 0x090176f780040944 0x782405dbde001025 0x01003fff800038c0 0x7c0400fffe0000e3

def z1226 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x19ffffff80000000 0x7c67fffffe000000

def z1227 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80400708 0x7ff7fffffe01001c

def z1228 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x1acc383e71c3c72b 0x986b30e0f9c70f1c

def z1229 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff03fc07e03d803 0x3cffc0ff01f80f60

def z1230 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1fd03fc07203f823 0xbc7f40ff01c80fe0

def z1231 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x09eb3f3e00000000 0x5c27acfcf8000000

def z1232 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xab2b07398db3a4fd 0xaaacac1ce636ce93

def z1233 : W := mkw 0x0800404280040944 0x102001010a001025 0xfc1cc0ff824c7ffe 0xfff07303fe0931ff

def z1234 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff80407fea 0xfff7fffffe0101ff

def z1235 : W := mkw 0xa04e982c31eac609 0xa2813a60b0c7ab18 0xfeeff83e7dffc73f 0xdffbbfe0f9f7ff1c

def z1236 : W := mkw 0x0001123500000000 0x20000448d4000000 0x01003f3f80000000 0x7c0400fcfe000000

def z1237 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfedcf83ff3cfe7ff 0xfffb73e0ffcf3f9f

def z1238 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db384d9 0x6fbcac1ce636ce13

def z1239 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xfdffff38024c001e 0x8bf7fffce0093000

def z1240 : W := mkw 0x010136b500000000 0x680404dad4000000 0x092b3f3800000000 0x0824acfce0000000

def z1241 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x5ec8383e7183c72b 0xdd7b20e0f9c60f1c

def z1242 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0x01233fff80000000 0x7c048cfffe000000

def z1243 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff8db00001 0x7ff7fffffe36c000

def z1244 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xedeb3f380db0001d 0x8bb7acfce036c000

def z1245 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdfffffffe4c001f 0xfff7fffffff93000

def z1246 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x3ff4ffc07e4ff827 0xbcffd3ff01f93fe0

def z1247 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x3fd03fc07203f827 0xbcff40ff01c80fe0

def z1248 : W := mkw 0x01b136b500000002 0x6806c4dad4000000 0x3df03ff800000000 0x3cf7c0ffe0000000

def z1249 : W := mkw 0x09b176f780040946 0x7826c5dbde001025 0x3df03fff82007fe6 0xfcf7c0fffe0801ff

def z1250 : W := mkw 0x00b126914a000002 0x4402c49a45280000 0xfdfb3ff9ffb0001f 0xfff7ecffe7fec000

def z1251 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e73c3ff2f 0xdd7b30e0f9cf0ffc

def z1252 : W := mkw 0x01ffb6b54a000003 0xec07fedad5280000 0x3dfb3f387e000007 0x88f7ecfce1f80000

def z1253 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x7eec383e7dc3c72f 0xddfbb0e0f9f70f1c

def z1254 : W := mkw 0x08b166d380040946 0x5022c59b4e001025 0xfdffffff824c7ffe 0xfff7fffffe0931ff

def z1255 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xb9ffffff80000000 0x3ae7fffffe000000

def z1256 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfffb3fc1ffb3fcff 0xffffecff07fecff3

def z1257 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffff24c001e 0xfff7ffffffc93000

def z1258 : W := mkw 0x09fff6f7ca040947 0xfc27ffdbdf281025 0xfdfffffffe4c7fff 0xfff7fffffff931ff

def z1259 : W := mkw 0x01b136b500000002 0x6806c4dad4000000 0x09e03f3800000000 0x082780fce0000000

def z1260 : W := mkw 0x00feb4a400000003 0xe003fad290000000 0xfdfffffe00000000 0x7ff7fffff8000000

def z1261 : W := mkw 0x004d123500000001 0x20013448d4000000 0x5dcc3f3f80000000 0x7d7730fcfe000000

def z1262 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x7fec3f3e71c3c72b 0xfdffb0fcf9c70f1c

def z1263 : W := mkw 0x204c182c1082c609 0x20813060b0420b18 0x5ecc383e7003c723 0xdd7b30e0f9c00f1c

def z1264 : W := mkw 0x80fe90246b68020b 0xa603fa4091ada008 0xfcffc0067ffc031f 0x83f3ff0019fff00c

def z1265 : W := mkw 0x0800404280040944 0x102001010a001025 0xf437c0c78e7c7ffe 0xf7d0df031e39f1ff

def z1266 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x5def3fff80000000 0x7d77bcfffe000000

def z1267 : W := mkw 0x010176f780000000 0x780405dbde000000 0x1dc03fff80000000 0x7c7700fffe000000

def z1268 : W := mkw 0x700009081493e6a8 0x01c0002420524f9a 0x020000000db3e7fd 0x800800000036cf9f

def z1269 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xedeb3f39800024fc 0xefb7acfce6000093

def z1270 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdfffffff3fc001a 0x7ff7ffffffcff000

def z1271 : W := mkw 0x384d527fa1d48fcd 0x30e13549fe87523f 0xc00fc03f81fc07d8 0x43003f00fe07f01f

def z1272 : W := mkw 0x600009081483f638 0x0180002420520fd8 0x020000000003ff20 0x0008000000000ffc

def z1273 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0x3df4ffff80000000 0x7cf7d3fffe000000

def z1274 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xecfbc0007fbc001d 0x83b3ef0001fef000

def z1275 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdfffffff2000002 0x7ff7ffffffc80000

def z1276 : W := mkw 0x200008081082c400 0x0080002020420b10 0x5ecc383e71c3c72b 0xdd7b30e0f9c70f1c

def z1277 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xedfbfff980000000 0x6fb7efffe6000000

def z1278 : W := mkw 0x01b3f6f780000002 0xf806cfdbde000000 0xed3bffff80000000 0x7fb4effffe000000

def z1279 : W := mkw 0x40002d8014037030 0x410000b600500dc0 0x0bc03fc07003f821 0x3c2f00ff01c00fe0

def z1280 : W := mkw 0xc0b2ad805e2b7032 0xc702cab60178adc0 0x3ff33fc07e33f827 0xbcffccff01f8cfe0

def z1281 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0x2f2b07398db3a4e5 0xecbcac1ce636ce93

def z1282 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xedeb3fff80000000 0x7fb7acfffe000000

def z1283 : W := mkw 0xc0b2ad805e2b7032 0xc702cab60178adc0 0xfffbffc07fbff83f 0xbfffefff01feffe0

def z1284 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x4ecc383e71c38729 0xcd3b30e0f9c70e1c

def z1285 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x7ff03fc07e03fc2f 0xfdffc0ff01f80ff0

def z1286 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff804067fe 0xfff7fffffe01019f

def z1287 : W := mkw 0x814ff6f7a1680001 0xfa053fdbde85a000 0xc10fffff81fc0018 0x7f043ffffe07f000

def z1288 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x01c03f3800000000 0x080700fce0000000

def z1289 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xbff03fc1fe03f8f7 0xbeffc0ff07f80fe3

def z1290 : W := mkw 0x81fff6f7eb680003 0xfe07ffdbdfada000 0xfdffffff8ffc001c 0x7ff7fffffe3ff000

def z1291 : W := mkw 0x81fff6f7ca280003 0xfe07ffdbdf28a000 0xfdffffff8e7c001e 0xfff7fffffe39f000

def z1292 : W := mkw 0x010176f780000000 0x780405dbde000000 0x1114ffff80000000 0x7c4453fffe000000

def z1293 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff82007fe6 0xfff7fffffe0801ff

def z1294 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398fffa4ff 0xefbcac1ce63ffe93

def z1295 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff800c00d0 0x7ff7fffffe003003

def z1296 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x09eb3ff800000000 0x3c27acffe0000000

def z1297 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x7edc38fe71c3c72b 0xfdfb70e3f9c70f1c

def z1298 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff800038c0 0x7ff7fffffe0000e3

def z1299 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdffffff8e000004 0x7ff7fffffe380000

def z1300 : W := mkw 0x700009085e93f4b0 0x05c00024217a4fd2 0x020000007e03fce7 0x8008000001f80ff3

def z1301 : W := mkw 0x89fff6f7ca2c0947 0xfe27ffdbdf28b025 0xfdffffff8e7c7ffe 0xfff7fffffe39f1ff

def z1302 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0c07ffc381f 0xa3f3ff0301fff0e0

def z1303 : W := mkw 0x010176f780000000 0x780405dbde000000 0xc10b3fff80000000 0x7f042cfffe000000

def z1304 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff80004022 0xfff7fffffe000100

def z1305 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x2bf03fc07e03f825 0x3cafc0ff01f80fe0

def z1306 : W := mkw 0x80fe90246b680003 0xa603fa4091ada000 0xfcfff8067ffc001f 0x93f3ffe019fff000

def z1307 : W := mkw 0x0800404280040944 0x102001010a001025 0x1014c0c7824c7ffe 0xf44053031e0931ff

def z1308 : W := mkw 0x70b009085e93f4b2 0x05c2c024217a4fd2 0xfefb00007fb3fcff 0x83fbec0001fecff3

def z1309 : W := mkw 0x09fff6f780040947 0xf827ffdbde001025 0xfdffffff804c47fa 0xfff7fffffe01311f

def z1310 : W := mkw 0x58b167d3ce1539f6 0x5562c59f4f3854e7 0xa133c7c18e3c38d4 0x2284cf1f0638f0e3

def z1311 : W := mkw 0x010176f780000000 0x780405dbde000000 0xa110ffff80000000 0x7e8443fffe000000

def z1312 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xe13fffff80000000 0x7f84fffffe000000

def z1313 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfcffc0067ffc071f 0xc3f3ff0019fff01c

def z1314 : W := mkw 0x01b3e6d380000002 0xd806cf9b4e000000 0xfdfbfff980000000 0x7ff7efffe6000000

def z1315 : W := mkw 0x00b1269100000002 0x4002c49a44000000 0xedeb3f3980000000 0x6fb7acfce6000000

def z1316 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xf1ffffff80000000 0x73c7fffffe000000

def z1317 : W := mkw 0x81ffb6b56b680003 0xee07fedad5ada000 0x09eb3f387ffc001f 0x8827acfce1fff000

def z1318 : W := mkw 0x80fea4806b680003 0xc603fa9201ada000 0xfcfff8c07ffc001f 0x93f3ffe301fff000

def z1319 : W := mkw 0x00fc34a400000003 0x6003f0d290000000 0x3df83ff800000000 0x3cf7e0ffe0000000

def z1320 : W := mkw 0x00ffa69100000003 0xc003fe9a44000000 0xfdfffff980000000 0x7ff7ffffe6000000

def z1321 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xecefc0007dfc001d 0x83b3bf0001f7f000

def z1322 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x12c4383e7043c302 0x184b10e0f9c10f0c

def z1323 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x1bf03fc07e03f823 0x3c6fc0ff01f80fe0

def z1324 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x19ef3f3e00000000 0x1867bcfcf8000000

def z1325 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0x18ffc0007ffc001f 0x8063ff0001fff000

def z1326 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdfffffff3cc001f 0xfff7ffffffcf3000

def z1327 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x13d03fc07203d802 0x184f40ff01c80f60

def z1328 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xcb2b07398db3a4f9 0x6f2cac1ce636ce93

def z1329 : W := mkw 0x40b2ad805e037032 0xc502cab601780dc0 0xbff3ffc07e03f827 0xbeffcfff01f80fe0

def z1330 : W := mkw 0x014fd27780000001 0xb8053f49de000000 0xfdefff3f80000000 0x7ff7bffcfe000000

def z1331 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0xfff43fc7fe43ffff 0xffffd0ff1ff90fff

def z1332 : W := mkw 0x08fc74e680040947 0x7023f1d39a001025 0xfdfcffff824c7ffe 0xfff7f3fffe0931ff

def z1333 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xa8fbc0007ffc001f 0x82a3ef0001fff000

def z1334 : W := mkw 0x00fc34a400000003 0x6003f0d290000000 0x09e83f3800000000 0x0827a0fce0000000

def z1335 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2f073f8df3a7fd 0xefbcbc1cfe37ce9f

def z1336 : W := mkw 0x01ffb6b521400003 0xe807fedad4850000 0x5def3f3871c0000b 0x8977bcfce1c70000

def z1337 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x5ecc383e71c3870b 0xc97b30e0f9c70e1c

def z1338 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0xa9fbff3800000000 0x0aa7effce0000000

def z1339 : W := mkw 0x014d76f780000001 0x780535dbde000000 0xfddcffff80000000 0x7ff773fffe000000

def z1340 : W := mkw 0x01fff6f780000003 0xf807ffdbde000000 0xfdffffff800004d8 0x7ff7fffffe000013

def z1341 : W := mkw 0x01fff6f7ca000003 0xfc07ffdbdf280000 0xfdfffffffc000001 0x7ff7fffffff00000

def z1342 : W := mkw 0x700009081493e6a8 0x01c0002420524f9a 0x020000000003e7e0 0x0008000000000f9f

def z1343 : W := mkw 0x01fff6f7a1400003 0xf807ffdbde850000 0xfdfffffff1800001 0x7ff7ffffffc60000

def z1344 : W := mkw 0x2000182c1082c608 0x20800060b0420b18 0x5ec4383e7043c72b 0xdd7b10e0f9c10f1c

def z1345 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0x56c4383e7043c72a 0xdd5b10e0f9c10f1c

def z1346 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xfdffc7007ffc001f 0xaff7ff1c01fff000

def z1347 : W := mkw 0x7000090835d3e6a8 0x01c0002420d74f9a 0x020000007db38001 0x0008000001f6ce00

def z1348 : W := mkw 0x89fff6f7eb6c0947 0xfe27ffdbdfadb025 0xfdfffffff24c7ffe 0xfff7ffffffc931ff

def z1349 : W := mkw 0x780009085e97fdf4 0x05e00024217a5ff7 0x020000007fffffff 0x8008000001ffffff

def z1350 : W := mkw 0x0800404280040944 0x102001010a001025 0xfd34c7c7824c7ffe 0xfff4d31f1e0931ff

def z1351 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xdcefc0007dfc001b 0x8373bf0001f7f000

def z1352 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x2ff03fc07e03b825 0xacbfc0ff01f80ee0

def z1353 : W := mkw 0x804e800021680001 0x82013a000085a000 0xfcefc0007dfc001f 0x83f3bf0001f7f000

def z1354 : W := mkw 0x204c182c31c2c609 0x20813060b0c70b18 0xfecc383e71c3c73f 0xdffb30e0f9c70f1c

def z1355 : W := mkw 0x004d123500000001 0x20013448d4000000 0x09eb3f3800000000 0x0827acfce0000000

def z1356 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398db3a0d5 0x6fbcac1ce636ce83

def z1357 : W := mkw 0x014fb6b500000001 0xe8053edad4000000 0x010b3f3800000000 0x08042cfce0000000

def z1358 : W := mkw 0x78015b7f9497efec 0x31e0056dfe525fbf 0x03003fff8003ffe0 0x7c0c00fffe000fff

def z1359 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xcf2b07398db384f9 0xcf3cac1ce636ce13

def z1360 : W := mkw 0x01ffb6b500000003 0xe807fedad4000000 0x4deb3f3800000000 0x4d37acfce0000000

def z1361 : W := mkw 0x700103190491a4a0 0x01c0040c64124692 0xef2b07398df3e7ff 0xefbcac1ce637cf9f

def z1362 : W := mkw 0x010176f780000000 0x780405dbde000000 0x01003fff80007820 0x7c0400fffe0001e0

def z1363 : W := mkw 0x40b02d805e037032 0x4502c0b601780dc0 0x7ff83fc07f83f82f 0xbdffe0ff01fe0fe0

def z1364 : W := mkw 0x80fe80006b680003 0x8603fa0001ada000 0xe03fc0007ffc001f 0x8380ff0001fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z8,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z9,z6]),(0,[z0,z1,z2,z3,z5,z10,z11]),(0,[z12,z0,z1,z2,z3,z5,z6])],[(0,[z13,z0,z1,z2,z3,z5,z6]),(0,[z1,z1,z14,z2,z3,z5,z6]),(0,[z1,z14,z15,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z17,z3,z5,z6]),(0,[z0,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z19,z20])],[(0,[z21,z22,z1,z2,z3,z5,z6]),(0,[z1,z2,z23,z3,z5,z6,z24]),(0,[z0,z1,z25,z3,z26,z5,z6]),(0,[z0,z27,z1,z2,z3,z5,z6]),(0,[z0,z28,z2,z3,z29,z5,z6]),(0,[z0,z1,z2,z30,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z10,z31]),(0,[z32,z0,z1,z2,z3,z5,z11]),(0,[z0,z1,z2,z3,z5,z6,z33])],[(0,[z1,z14,z2,z3,z29,z5,z6]),(0,[z0,z1,z2,z3,z34,z5,z6]),(0,[z0,z1,z2,z35,z3,z5,z6]),(0,[z36,z1,z37,z2,z3,z5,z6]),(0,[z0,z1,z2,z38,z3,z5,z6]),(0,[z39,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z40,z3,z5,z6]),(0,[z41,z27,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z42,z6]),(0,[z0,z1,z43,z2,z44,z5,z6]),(0,[z0,z1,z45,z3,z5,z46,z6]),(0,[z1,z2,z3,z47,z5,z46,z6]),(0,[z0,z1,z2,z3,z5,z6,z48])],[(0,[z0,z1,z2,z3,z5,z49,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z50,z0,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z5,z6,z6,z24]),(0,[z0,z51,z1,z2,z3,z5,z6])],[(0,[z22,z1,z2,z52,z3,z5,z6]),(0,[z53,z1,z15,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z54,z5,z6]),(0,[z0,z1,z2,z55,z3,z5,z6]),(0,[z0,z1,z56,z37,z3,z5,z6]),(1,[z57,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z58,z5,z6])],[(0,[z22,z59,z1,z2,z3,z5,z6]),(0,[z53,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z60,z5,z6]),(0,[z0,z1,z2,z3,z61,z5,z6])],[(1,[z0,z1,z2,z62,z5,z6]),(0,[z0,z1,z2,z63,z3,z5,z6]),(0,[z0,z1,z2,z23,z64,z5,z6]),(0,[z0,z65,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z66,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z67,z19]),(0,[z0,z1,z2,z3,z5,z68,z19]),(0,[z69,z0,z1,z2,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z5,z6])],[(0,[z22,z1,z15,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z71]),(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z67,z6,z24]),(0,[z0,z1,z2,z73,z3,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z19]),(0,[z75,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z76,z77]),(0,[z0,z1,z2,z3,z5,z6,z78])],[(0,[z79,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z24]),(0,[z80,z81,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z82]),(0,[z0,z1,z2,z3,z83,z5,z6]),(0,[z0,z1,z2,z3,z84,z5,z6])],[(0,[z1,z14,z2,z3,z5,z6,z20]),(0,[z22,z1,z2,z3,z29,z5,z6]),(0,[z36,z1,z2,z3,z5,z85,z6])],[(0,[z0,z1,z2,z3,z5,z68,z24]),(0,[z86,z36,z1,z2,z3,z5,z6]),(0,[z87,z0,z1,z2,z3,z5,z6])],[(0,[z88,z0,z1,z2,z3,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z6]),(0,[z90,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z91,z6])],[(0,[z1,z15,z2,z52,z3,z5,z6]),(0,[z0,z1,z2,z92,z3,z5,z6]),(0,[z0,z1,z2,z3,z93,z5,z6]),(0,[z0,z1,z2,z3,z5,z94,z6]),(0,[z95,z0,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z3,z96,z5,z6]),(0,[z90,z0,z1,z56,z3,z5,z6]),(0,[z0,z1,z56,z2,z3,z5,z6])],[(0,[z32,z1,z14,z2,z3,z5,z6]),(0,[z97,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z98]),(0,[z99,z0,z1,z2,z3,z5,z6]),(0,[z100,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z64,z5,z6,z11]),(0,[z0,z1,z101,z2,z3,z5,z6]),(0,[z102,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z103,z1,z2,z3,z5,z6,z24]),(0,[z104,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z105,z3,z5,z6]),(0,[z106,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z107,z3,z5,z6,z24]),(0,[z36,z1,z45,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z108,z5,z6]),(0,[z0,z1,z2,z3,z96,z29,z6]),(0,[z0,z1,z2,z3,z5,z6,z109]),(1,[z1,z2,z3,z110,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z11])],[(0,[z111,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z6,z112]),(0,[z0,z59,z2,z107,z3,z5,z6]),(0,[z0,z1,z2,z3,z113,z5,z6]),(0,[z0,z1,z114,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z115,z5,z6])],[(0,[z97,z0,z1,z15,z3,z5,z6]),(0,[z1,z37,z2,z3,z5,z6,z24]),(0,[z116,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z117,z6]),(0,[z0,z118,z1,z2,z3,z5,z6]),(0,[z0,z1,z119,z2,z3,z5,z6])],[(0,[z120,z0,z1,z2,z3,z5,z6]),(0,[z0,z121,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z6,z6]),(0,[z122,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z123,z6]),(0,[z124,z0,z1,z2,z3,z5,z6]),(1,[z125,z1,z2,z3,z5,z6])],[(0,[z22,z1,z43,z2,z3,z5,z6]),(0,[z126,z0,z1,z2,z3,z5,z6]),(0,[z127,z0,z1,z2,z64,z5,z6]),(0,[z0,z1,z2,z3,z5,z128,z6]),(1,[z0,z1,z2,z129,z5,z6])],[(0,[z0,z1,z2,z3,z5,z130,z6]),(0,[z0,z1,z2,z3,z5,z131,z6]),(0,[z132,z1,z2,z3,z5,z6,z24]),(0,[z133,z0,z1,z37,z3,z5,z6]),(0,[z0,z1,z2,z134,z3,z135,z6])]],
   [[(0,[z0,z1,z2,z136,z3,z5,z6]),(0,[z0,z137,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z3,z139,z5,z6]),(0,[z132,z0,z1,z56,z3,z5,z6]),(0,[z140,z0,z1,z2,z3,z5,z6]),(0,[z32,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z3,z5,z6,z141])],[(0,[z0,z142,z1,z2,z3,z5,z6]),(1,[z36,z1,z2,z3,z5,z24]),(0,[z143,z0,z1,z144,z3,z5,z6]),(0,[z0,z1,z145,z2,z3,z5,z6]),(0,[z146,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z6]),(0,[z147,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z96,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z6])],[(0,[z0,z1,z2,z149,z3,z5,z6]),(0,[z0,z1,z2,z150,z3,z5,z6]),(0,[z0,z1,z151,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z152,z6,z24]),(0,[z41,z0,z59,z2,z3,z5,z6]),(0,[z125,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z153,z6])],[(0,[z36,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z154,z6]),(0,[z143,z155,z1,z2,z3,z5,z6])],[(0,[z0,z1,z156,z2,z3,z5,z6]),(0,[z0,z1,z2,z157,z3,z5,z6]),(0,[z0,z1,z2,z3,z158,z5,z6]),(0,[z74,z1,z2,z3,z5,z6,z24]),(0,[z1,z2,z44,z3,z5,z6,z24]),(0,[z1,z2,z3,z5,z6,z24,z11]),(1,[z0,z1,z144,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z159,z6]),(0,[z0,z1,z2,z160,z3,z5,z6])],[(0,[z1,z2,z161,z3,z5,z6,z24]),(0,[z162,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z163,z2,z3,z5,z6]),(1,[z0,z1,z3,z5,z6,z164])],[(0,[z53,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z24,z31]),(0,[z36,z1,z2,z3,z5,z91,z6]),(1,[z155,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z165]),(0,[z0,z1,z166,z2,z3,z5,z6]),(0,[z132,z0,z1,z2,z3,z5,z67])],[(0,[z36,z1,z56,z2,z3,z5,z6]),(0,[z133,z167,z1,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z5,z168]),(1,[z169,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z2,z3,z96,z6]),(0,[z0,z1,z2,z3,z5,z6,z170]),(0,[z0,z1,z2,z171,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z172,z6]),(0,[z0,z1,z173,z2,z3,z5,z6]),(0,[z133,z0,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z29,z6]),(0,[z0,z1,z2,z129,z5,z67,z6]),(0,[z0,z1,z2,z3,z5,z6,z174]),(0,[z1,z2,z3,z5,z77,z6,z33])],[(0,[z0,z1,z2,z52,z3,z5,z6]),(0,[z0,z175,z1,z2,z3,z5,z6]),(0,[z127,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z6,z176]),(1,[z0,z1,z2,z3,z5,z165]),(0,[z80,z0,z1,z2,z3,z5,z19]),(1,[z79,z0,z1,z26,z5,z6])],[(0,[z22,z0,z1,z2,z3,z5,z6]),(0,[z1,z14,z2,z23,z3,z5,z6]),(0,[z0,z59,z1,z2,z3,z5,z6])],[(0,[z22,z1,z2,z3,z177,z5,z6]),(0,[z0,z1,z178,z2,z3,z5,z6]),(0,[z133,z122,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z179,z3,z5,z6]),(0,[z0,z1,z2,z3,z180,z5,z6])],[(0,[z1,z14,z2,z3,z5,z77,z6]),(0,[z181,z0,z1,z2,z3,z5,z6]),(0,[z0,z182,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z183,z6]),(0,[z184,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z110,z5,z6]),(1,[z0,z1,z2,z185,z5,z6]),(0,[z86,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z186,z5,z6]),(0,[z1,z14,z2,z3,z5,z68,z6]),(0,[z0,z187,z1,z2,z3,z5,z6]),(0,[z0,z1,z15,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z131,z11]),(0,[z0,z1,z2,z3,z188,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z189]),(0,[z190,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z191,z6])],[(0,[z0,z1,z2,z3,z192,z5,z6]),(0,[z0,z1,z56,z25,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z193]),(0,[z0,z28,z1,z2,z3,z29,z6]),(0,[z0,z1,z2,z3,z194,z5,z6])],[(0,[z195,z0,z1,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z107,z5,z6]),(0,[z0,z1,z2,z3,z29,z5,z6]),(0,[z0,z1,z2,z3,z5,z19,z11])]],
   [[(0,[z22,z0,z14,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z131,z6]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z23,z5,z152,z6])],[(0,[z79,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z196,z2,z3,z5,z6]),(0,[z0,z1,z197,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z198,z5,z6]),(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z200,z3,z201,z5,z6]),(0,[z50,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z43,z37,z3,z5,z6]),(0,[z41,z0,z1,z202,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z193]),(0,[z0,z1,z2,z3,z5,z19,z31]),(0,[z0,z1,z3,z96,z5,z46,z6]),(0,[z0,z1,z2,z3,z76,z77,z6])],[(0,[z99,z1,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z23,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z19,z6]),(0,[z36,z1,z2,z44,z3,z5,z6]),(1,[z167,z1,z2,z3,z5,z6]),(0,[z203,z1,z204,z2,z3,z5,z6]),(0,[z0,z205,z1,z2,z3,z5,z6]),(0,[z206,z0,z1,z2,z3,z5,z6]),(0,[z86,z0,z1,z207,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z208,z5,z6]),(0,[z0,z1,z2,z209,z3,z5,z6]),(0,[z0,z1,z2,z210,z3,z5,z6])],[(0,[z22,z1,z2,z3,z5,z77,z6]),(0,[z0,z1,z2,z3,z5,z211,z6]),(0,[z0,z1,z2,z3,z5,z6,z212]),(0,[z143,z0,z2,z3,z5,z135,z6])],[(0,[z1,z14,z2,z3,z93,z5,z6]),(0,[z22,z1,z2,z3,z5,z68,z6]),(1,[z213,z1,z2,z3,z85,z6]),(0,[z0,z214,z1,z2,z3,z5,z6])],[(0,[z0,z1,z215,z2,z3,z5,z6]),(0,[z22,z74,z1,z2,z3,z5,z6]),(0,[z216,z0,z1,z52,z3,z5,z6]),(0,[z217,z0,z1,z2,z3,z5,z6]),(0,[z80,z1,z2,z3,z5,z6,z24]),(1,[z122,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z23,z107,z5,z6]),(1,[z0,z28,z2,z3,z29,z6]),(0,[z0,z1,z2,z3,z29,z152,z6]),(0,[z86,z0,z1,z218,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z219,z6]),(0,[z0,z1,z2,z3,z5,z6,z220]),(0,[z0,z1,z2,z221,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z20])]],
   [[(0,[z222,z59,z1,z2,z3,z5,z6]),(1,[z0,z1,z45,z3,z46,z6]),(0,[z223,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z224]),(0,[z0,z1,z2,z225,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z6,z11]),(0,[z226,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z227,z3,z5,z6]),(0,[z133,z0,z2,z25,z3,z5,z6]),(0,[z0,z155,z1,z2,z3,z5,z6]),(1,[z0,z1,z207,z3,z5,z6])],[(0,[z228,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z229,z3,z5,z6]),(0,[z36,z1,z2,z52,z3,z5,z6]),(0,[z1,z2,z134,z3,z5,z6,z24]),(0,[z0,z169,z1,z2,z3,z5,z6]),(0,[z0,z1,z43,z2,z3,z5,z6]),(0,[z79,z0,z1,z2,z5,z6,z11]),(1,[z132,z0,z1,z3,z5,z20]),(0,[z0,z1,z2,z23,z3,z5,z68]),(0,[z0,z1,z3,z5,z68,z6,z164]),(0,[z0,z1,z2,z3,z77,z6,z31])],[(0,[z1,z14,z2,z3,z5,z6,z31]),(0,[z32,z22,z1,z2,z3,z5,z6]),(0,[z97,z22,z1,z2,z3,z5,z6]),(0,[z230,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z231,z6]),(0,[z36,z59,z1,z2,z3,z5,z6]),(1,[z133,z0,z25,z3,z5,z6]),(0,[z143,z0,z28,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z29,z46,z6]),(0,[z232,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z233]),(0,[z0,z234,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z235,z5,z6]),(0,[z1,z2,z3,z5,z6,z24,z10]),(0,[z1,z43,z2,z3,z5,z6,z24]),(0,[z1,z2,z3,z236,z5,z6,z24]),(0,[z0,z1,z237,z2,z3,z5,z6]),(1,[z0,z1,z238,z3,z5,z6])],[(0,[z216,z0,z1,z2,z3,z5,z239]),(0,[z0,z1,z240,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z241]),(0,[z242,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z218,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z243,z6])],[(0,[z36,z97,z1,z2,z3,z5,z6]),(0,[z36,z1,z15,z2,z3,z5,z6]),(0,[z1,z2,z3,z93,z5,z85,z6])],[(0,[z244,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z245,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z246,z6])]],
   [[(0,[z1,z14,z2,z3,z96,z5,z6]),(0,[z36,z1,z2,z3,z29,z5,z6]),(0,[z133,z0,z1,z25,z3,z5,z6]),(0,[z90,z0,z1,z37,z3,z5,z6]),(1,[z116,z1,z2,z3,z5,z6]),(0,[z247,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z107,z26,z5,z6]),(0,[z80,z0,z2,z3,z5,z6,z10])],[(0,[z248,z0,z1,z2,z3,z5,z6]),(0,[z249,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z250]),(0,[z251,z0,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z45,z3,z5,z6])],[(0,[z1,z14,z156,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z6,z31]),(0,[z28,z1,z252,z2,z3,z5,z6]),(0,[z0,z1,z44,z3,z5,z6,z20])],[(1,[z1,z2,z3,z5,z67,z24]),(0,[z106,z36,z1,z2,z3,z5,z6]),(0,[z253,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z254,z6])],[(0,[z255,z0,z1,z2,z3,z5,z6]),(0,[z256,z0,z1,z2,z3,z5,z6]),(0,[z257,z0,z1,z2,z201,z5,z6]),(0,[z213,z1,z2,z3,z5,z85,z6]),(0,[z0,z167,z1,z2,z3,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z257,z1,z2,z3,z5,z6,z24]),(0,[z0,z258,z1,z2,z3,z5,z6]),(0,[z259,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z3,z29,z6]),(0,[z0,z1,z2,z3,z5,z6,z260]),(0,[z0,z1,z2,z3,z5,z261,z6])],[(0,[z181,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z177,z5,z6]),(0,[z53,z0,z1,z2,z200,z5,z6]),(0,[z133,z0,z1,z2,z62,z5,z6]),(0,[z262,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z22,z1,z2,z3,z263,z5,z6]),(0,[z99,z0,z1,z2,z3,z85,z6]),(0,[z264,z0,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z6,z20])],[(0,[z22,z1,z2,z3,z26,z5,z6]),(0,[z50,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z29,z5,z6,z24])],[(0,[z0,z1,z2,z3,z265,z5,z6]),(0,[z0,z28,z1,z2,z3,z135,z6]),(0,[z0,z1,z2,z3,z5,z6,z266])],[(1,[z1,z267,z2,z3,z5,z6]),(0,[z97,z0,z1,z52,z3,z5,z6]),(0,[z268,z0,z1,z2,z3,z5,z6]),(0,[z99,z0,z1,z2,z3,z93,z6]),(0,[z41,z0,z1,z2,z64,z5,z6]),(0,[z269,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z270,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z271]),(0,[z59,z1,z101,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z5,z77])],[(0,[z272,z0,z1,z2,z3,z5,z6]),(0,[z79,z0,z1,z2,z23,z5,z6]),(0,[z273,z0,z1,z2,z3,z5,z6])],[(0,[z36,z99,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z93,z5,z6,z24]),(0,[z274,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z23,z3,z5,z6]),(1,[z0,z275,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z276,z5,z6]),(0,[z0,z1,z2,z3,z5,z277,z6]),(0,[z1,z2,z3,z5,z19,z6,z24]),(0,[z111,z0,z1,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z278,z6])]],
   [[(0,[z0,z1,z2,z3,z279,z5,z6]),(0,[z0,z1,z2,z3,z5,z280,z6]),(0,[z36,z1,z245,z2,z3,z5,z6]),(0,[z0,z28,z2,z3,z5,z6,z10]),(0,[z0,z1,z2,z3,z281,z5,z6]),(0,[z0,z1,z2,z3,z5,z77,z6])],[(0,[z1,z14,z2,z3,z5,z6,z10]),(0,[z1,z2,z3,z76,z5,z6,z24]),(0,[z0,z1,z2,z282,z3,z5,z6]),(0,[z283,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z284,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z68,z6])],[(0,[z0,z285,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z286,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z287]),(0,[z133,z0,z1,z2,z3,z288,z6]),(0,[z0,z1,z43,z25,z3,z5,z6]),(1,[z0,z1,z2,z289,z5,z6]),(1,[z0,z1,z2,z290,z5,z6]),(0,[z0,z1,z2,z291,z3,z5,z6])],[(0,[z133,z36,z1,z2,z3,z5,z6]),(0,[z292,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z293,z6]),(0,[z0,z1,z2,z3,z294,z5,z6]),(0,[z0,z1,z2,z3,z295,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z296])],[(0,[z0,z1,z2,z3,z5,z193,z6]),(0,[z1,z2,z3,z297,z5,z152,z6])],[(0,[z298,z0,z1,z2,z3,z5,z6]),(0,[z213,z1,z2,z3,z5,z6,z24]),(0,[z41,z0,z1,z299,z3,z5,z6]),(0,[z0,z1,z2,z3,z300,z5,z6]),(0,[z0,z1,z2,z301,z3,z5,z6]),(0,[z302,z0,z1,z2,z3,z5,z6])],[(0,[z99,z22,z1,z2,z3,z5,z6]),(0,[z41,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z303,z3,z5,z6]),(0,[z0,z304,z1,z2,z3,z5,z6]),(0,[z0,z74,z2,z3,z5,z135,z6])],[(0,[z36,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z24]),(0,[z0,z1,z37,z3,z5,z6,z20]),(0,[z32,z305,z1,z2,z3,z5,z6]),(0,[z0,z306,z1,z2,z3,z5,z6])]],
   [[(0,[z22,z1,z2,z3,z5,z307,z6]),(0,[z36,z0,z1,z2,z3,z5,z131]),(0,[z0,z1,z2,z3,z5,z6,z308])],[(0,[z1,z14,z2,z229,z3,z5,z6]),(0,[z1,z14,z43,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z6,z10]),(0,[z1,z2,z3,z26,z5,z6,z24])],[(0,[z249,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z309,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z310]),(0,[z311,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z312,z3,z5,z6]),(0,[z0,z1,z313,z2,z3,z5,z6]),(0,[z143,z36,z1,z2,z3,z5,z6]),(0,[z314,z0,z1,z2,z3,z5,z6]),(0,[z315,z0,z1,z2,z3,z5,z6]),(0,[z316,z0,z1,z2,z3,z5,z6])],[(0,[z0,z317,z1,z2,z3,z5,z6]),(0,[z199,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z318,z6]),(0,[z0,z1,z319,z2,z3,z5,z6]),(0,[z320,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z56,z3,z5,z46,z6]),(0,[z0,z1,z2,z23,z3,z5,z11])],[(0,[z22,z28,z1,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z24]),(1,[z0,z1,z2,z3,z288,z6]),(0,[z321,z0,z1,z2,z3,z5,z6]),(0,[z322,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z278,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z323]),(0,[z79,z0,z1,z56,z3,z5,z6]),(0,[z0,z1,z56,z44,z3,z5,z6]),(0,[z0,z1,z2,z324,z3,z5,z6]),(0,[z127,z0,z1,z2,z3,z5,z6]),(0,[z0,z325,z1,z2,z3,z5,z6]),(0,[z86,z0,z326,z2,z3,z5,z6])],[(0,[z0,z1,z267,z2,z3,z5,z6]),(0,[z327,z0,z1,z2,z3,z5,z6]),(0,[z53,z1,z2,z3,z201,z5,z6]),(1,[z36,z1,z2,z3,z5,z6]),(0,[z28,z1,z2,z3,z5,z6,z24]),(0,[z1,z328,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z329,z5,z6]),(0,[z143,z0,z1,z2,z330,z5,z6]),(0,[z80,z169,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z331,z6]),(0,[z1,z2,z52,z3,z5,z6,z24]),(0,[z36,z1,z2,z23,z3,z5,z6]),(1,[z36,z1,z2,z3,z5,z131]),(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z333,z3,z5,z6]),(0,[z0,z334,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z31])]],
   [[(0,[z335,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z336,z6]),(0,[z1,z2,z3,z201,z5,z6,z24]),(0,[z1,z2,z3,z5,z131,z6,z24]),(1,[z143,z0,z2,z3,z135,z6])],[(0,[z0,z1,z2,z337,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z338,z6]),(0,[z1,z56,z2,z3,z5,z6,z24]),(0,[z36,z1,z2,z3,z5,z77,z6]),(1,[z0,z1,z2,z330,z5,z6]),(0,[z339,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z340,z6])],[(0,[z22,z1,z2,z3,z201,z5,z6]),(0,[z0,z1,z341,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z68,z6]),(0,[z0,z1,z2,z299,z3,z5,z6]),(0,[z0,z1,z2,z64,z26,z5,z6]),(0,[z0,z1,z3,z5,z46,z6,z20]),(0,[z0,z1,z2,z5,z68,z6,z11]),(1,[z1,z2,z3,z5,z6,z342])],[(0,[z0,z1,z2,z3,z343,z5,z6]),(0,[z0,z1,z2,z3,z5,z344,z6]),(0,[z0,z1,z2,z345,z3,z5,z6]),(0,[z127,z0,z1,z2,z134,z5,z6])],[(0,[z0,z1,z2,z3,z263,z5,z6]),(0,[z69,z1,z2,z3,z5,z46,z6]),(0,[z127,z0,z1,z2,z3,z152,z6]),(1,[z0,z326,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z346,z6]),(0,[z53,z22,z1,z2,z3,z5,z6]),(1,[z222,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z5,z6])],[(0,[z0,z1,z2,z3,z5,z347,z6]),(0,[z0,z1,z2,z348,z3,z5,z6]),(0,[z203,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z349,z6])],[(0,[z133,z22,z1,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z293,z6]),(0,[z0,z1,z2,z350,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z351,z6]),(0,[z0,z1,z2,z3,z5,z352,z6]),(1,[z0,z1,z145,z3,z5,z6]),(0,[z32,z70,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z353,z5,z6])],[(0,[z22,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z354,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z355]),(0,[z0,z1,z2,z356,z3,z5,z6])],[(0,[z213,z216,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z93,z5,z6]),(0,[z357,z0,z1,z2,z3,z5,z6]),(0,[z80,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z358]),(0,[z269,z1,z2,z3,z26,z5,z6]),(0,[z359,z0,z1,z2,z3,z5,z6])],[(0,[z86,z22,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z24,z360]),(0,[z0,z1,z144,z2,z3,z5,z6]),(0,[z0,z361,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z96,z5,z6,z24]),(0,[z362,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z363,z6]),(0,[z0,z1,z2,z3,z5,z6,z364])],[(0,[z1,z14,z2,z134,z3,z5,z6]),(0,[z0,z1,z2,z365,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z310]),(0,[z0,z1,z2,z366,z3,z5,z6]),(1,[z0,z1,z2,z367,z152,z6])],[(0,[z36,z1,z2,z3,z5,z6,z11]),(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z127,z0,z1,z2,z134,z3,z6])],[(0,[z143,z22,z1,z2,z3,z5,z6]),(1,[z292,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z152,z135,z6]),(0,[z0,z1,z2,z3,z5,z369,z6]),(0,[z370,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z238,z3,z5,z68,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z371]),(0,[z1,z14,z2,z3,z5,z67,z6]),(0,[z216,z1,z2,z3,z5,z6,z24]),(0,[z213,z1,z15,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z6,z31]),(0,[z0,z1,z2,z3,z5,z372,z6]),(0,[z0,z1,z373,z2,z3,z5,z6]),(0,[z86,z0,z1,z2,z3,z76,z6])],[],[(1,[z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z374,z6]),(0,[z375,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z376,z5,z6]),(0,[z86,z377,z1,z2,z3,z5,z6])],[(0,[z88,z1,z14,z2,z3,z5,z6]),(0,[z79,z0,z1,z3,z5,z6,z20]),(1,[z1,z2,z3,z47,z5,z6]),(0,[z0,z1,z2,z134,z5,z152,z6])],[(0,[z0,z1,z2,z3,z5,z378,z6]),(0,[z36,z1,z2,z345,z3,z5,z6]),(0,[z90,z36,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z379]),(0,[z0,z2,z3,z29,z5,z135,z6]),(0,[z0,z1,z2,z3,z380,z5,z6]),(0,[z381,z0,z1,z2,z3,z5,z6]),(1,[z382,z1,z2,z3,z5,z6])],[(0,[z22,z1,z2,z134,z3,z5,z6]),(0,[z36,z1,z2,z3,z96,z5,z6]),(0,[z0,z1,z202,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z10]),(0,[z0,z1,z2,z3,z5,z6,z342])],[(0,[z383,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z384,z6]),(0,[z36,z1,z2,z3,z26,z5,z6]),(0,[z385,z0,z1,z2,z3,z5,z6]),(0,[z386,z0,z1,z2,z3,z5,z6]),(0,[z32,z0,z1,z2,z23,z5,z6])],[(0,[z387,z0,z1,z2,z3,z5,z6])]],
   [[(1,[z22,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z67,z6]),(0,[z388,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z389]),(0,[z1,z2,z3,z5,z6,z24,z390]),(0,[z0,z28,z1,z2,z3,z5,z6]),(0,[z0,z1,z391,z2,z3,z5,z6])],[(0,[z392,z0,z1,z2,z3,z5,z6]),(0,[z257,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z393]),(0,[z0,z1,z2,z394,z3,z5,z6]),(0,[z80,z0,z74,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z395])],[(1,[z0,z1,z2,z3,z396,z6])],[(0,[z383,z0,z14,z2,z3,z5,z6]),(0,[z397,z0,z1,z2,z3,z5,z6]),(0,[z398,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z399,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z400])],[(0,[z0,z1,z2,z3,z401,z5,z6]),(1,[z97,z1,z15,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z135,z6]),(0,[z244,z22,z1,z2,z3,z5,z6]),(0,[z402,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z201,z5,z6]),(0,[z1,z2,z3,z64,z5,z6,z24]),(1,[z1,z403,z2,z3,z5,z6]),(0,[z132,z0,z1,z2,z3,z5,z20])],[(0,[z22,z0,z103,z2,z3,z5,z6]),(0,[z404,z0,z1,z2,z3,z5,z6]),(0,[z405,z0,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z368,z3,z5,z6]),(0,[z406,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z407]),(0,[z0,z1,z2,z408,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z409]),(0,[z0,z1,z2,z3,z5,z6,z410]),(0,[z86,z0,z1,z2,z3,z5,z31])]],
   [[(0,[z1,z14,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z411,z5,z6]),(0,[z412,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z413,z2,z3,z5,z6]),(0,[z213,z99,z1,z2,z3,z5,z6]),(0,[z414,z36,z1,z2,z3,z5,z6]),(0,[z132,z125,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z415,z5,z6]),(0,[z416,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z417,z6]),(0,[z127,z0,z1,z2,z5,z6,z11])],[(0,[z1,z14,z2,z200,z3,z5,z6]),(0,[z22,z1,z1,z2,z3,z5,z6]),(0,[z1,z2,z200,z3,z5,z6,z24]),(0,[z36,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z418,z6]),(0,[z0,z1,z25,z3,z5,z46,z6]),(0,[z0,z1,z2,z3,z5,z419,z6]),(0,[z420,z0,z1,z2,z3,z5,z6]),(0,[z421,z0,z1,z2,z3,z5,z6])],[(0,[z422,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z423,z5,z6]),(0,[z424,z0,z1,z2,z3,z5,z6]),(0,[z425,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z135,z6])],[(0,[z426,z0,z1,z2,z3,z5,z6]),(0,[z1,z215,z14,z2,z3,z5,z6]),(0,[z1,z14,z2,z3,z26,z5,z6]),(0,[z53,z1,z14,z2,z3,z5,z6]),(0,[z255,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z427])],[(0,[z97,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z428,z2,z3,z5,z6]),(0,[z182,z1,z2,z3,z5,z6,z24]),(0,[z32,z1,z2,z3,z5,z6,z24]),(0,[z429,z0,z1,z2,z3,z5,z6]),(0,[z79,z0,z1,z2,z26,z5,z6])],[(0,[z133,z1,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z135,z6]),(0,[z1,z2,z3,z5,z46,z6,z24]),(0,[z36,z1,z2,z3,z5,z6,z10]),(0,[z0,z1,z2,z3,z47,z5,z6])],[(0,[z216,z1,z2,z52,z3,z5,z6]),(0,[z430,z0,z1,z2,z3,z5,z6]),(0,[z431,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z22,z1,z14,z2,z3,z5,z6]),(0,[z50,z22,z1,z2,z3,z5,z6]),(0,[z432,z1,z2,z3,z5,z6,z24]),(0,[z127,z36,z1,z2,z3,z5,z6]),(0,[z433,z0,z1,z2,z3,z5,z6]),(0,[z0,z434,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z346,z6]),(0,[z435,z0,z1,z2,z3,z5,z6]),(0,[z213,z0,z1,z2,z3,z5,z6]),(0,[z36,z214,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z436,z5,z6]),(0,[z0,z1,z2,z3,z5,z437,z6]),(0,[z80,z0,z1,z2,z289,z5,z6]),(0,[z80,z0,z1,z2,z290,z5,z6]),(0,[z0,z438,z1,z2,z3,z5,z6]),(0,[z0,z1,z439,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z164])],[(0,[z86,z1,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z200,z3,z5,z6]),(0,[z36,z28,z1,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z5,z6]),(0,[z440,z0,z1,z2,z3,z5,z6]),(0,[z441,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z129,z3,z5,z6])],[(0,[z1,z14,z2,z25,z3,z5,z6]),(0,[z216,z97,z1,z2,z3,z5,z6]),(0,[z1,z45,z2,z3,z5,z6,z24]),(0,[z133,z0,z203,z2,z3,z5,z6]),(0,[z442,z0,z1,z2,z3,z5,z6])],[(0,[z443,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z444,z2,z3,z5,z6]),(0,[z0,z1,z445,z2,z3,z5,z6]),(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z367,z3,z6])],[(0,[z0,z1,z2,z3,z446,z5,z6]),(0,[z0,z1,z2,z3,z447,z5,z6]),(0,[z0,z1,z2,z448,z3,z5,z6])],[(0,[z143,z1,z14,z2,z3,z5,z6]),(0,[z1,z14,z2,z3,z76,z5,z6]),(0,[z0,z1,z449,z2,z3,z5,z6]),(0,[z36,z1,z43,z2,z3,z5,z6]),(0,[z0,z1,z450,z2,z3,z5,z6])],[(0,[z36,z1,z2,z3,z201,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z451]),(1,[z1,z452,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z453,z6]),(0,[z454,z0,z1,z2,z3,z5,z6]),(0,[z455,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z271,z24]),(0,[z0,z1,z2,z3,z5,z6,z456]),(0,[z0,z2,z3,z5,z19,z6,z10]),(0,[z0,z1,z2,z3,z5,z6,z457]),(1,[z0,z1,z56,z3,z5,z67]),(0,[z127,z0,z1,z2,z367,z5,z6])],[(1,[z1,z14,z2,z3,z5,z6]),(0,[z1,z313,z14,z2,z3,z5,z6]),(0,[z0,z1,z403,z2,z3,z5,z6]),(0,[z0,z1,z2,z134,z3,z5,z6])],[(0,[z22,z1,z2,z3,z5,z6,z458]),(0,[z459,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z460]),(0,[z0,z1,z461,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z64,z5,z6]),(0,[z22,z1,z2,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z462,z5,z6]),(0,[z1,z15,z2,z200,z3,z5,z6])],[(0,[z0,z1,z463,z2,z3,z5,z6]),(0,[z53,z0,z1,z2,z3,z5,z393]),(0,[z0,z1,z2,z3,z5,z464,z6]),(0,[z1,z2,z3,z5,z6,z427,z24]),(0,[z0,z1,z2,z3,z5,z67,z6]),(1,[z1,z2,z3,z297,z5,z6]),(0,[z0,z1,z2,z465,z3,z5,z6])],[(0,[z0,z1,z2,z3,z236,z5,z6]),(0,[z80,z36,z1,z2,z3,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z6]),(0,[z442,z1,z2,z3,z5,z77,z6])],[(0,[z22,z1,z2,z3,z76,z5,z6]),(0,[z36,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z466,z6]),(0,[z132,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z37,z2,z25,z3,z5,z6]),(0,[z41,z116,z1,z2,z3,z5,z6]),(0,[z222,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z414,z0,z1,z2,z3,z5,z6]),(0,[z0,z467,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z468,z5,z6]),(0,[z0,z1,z2,z3,z5,z469,z6]),(0,[z470,z1,z2,z3,z5,z68,z6])],[(0,[z249,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z3,z5,z6,z20]),(0,[z0,z1,z471,z2,z3,z5,z6]),(0,[z472,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z473,z6]),(1,[z0,z1,z2,z23,z5,z68])],[(0,[z216,z0,z1,z2,z3,z5,z474]),(1,[z1,z2,z3,z5,z6,z358]),(0,[z0,z1,z2,z3,z5,z475,z6]),(0,[z0,z1,z2,z476,z3,z5,z6])],[(1,[z1,z2,z3,z5,z6,z458]),(0,[z22,z1,z37,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z64,z5,z6]),(0,[z257,z0,z1,z2,z200,z5,z6]),(0,[z0,z1,z204,z2,z3,z5,z6]),(0,[z0,z1,z477,z2,z3,z5,z6]),(0,[z86,z302,z1,z2,z3,z5,z6])],[(0,[z127,z22,z1,z2,z3,z5,z6]),(0,[z0,z2,z107,z3,z64,z5,z6]),(0,[z478,z0,z1,z2,z3,z5,z6]),(0,[z479,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z480])],[(0,[z1,z14,z2,z3,z201,z5,z6]),(0,[z0,z1,z2,z481,z3,z5,z6]),(0,[z0,z1,z482,z2,z3,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z483,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z484]),(0,[z485,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z486]),(0,[z0,z487,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z488,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z489,z6]),(0,[z0,z1,z2,z490,z3,z5,z6])],[(0,[z79,z1,z2,z3,z5,z6,z24]),(0,[z491,z0,z1,z2,z3,z5,z6]),(0,[z80,z0,z1,z145,z3,z5,z6]),(0,[z492,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z493]),(0,[z0,z1,z494,z2,z3,z5,z6])]],
   [[(0,[z97,z1,z15,z2,z3,z5,z6]),(0,[z99,z1,z2,z3,z5,z6,z24]),(0,[z0,z74,z28,z2,z3,z5,z6])],[(0,[z383,z36,z1,z2,z3,z5,z6]),(0,[z0,z495,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z393]),(1,[z99,z1,z2,z3,z93,z6]),(0,[z1,z2,z3,z5,z6,z456,z24]),(0,[z0,z1,z2,z3,z5,z496,z6]),(0,[z79,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z43,z2,z5,z6,z11]),(0,[z0,z1,z2,z3,z5,z6,z497]),(0,[z0,z498,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z218,z3,z5,z6])],[(0,[z36,z1,z403,z2,z3,z5,z6]),(0,[z36,z1,z2,z134,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z135,z6]),(0,[z0,z1,z452,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z499]),(0,[z500,z0,z1,z2,z3,z5,z6])],[(0,[z41,z0,z2,z3,z64,z5,z6]),(0,[z0,z1,z2,z3,z501,z5,z6]),(0,[z0,z1,z45,z2,z3,z96,z6])],[(0,[z502,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z14,z2,z3,z5,z6]),(0,[z216,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z360]),(0,[z0,z1,z2,z3,z5,z6,z503]),(0,[z90,z0,z1,z25,z3,z5,z6]),(0,[z79,z0,z1,z2,z44,z5,z6]),(0,[z0,z1,z2,z3,z5,z504,z6])],[(0,[z0,z1,z2,z3,z5,z6,z239]),(0,[z0,z1,z505,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z67,z6]),(0,[z32,z0,z1,z2,z3,z5,z68])],[(1,[z216,z1,z52,z3,z5,z6]),(0,[z0,z1,z2,z200,z3,z5,z6]),(0,[z36,z74,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z506,z5,z6]),(0,[z0,z1,z2,z507,z3,z5,z6]),(1,[z0,z1,z30,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z508,z6]),(0,[z0,z1,z56,z2,z3,z5,z67]),(0,[z0,z1,z509,z2,z3,z5,z6]),(0,[z510,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z58,z3,z5,z6])],[(0,[z90,z1,z14,z2,z3,z5,z6]),(0,[z50,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z511,z3,z5,z6]),(0,[z512,z28,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z513,z5,z6]),(0,[z0,z1,z2,z3,z297,z5,z6])]],
   [[(0,[z514,z0,z1,z2,z3,z5,z6])],[(0,[z80,z22,z1,z2,z3,z5,z6]),(0,[z22,z1,z45,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z515,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z168]),(0,[z0,z1,z2,z516,z3,z5,z6]),(1,[z0,z1,z2,z3,z517,z6]),(0,[z0,z1,z2,z3,z5,z518,z6]),(0,[z0,z1,z2,z3,z519,z5,z6]),(0,[z0,z1,z520,z2,z3,z5,z6]),(0,[z0,z1,z2,z23,z5,z68,z6])],[(0,[z0,z1,z2,z521,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z29,z6])],[(0,[z1,z196,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z522,z6]),(0,[z0,z523,z1,z2,z3,z5,z6]),(0,[z0,z524,z1,z2,z3,z5,z6]),(0,[z412,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z525,z6])],[(0,[z0,z1,z2,z3,z526,z5,z6]),(0,[z0,z527,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z528])],[(0,[z1,z14,z2,z107,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z458]),(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z53,z0,z1,z2,z201,z5,z6]),(1,[z1,z2,z3,z5,z24,z20]),(0,[z0,z1,z2,z3,z5,z293,z6]),(0,[z0,z1,z2,z3,z530,z5,z6])],[(0,[z1,z14,z2,z3,z5,z453,z6]),(0,[z53,z0,z1,z2,z3,z5,z336]),(0,[z53,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z131,z67]),(0,[z0,z1,z2,z25,z3,z5,z6]),(0,[z292,z203,z1,z2,z3,z5,z6]),(0,[z102,z1,z2,z3,z5,z19,z6]),(1,[z470,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z14,z2,z531,z3,z5,z6]),(0,[z0,z1,z2,z3,z532,z5,z6]),(0,[z0,z1,z2,z3,z5,z533,z6]),(0,[z0,z1,z2,z3,z5,z534,z6]),(0,[z535,z0,z1,z2,z3,z5,z6]),(0,[z536,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z537,z6]),(0,[z538,z0,z1,z2,z3,z5,z6])],[],[(0,[z0,z1,z2,z3,z539,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z390]),(0,[z80,z0,z1,z2,z3,z396,z6]),(0,[z540,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z5,z6])],[(0,[z36,z1,z2,z3,z5,z135,z6]),(1,[z0,z59,z2,z107,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z541]),(0,[z542,z0,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z152,z6]),(0,[z213,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z543,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z544]),(0,[z0,z1,z2,z107,z5,z152,z6]),(0,[z74,z1,z452,z2,z3,z5,z6]),(0,[z0,z1,z44,z3,z26,z5,z6])],[(0,[z383,z22,z1,z2,z3,z5,z6]),(0,[z36,z1,z14,z2,z3,z5,z6]),(0,[z86,z1,z2,z3,z5,z6,z24]),(0,[z41,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z545,z3,z5,z6]),(0,[z0,z1,z2,z546,z3,z5,z6]),(0,[z0,z1,z238,z2,z3,z5,z6])],[(0,[z74,z1,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z107,z3,z5,z6]),(0,[z0,z1,z2,z3,z547,z5,z6]),(0,[z0,z1,z2,z548,z3,z5,z6]),(1,[z102,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z549]),(0,[z0,z1,z550,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z307,z6]),(0,[z216,z1,z2,z3,z93,z5,z6]),(0,[z36,z1,z2,z200,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z551,z6]),(0,[z0,z1,z37,z2,z3,z5,z6]),(0,[z133,z0,z1,z2,z481,z5,z6]),(0,[z0,z1,z2,z3,z64,z5,z6]),(0,[z512,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z290,z3,z5,z6])]],
   [[(0,[z249,z1,z14,z2,z3,z5,z6]),(0,[z552,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z553,z2,z3,z5,z6]),(0,[z53,z257,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z554,z6])],[(0,[z1,z14,z2,z3,z5,z46,z6]),(0,[z555,z0,z1,z2,z3,z5,z6]),(0,[z257,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z556,z5,z6]),(0,[z0,z1,z2,z3,z5,z77,z10]),(0,[z0,z1,z275,z2,z3,z5,z6])],[(0,[z213,z0,z1,z2,z3,z85,z6]),(0,[z0,z1,z2,z3,z5,z68,z10]),(0,[z0,z1,z2,z557,z3,z5,z6]),(0,[z86,z0,z1,z2,z3,z6,z31])],[(0,[z127,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z161,z3,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z19,z77]),(0,[z0,z1,z2,z5,z152,z6,z11])],[(0,[z1,z14,z2,z367,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z152,z6]),(1,[z0,z1,z2,z3,z5,z336]),(0,[z432,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z558,z3,z5,z6]),(0,[z143,z0,z1,z2,z559,z5,z6]),(0,[z560,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z561,z2,z3,z5,z6]),(1,[z377,z1,z2,z3,z5,z6])],[(0,[z1,z2,z25,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z29,z6,z31]),(0,[z0,z1,z562,z2,z3,z5,z6])],[(0,[z563,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z328,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z564,z6]),(0,[z0,z1,z2,z3,z5,z6,z565]),(0,[z0,z1,z2,z3,z566,z5,z6]),(0,[z382,z0,z1,z2,z3,z5,z6])],[(0,[z213,z53,z1,z2,z3,z5,z6]),(0,[z0,z1,z567,z2,z3,z5,z6]),(1,[z0,z1,z2,z559,z5,z6])]],
   [[(0,[z0,z1,z568,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z131,z6]),(0,[z36,z1,z2,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z569]),(0,[z0,z570,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z571,z3,z5,z6])],[(0,[z22,z1,z2,z3,z5,z46,z6]),(0,[z22,z103,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z24,z20]),(0,[z132,z36,z1,z2,z3,z5,z6]),(0,[z572,z0,z1,z2,z3,z5,z6])],[(1,[z383,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z19,z6]),(0,[z0,z1,z2,z573,z3,z5,z6]),(0,[z574,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z575,z2,z3,z5,z6]),(1,[z0,z1,z2,z481,z5,z6]),(0,[z576,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z367,z5,z152,z6])],[(0,[z36,z1,z2,z3,z76,z5,z6]),(0,[z0,z577,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z578,z5,z6]),(0,[z86,z0,z1,z2,z58,z5,z6])],[(0,[z22,z1,z2,z367,z3,z5,z6]),(0,[z0,z1,z2,z3,z579,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z580]),(0,[z0,z1,z43,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z581,z6])],[(0,[z0,z1,z2,z3,z5,z474,z6]),(0,[z36,z1,z2,z3,z543,z5,z6]),(0,[z0,z1,z45,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z582,z6])],[(0,[z583,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z107,z5,z6]),(0,[z86,z0,z1,z2,z3,z5,z77])],[(1,[z22,z103,z2,z3,z5,z6]),(0,[z0,z1,z584,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z379,z6])]],
   [[(0,[z80,z1,z14,z2,z3,z5,z6]),(0,[z435,z22,z1,z2,z3,z5,z6]),(0,[z213,z22,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z64,z5,z6]),(0,[z0,z1,z2,z3,z5,z131,z68]),(0,[z0,z1,z37,z3,z26,z5,z6]),(0,[z0,z1,z2,z585,z3,z5,z6])],[(0,[z22,z203,z1,z2,z3,z5,z6]),(0,[z41,z22,z1,z2,z3,z5,z6]),(0,[z1,z2,z200,z3,z93,z5,z6]),(0,[z1,z2,z3,z5,z68,z6,z24]),(0,[z81,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z586]),(0,[z382,z1,z2,z3,z5,z67,z6])],[(0,[z0,z1,z2,z587,z3,z5,z6])],[(0,[z383,z0,z103,z2,z3,z5,z6]),(0,[z90,z22,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z588,z6]),(1,[z1,z204,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z5,z379]),(0,[z0,z1,z207,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z239]),(0,[z0,z1,z2,z3,z589,z5,z6]),(1,[z86,z0,z1,z2,z3,z31])],[(0,[z0,z1,z2,z3,z5,z590,z6]),(0,[z0,z1,z2,z3,z5,z6,z591]),(0,[z0,z2,z3,z5,z135,z6,z10])],[(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z593,z0,z1,z2,z3,z5,z6])],[(0,[z216,z36,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z135,z6,z24]),(0,[z0,z1,z2,z3,z5,z594,z6]),(0,[z0,z59,z1,z2,z107,z5,z6]),(0,[z0,z377,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z595,z1,z2,z3,z5,z6]),(0,[z596,z0,z1,z2,z3,z5,z6]),(0,[z133,z0,z1,z2,z3,z5,z544]),(1,[z0,z1,z2,z3,z5,z168]),(0,[z0,z1,z56,z3,z5,z67,z6]),(0,[z470,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z597,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z3,z5,z598,z6]),(0,[z599,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z600,z5,z6]),(0,[z0,z1,z45,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z601,z5,z6]),(1,[z305,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z602,z3,z5,z6]),(0,[z0,z1,z603,z2,z3,z5,z6]),(0,[z50,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z62,z5,z6]),(0,[z0,z1,z2,z107,z3,z5,z6]),(0,[z0,z1,z2,z559,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z604]),(0,[z0,z1,z2,z3,z289,z5,z6])],[(0,[z0,z1,z605,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z46,z135,z6]),(0,[z0,z1,z2,z3,z396,z5,z6]),(0,[z80,z0,z1,z2,z3,z5,z10]),(0,[z79,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z6,z296]),(0,[z0,z1,z2,z606,z3,z5,z6])],[(0,[z383,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z531,z3,z5,z6]),(1,[z1,z2,z3,z5,z24,z11]),(1,[z607,z1,z2,z3,z5,z6]),(1,[z359,z1,z2,z3,z5,z6])],[(0,[z132,z22,z1,z2,z3,z5,z6]),(0,[z16,z1,z2,z3,z5,z6,z24]),(0,[z608,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z64,z5,z152,z6]),(0,[z0,z74,z2,z3,z5,z19,z6])],[(0,[z1,z14,z37,z2,z3,z5,z6]),(1,[z50,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z609,z6]),(0,[z610,z0,z1,z2,z3,z5,z6])],[(0,[z611,z0,z1,z2,z3,z5,z6]),(0,[z127,z0,z1,z2,z23,z5,z6]),(1,[z32,z0,z1,z2,z5,z11]),(0,[z0,z1,z2,z3,z5,z6,z612])]],
   [[(0,[z257,z1,z14,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z6,z20]),(0,[z613,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z614,z5,z6]),(0,[z0,z1,z2,z3,z5,z152,z6])],[(0,[z59,z1,z14,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z24,z24]),(0,[z133,z0,z1,z2,z3,z418,z6]),(0,[z0,z1,z615,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z135,z6,z31]),(0,[z0,z1,z2,z3,z5,z616,z6]),(0,[z0,z1,z617,z2,z3,z5,z6])],[(0,[z216,z53,z1,z2,z3,z5,z6]),(0,[z0,z618,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z619,z3,z5,z6]),(0,[z257,z1,z2,z200,z3,z5,z6]),(0,[z620,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z202,z3,z5,z6]),(0,[z621,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z622,z6]),(1,[z0,z1,z2,z3,z5,z544]),(0,[z623,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z624,z5,z6]),(1,[z81,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z625,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z626])],[(0,[z228,z0,z1,z2,z3,z5,z6]),(0,[z22,z1,z2,z627,z3,z5,z6]),(0,[z0,z203,z1,z37,z3,z5,z6]),(1,[z80,z0,z2,z3,z5,z10]),(0,[z628,z0,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z629]),(0,[z0,z326,z1,z2,z3,z5,z6])],[(0,[z0,z103,z1,z2,z3,z5,z6]),(0,[z80,z0,z1,z30,z3,z5,z6]),(0,[z0,z1,z2,z630,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z46,z6])],[(0,[z1,z14,z2,z3,z5,z85,z6]),(0,[z1,z2,z3,z5,z6,z24,z98]),(0,[z1,z2,z3,z5,z6,z310,z24]),(0,[z0,z1,z2,z3,z5,z19,z6])],[]],
   [[(0,[z0,z1,z2,z631,z3,z5,z6]),(0,[z80,z0,z1,z2,z3,z517,z6]),(0,[z0,z1,z2,z367,z3,z5,z6])],[(0,[z1,z14,z2,z3,z632,z5,z6]),(0,[z633,z36,z1,z2,z3,z5,z6]),(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z330,z5,z6]),(0,[z0,z635,z1,z2,z3,z5,z6])],[(0,[z636,z0,z1,z2,z3,z5,z6]),(0,[z0,z637,z1,z2,z3,z5,z6]),(0,[z638,z0,z1,z2,z3,z5,z6]),(1,[z41,z0,z2,z64,z5,z6]),(0,[z0,z1,z2,z44,z64,z5,z6]),(0,[z0,z1,z2,z3,z5,z10,z20]),(0,[z0,z1,z2,z3,z639,z5,z6]),(1,[z69,z1,z2,z3,z5,z6]),(1,[z70,z1,z2,z3,z5,z6]),(0,[z86,z0,z1,z2,z185,z5,z6])],[(0,[z216,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z640,z3,z5,z6]),(0,[z249,z1,z2,z3,z5,z6,z24]),(0,[z552,z36,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z107,z3,z5,z6]),(0,[z0,z1,z641,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z67,z6,z296])],[(0,[z1,z14,z2,z3,z4,z5,z6]),(0,[z1,z14,z45,z2,z3,z5,z6]),(0,[z32,z36,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z418,z6]),(0,[z0,z1,z2,z642,z3,z5,z6]),(1,[z1,z252,z2,z3,z5,z6]),(0,[z0,z305,z1,z2,z3,z5,z6]),(0,[z0,z643,z1,z2,z3,z5,z6])],[(0,[z0,z203,z1,z2,z3,z5,z6]),(0,[z644,z0,z1,z2,z3,z5,z6]),(1,[z302,z1,z2,z3,z5,z6])],[(0,[z22,z1,z2,z3,z5,z645,z6]),(0,[z22,z1,z2,z3,z5,z85,z6]),(0,[z646,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z474]),(0,[z0,z1,z2,z647,z3,z5,z6]),(1,[z257,z1,z2,z200,z5,z6])],[(0,[z213,z1,z14,z2,z3,z5,z6]),(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z99,z1,z2,z3,z93,z5,z6]),(0,[z0,z1,z2,z3,z5,z24,z11]),(0,[z649,z0,z1,z2,z3,z5,z6]),(1,[z512,z1,z2,z3,z5,z6]),(0,[z552,z1,z2,z3,z5,z6,z10]),(0,[z0,z1,z2,z3,z650,z5,z6]),(0,[z0,z607,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z367,z3,z152,z6])]],
   [[(0,[z41,z1,z14,z2,z3,z5,z6]),(0,[z22,z1,z651,z2,z3,z5,z6]),(0,[z652,z0,z1,z2,z3,z5,z6])],[(0,[z653,z0,z1,z2,z3,z5,z6]),(0,[z36,z257,z1,z2,z3,z5,z6]),(0,[z213,z1,z2,z200,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z152,z6]),(1,[z269,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z3,z5,z6,z20]),(0,[z1,z2,z3,z5,z68,z6,z342])],[(0,[z443,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z654]),(0,[z143,z0,z1,z282,z3,z5,z6]),(0,[z1,z2,z3,z5,z19,z6,z358])],[(0,[z0,z1,z2,z655,z3,z5,z6]),(0,[z0,z59,z1,z2,z64,z5,z6])],[(0,[z0,z1,z2,z3,z656,z5,z6]),(0,[z657,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z658,z5,z6]),(0,[z0,z1,z43,z2,z26,z5,z6])],[(0,[z103,z1,z14,z2,z3,z5,z6]),(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z77,z6,z24]),(0,[z0,z660,z1,z2,z3,z5,z6]),(1,[z0,z1,z282,z3,z5,z6]),(0,[z0,z1,z3,z5,z67,z6,z20]),(0,[z0,z1,z2,z3,z661,z5,z6])],[(0,[z1,z14,z2,z3,z5,z6,z24]),(0,[z36,z103,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z662,z6]),(0,[z36,z1,z2,z3,z5,z46,z6]),(0,[z1,z2,z3,z5,z67,z6,z629])],[(0,[z0,z1,z2,z3,z5,z6,z663]),(0,[z1,z2,z367,z3,z5,z6,z24]),(0,[z0,z1,z664,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z629]),(1,[z442,z1,z2,z3,z5,z6])]],
   [[(0,[z28,z1,z14,z2,z3,z5,z6]),(0,[z613,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z665,z6])],[(1,[z53,z1,z2,z201,z5,z6]),(0,[z36,z1,z2,z367,z3,z5,z6]),(0,[z133,z0,z1,z2,z3,z5,z598]),(0,[z0,z1,z2,z3,z5,z666,z6])],[(0,[z1,z14,z56,z2,z3,z5,z6]),(0,[z0,z1,z667,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z96,z135,z6])],[(0,[z1,z14,z2,z3,z5,z6,z98]),(0,[z357,z1,z2,z3,z5,z6,z24]),(0,[z132,z0,z1,z3,z5,z6,z20])],[(0,[z132,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z668,z2,z3,z5,z6]),(0,[z133,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z6,z669]),(0,[z0,z1,z2,z3,z5,z670,z6]),(0,[z132,z607,z1,z2,z3,z5,z6])],[(1,[z552,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z671,z3,z5,z6]),(0,[z0,z672,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z673,z3,z5,z6]),(0,[z0,z674,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z675])],[(0,[z22,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z53,z1,z2,z3,z93,z5,z6]),(0,[z36,z203,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z107,z5,z6,z11]),(0,[z0,z1,z2,z676,z3,z5,z6]),(0,[z57,z74,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z677])],[(0,[z552,z22,z1,z2,z3,z5,z6]),(1,[z27,z1,z2,z3,z5,z6]),(0,[z0,z1,z252,z2,z3,z5,z6]),(0,[z0,z1,z43,z2,z23,z5,z6]),(1,[z1,z2,z3,z5,z6,z33])]],
   [[(0,[z203,z1,z14,z2,z3,z5,z6]),(0,[z555,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z627,z3,z5,z6]),(0,[z0,z1,z2,z678,z3,z5,z6]),(0,[z679,z0,z1,z2,z3,z5,z6]),(0,[z680,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z681]),(1,[z0,z1,z2,z3,z278,z6]),(0,[z0,z1,z682,z2,z3,z5,z6])],[(0,[z633,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z683,z5,z6])],[(0,[z1,z267,z14,z2,z3,z5,z6]),(0,[z22,z1,z56,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z93,z5,z6]),(0,[z36,z1,z2,z3,z506,z5,z6]),(0,[z0,z1,z2,z3,z684,z5,z6])],[(0,[z1,z14,z2,z3,z5,z131,z6]),(0,[z0,z685,z1,z2,z3,z5,z6])],[(0,[z97,z0,z1,z2,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z6,z24]),(1,[z0,z1,z2,z3,z5,z598]),(0,[z686,z0,z1,z2,z3,z5,z6]),(0,[z359,z1,z2,z3,z5,z152,z6]),(0,[z32,z0,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z19,z6]),(0,[z1,z14,z2,z44,z3,z5,z6]),(0,[z563,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z687,z6]),(0,[z0,z203,z1,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z688,z6]),(0,[z0,z1,z37,z3,z5,z46,z6]),(0,[z0,z1,z2,z3,z5,z67,z10])],[(0,[z22,z1,z2,z3,z5,z6,z11]),(0,[z1,z2,z3,z5,z6,z24,z20]),(0,[z79,z36,z1,z2,z3,z5,z6]),(0,[z0,z203,z37,z2,z3,z5,z6]),(1,[z0,z1,z299,z3,z5,z6]),(0,[z143,z686,z1,z2,z3,z5,z6]),(0,[z79,z0,z1,z43,z3,z5,z6]),(0,[z689,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z56,z2,z3,z5,z20])],[(0,[z383,z1,z2,z3,z5,z6,z24]),(0,[z1,z15,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z690,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z24]),(0,[z1,z2,z3,z5,z6,z10,z98]),(0,[z0,z1,z2,z3,z5,z6,z691])]],
   [[(0,[z213,z0,z1,z2,z3,z93,z6]),(0,[z692,z0,z1,z2,z3,z5,z6])],[(0,[z693,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z85,z6,z24]),(1,[z1,z2,z3,z5,z68,z24]),(1,[z686,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z135,z6]),(0,[z694,z0,z1,z2,z3,z5,z6])],[(0,[z216,z1,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z645,z6]),(0,[z0,z1,z2,z3,z5,z85,z6]),(0,[z695,z0,z1,z2,z3,z5,z6]),(0,[z127,z0,z1,z2,z107,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z165]),(1,[z0,z74,z2,z3,z5,z19]),(0,[z696,z0,z1,z2,z3,z5,z6]),(0,[z697,z0,z1,z2,z3,z5,z6])],[(0,[z1,z15,z2,z3,z93,z5,z6]),(0,[z0,z1,z2,z3,z5,z698,z6]),(0,[z1,z2,z3,z110,z26,z5,z6]),(0,[z699,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z700,z5,z6])],[(1,[z1,z2,z3,z5,z6,z98]),(0,[z0,z1,z651,z2,z3,z5,z6]),(0,[z216,z1,z2,z200,z3,z5,z6]),(0,[z0,z1,z2,z701,z3,z5,z6]),(0,[z657,z0,z1,z2,z3,z5,z6]),(0,[z59,z1,z2,z3,z5,z6,z24]),(0,[z1,z2,z3,z5,z6,z24,z241]),(1,[z1,z101,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z517,z6]),(0,[z0,z1,z2,z702,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z703]),(0,[z86,z0,z275,z2,z3,z5,z6])],[(0,[z1,z14,z2,z52,z3,z5,z6]),(0,[z0,z1,z2,z3,z632,z5,z6]),(0,[z583,z22,z1,z2,z3,z5,z6]),(0,[z22,z1,z2,z44,z3,z5,z6]),(0,[z22,z1,z2,z3,z96,z5,z6]),(0,[z704,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z705,z6]),(0,[z0,z706,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z5,z31])],[(0,[z22,z1,z2,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z288,z5,z6]),(1,[z90,z0,z1,z3,z96,z6])],[(0,[z216,z0,z1,z15,z3,z5,z6]),(0,[z50,z0,z1,z2,z3,z5,z131]),(0,[z0,z1,z2,z3,z5,z131,z20])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z76,z77,z24]),(0,[z80,z0,z2,z3,z396,z10])],[],[(0,[z155,z1,z2,z3,z5,z6])],[],[(0,[z22,z72,z2,z3,z5,z6]),(0,[z0,z1,z707,z3,z5,z6])],[(0,[z1,z708,z2,z3,z5,z6]),(0,[z709,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z474]),(0,[z257,z1,z2,z200,z5,z6]),(0,[z0,z1,z471,z3,z46,z6]),(0,[z1,z2,z3,z5,z6,z710])],[(0,[z1,z14,z2,z3,z5,z239])],[(0,[z0,z275,z2,z3,z5,z77])],[(0,[z32,z22,z1,z2,z5,z11]),(0,[z0,z1,z2,z185,z5,z6])],[(0,[z0,z1,z2,z3,z5,z711]),(0,[z86,z1,z2,z3,z24,z31]),(0,[z712,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z168]),(0,[z216,z1,z368,z3,z5,z6]),(0,[z0,z1,z2,z713,z5,z6])],[(0,[z0,z1,z2,z3,z714,z6]),(0,[z686,z1,z2,z330,z5,z6]),(0,[z0,z1,z2,z3,z715,z6])],[(0,[z1,z2,z3,z5,z6,z716]),(0,[z0,z1,z282,z3,z5,z6])],[(0,[z717,z0,z1,z3,z5,z6]),(0,[z0,z28,z2,z3,z188,z6]),(0,[z80,z81,z2,z3,z5,z10]),(0,[z1,z2,z3,z5,z6,z718])],[(0,[z167,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z246,z24])],[(0,[z0,z1,z719,z3,z5,z6]),(0,[z1,z720,z2,z3,z5,z6]),(0,[z721,z1,z2,z3,z5,z6])]],
   [[(0,[z14,z2,z3,z446,z5,z6]),(0,[z722,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z544,z723]),(0,[z0,z2,z3,z724,z5,z6]),(0,[z1,z725,z2,z3,z5,z6]),(0,[z1,z726,z2,z3,z5,z6])],[(0,[z0,z727,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z24,z400]),(0,[z728,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z729,z5,z6]),(0,[z1,z2,z3,z5,z6,z730]),(0,[z731,z1,z2,z3,z5,z6]),(0,[z0,z1,z218,z185,z5,z6])],[(0,[z1,z2,z3,z5,z6,z732])],[(0,[z79,z1,z14,z26,z5,z6]),(0,[z733,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z58,z5,z6]),(0,[z0,z1,z45,z3,z46,z6])],[(0,[z734,z1,z2,z3,z5,z68])],[(0,[z0,z1,z2,z3,z735,z6]),(0,[z1,z2,z3,z736,z5,z6]),(0,[z1,z2,z3,z5,z6,z33]),(0,[z0,z1,z2,z3,z5,z737]),(0,[z133,z36,z25,z3,z5,z6]),(0,[z0,z1,z3,z5,z19,z164]),(0,[z1,z738,z2,z3,z5,z6])],[(0,[z36,z1,z2,z3,z5,z307]),(0,[z0,z1,z2,z107,z293,z6]),(0,[z739,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z740]),(1,[z0,z2,z3,z741,z6])],[(0,[z36,z1,z2,z3,z5,z654]),(0,[z36,z1,z2,z3,z76,z77])],[(0,[z81,z1,z2,z290,z5,z6]),(0,[z0,z1,z3,z742,z46,z6])],[(0,[z22,z1,z2,z3,z5,z336])],[(0,[z181,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z3,z5,z598]),(0,[z0,z1,z299,z3,z5,z379])],[(0,[z1,z2,z3,z5,z6,z743]),(0,[z0,z1,z744,z3,z5,z6])],[(0,[z0,z1,z2,z3,z745,z6]),(0,[z22,z1,z2,z559,z5,z6]),(0,[z0,z1,z299,z3,z5,z6])],[(0,[z0,z1,z641,z3,z46,z6])],[(0,[z1,z2,z3,z5,z280,z24])]],
   [[(0,[z0,z1,z2,z746,z5,z6]),(0,[z1,z2,z3,z5,z68,z24]),(0,[z133,z167,z25,z3,z5,z6])],[(0,[z1,z2,z286,z3,z5,z24]),(0,[z1,z2,z3,z747,z5,z6]),(0,[z0,z1,z748,z3,z5,z6]),(0,[z749,z1,z2,z3,z5,z6])],[(0,[z0,z750,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z751])],[(0,[z432,z1,z52,z3,z5,z6]),(0,[z0,z752,z2,z3,z5,z6]),(0,[z0,z1,z753,z26,z5,z6]),(0,[z1,z2,z3,z754,z5,z6]),(0,[z0,z275,z2,z185,z5,z6])],[(0,[z213,z1,z2,z3,z91,z6])],[(0,[z1,z2,z3,z5,z68,z98]),(0,[z132,z1,z14,z3,z5,z20]),(0,[z36,z1,z2,z129,z5,z6]),(0,[z0,z1,z37,z62,z5,z6]),(0,[z0,z1,z755,z3,z5,z6]),(0,[z0,z1,z756,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z757]),(0,[z0,z1,z2,z758,z5,z6])],[(0,[z1,z2,z3,z5,z458,z11]),(0,[z1,z2,z3,z5,z24,z457]),(0,[z644,z0,z1,z26,z5,z6]),(0,[z0,z1,z333,z3,z46,z6])],[(0,[z0,z1,z2,z3,z759,z6])],[(0,[z1,z267,z2,z3,z5,z131]),(0,[z22,z1,z2,z58,z5,z6]),(0,[z0,z760,z25,z3,z5,z6]),(0,[z761,z1,z2,z3,z5,z6]),(0,[z762,z1,z2,z3,z5,z6])],[(0,[z763,z0,z1,z2,z5,z6]),(0,[z734,z1,z2,z3,z5,z6]),(0,[z764,z1,z2,z3,z5,z6]),(0,[z765,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z758,z367,z6]),(0,[z0,z1,z2,z766,z5,z6])],[(0,[z100,z0,z1,z26,z5,z6]),(0,[z116,z1,z299,z3,z5,z6]),(0,[z81,z1,z30,z3,z5,z6]),(0,[z767,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z165,z24]),(0,[z36,z1,z144,z3,z5,z6]),(0,[z768,z1,z2,z3,z5,z6])],[],[(0,[z0,z1,z2,z3,z769,z6]),(1,[z0,z2,z3,z517,z10])],[(0,[z0,z1,z2,z3,z5,z770]),(0,[z0,z1,z144,z330,z5,z6]),(0,[z0,z2,z3,z741,z135,z6]),(0,[z80,z0,z2,z3,z517,z10])],[(0,[z1,z2,z3,z5,z6,z771]),(0,[z0,z1,z2,z3,z5,z772])]],
   [[(0,[z0,z1,z2,z773,z5,z6]),(0,[z0,z1,z2,z631,z152,z6]),(0,[z0,z275,z207,z3,z5,z6])],[(0,[z122,z1,z2,z62,z5,z6])],[(0,[z0,z1,z2,z3,z5,z774]),(0,[z143,z0,z2,z3,z135,z165]),(0,[z87,z0,z1,z2,z3,z31]),(0,[z0,z1,z2,z3,z76,z9])],[(0,[z633,z403,z2,z3,z5,z6]),(0,[z775,z1,z2,z3,z5,z6]),(0,[z0,z1,z56,z3,z5,z246])],[(0,[z0,z1,z776,z3,z5,z6]),(0,[z97,z1,z245,z3,z5,z6]),(0,[z143,z0,z2,z3,z741,z6]),(0,[z1,z777,z2,z3,z5,z6])],[(0,[z0,z1,z3,z5,z6,z778])],[(0,[z1,z2,z3,z5,z6,z310]),(0,[z1,z779,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z780]),(0,[z0,z1,z2,z3,z781,z6]),(0,[z133,z0,z25,z62,z5,z6]),(0,[z169,z1,z2,z3,z517,z6]),(0,[z0,z1,z2,z3,z5,z782])],[(0,[z90,z22,z1,z3,z96,z6]),(0,[z783,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z358,z20]),(0,[z0,z784,z2,z3,z5,z6])],[(0,[z22,z1,z202,z3,z5,z6]),(0,[z53,z1,z2,z506,z5,z6]),(0,[z1,z2,z3,z5,z24,z499]),(0,[z79,z0,z1,z468,z5,z6])],[(0,[z22,z1,z2,z129,z5,z6]),(0,[z0,z1,z2,z3,z288,z6]),(0,[z0,z1,z144,z3,z5,z165]),(0,[z1,z785,z2,z3,z5,z6]),(0,[z0,z1,z163,z2,z5,z11]),(0,[z0,z326,z2,z185,z5,z6])],[(0,[z36,z1,z2,z3,z5,z6]),(0,[z143,z0,z2,z3,z135,z193]),(0,[z535,z0,z2,z3,z5,z10])],[(0,[z1,z14,z2,z3,z5,z786]),(0,[z0,z1,z2,z3,z5,z787]),(0,[z36,z1,z2,z3,z5,z131]),(0,[z382,z1,z2,z129,z5,z6]),(0,[z1,z2,z3,z76,z77,z33])],[(0,[z1,z328,z3,z5,z6,z271]),(0,[z0,z1,z2,z3,z788,z6]),(0,[z789,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z742,z6])],[(0,[z1,z790,z2,z3,z5,z6]),(0,[z0,z1,z2,z330,z5,z6])],[(0,[z1,z2,z3,z5,z6,z342]),(0,[z1,z238,z3,z5,z68,z24])],[]],
   [[(0,[z86,z22,z1,z2,z3,z31]),(0,[z0,z791,z2,z3,z5,z6])],[(0,[z0,z1,z144,z3,z5,z193]),(0,[z0,z1,z30,z3,z5,z19]),(0,[z90,z0,z1,z3,z376,z6])],[(0,[z0,z1,z2,z465,z152,z6])],[(0,[z36,z1,z238,z3,z5,z6]),(0,[z792,z1,z2,z3,z5,z6])],[(0,[z36,z1,z218,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z164])],[(0,[z1,z2,z3,z5,z6,z793]),(0,[z634,z0,z1,z2,z5,z11]),(0,[z794,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z795]),(0,[z0,z796,z2,z3,z5,z6]),(0,[z0,z797,z2,z3,z5,z6])],[(0,[z0,z1,z25,z62,z5,z6]),(0,[z0,z1,z2,z481,z5,z544])],[(0,[z0,z1,z2,z798,z5,z6]),(0,[z1,z2,z3,z5,z6,z799]),(0,[z0,z74,z2,z3,z5,z800])],[(0,[z0,z1,z2,z801,z5,z6]),(0,[z0,z1,z2,z3,z5,z165])],[(0,[z1,z2,z3,z5,z6,z802]),(0,[z22,z175,z2,z3,z5,z6]),(0,[z79,z1,z26,z5,z6,z24])],[(0,[z803,z1,z2,z3,z5,z6]),(0,[z804,z1,z2,z3,z5,z6]),(0,[z805,z1,z2,z3,z5,z6])],[(0,[z169,z1,z2,z3,z396,z6]),(0,[z0,z806,z2,z3,z5,z6])],[(1,[z1,z2,z5,z24,z296]),(0,[z807,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z808])],[(0,[z213,z1,z2,z3,z5,z393]),(0,[z1,z2,z3,z5,z6,z809]),(0,[z621,z0,z1,z2,z3,z31])],[(0,[z810,z1,z2,z3,z5,z6])]],
   [[(0,[z86,z1,z2,z3,z5,z458]),(0,[z0,z1,z2,z811,z5,z6]),(0,[z382,z1,z2,z3,z5,z6]),(0,[z375,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z193]),(0,[z1,z812,z2,z3,z5,z6])],[(0,[z1,z2,z5,z152,z24,z11]),(0,[z382,z1,z2,z3,z5,z131]),(0,[z813,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z168,z814]),(0,[z621,z0,z2,z3,z135,z6])],[(0,[z815,z1,z2,z3,z5,z6]),(0,[z0,z74,z2,z3,z517,z6])],[(0,[z255,z1,z2,z3,z263,z6]),(0,[z816,z1,z2,z3,z5,z6])],[(0,[z14,z2,z3,z601,z5,z6]),(0,[z213,z1,z2,z3,z85,z6]),(0,[z817,z1,z2,z3,z5,z6]),(0,[z59,z101,z2,z107,z5,z6]),(0,[z818,z1,z2,z3,z5,z6])],[(0,[z122,z1,z2,z3,z5,z6]),(0,[z36,z275,z2,z3,z5,z6]),(0,[z472,z0,z1,z3,z5,z20]),(0,[z269,z1,z2,z3,z5,z819])],[(0,[z22,z1,z2,z3,z278,z6]),(0,[z1,z2,z3,z5,z24,z569]),(0,[z1,z3,z5,z6,z24,z164])],[(0,[z22,z1,z238,z3,z5,z6]),(0,[z552,z214,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z396,z6]),(0,[z820,z1,z2,z3,z5,z6]),(0,[z0,z1,z56,z129,z5,z67])],[(0,[z1,z14,z2,z3,z5,z544]),(0,[z1,z2,z3,z5,z393,z24]),(0,[z0,z1,z2,z62,z288,z6]),(0,[z821,z1,z2,z3,z5,z6]),(1,[z0,z2,z3,z135,z165]),(0,[z0,z1,z2,z822,z5,z6]),(0,[z0,z1,z207,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z823]),(0,[z0,z824,z2,z3,z5,z6]),(0,[z36,z1,z2,z62,z5,z6]),(0,[z36,z1,z2,z289,z5,z6]),(0,[z36,z1,z2,z290,z5,z6]),(0,[z0,z325,z2,z107,z5,z6]),(0,[z1,z825,z2,z3,z5,z6]),(0,[z326,z826,z2,z3,z5,z6]),(0,[z827,z1,z2,z3,z5,z6])],[(0,[z1,z403,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z293,z6]),(0,[z133,z0,z25,z3,z5,z6]),(0,[z0,z2,z760,z3,z5,z6]),(0,[z0,z1,z2,z3,z828,z6]),(0,[z0,z1,z2,z3,z829,z6]),(0,[z830,z1,z2,z3,z5,z6]),(0,[z831,z1,z2,z3,z5,z6])],[(0,[z1,z2,z200,z832,z5,z6]),(0,[z0,z1,z833,z3,z5,z6]),(0,[z834,z1,z2,z3,z5,z6])],[(0,[z1,z238,z3,z5,z6,z342])],[(0,[z53,z1,z2,z60,z5,z6])],[(0,[z22,z1,z2,z3,z5,z835]),(0,[z0,z1,z836,z3,z5,z6])],[(0,[z0,z1,z837,z3,z5,z6]),(0,[z1,z2,z3,z838,z5,z6])]],
   [[(0,[z0,z1,z2,z839,z5,z6]),(0,[z840,z1,z2,z3,z5,z6])],[(0,[z596,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z289,z517,z6]),(0,[z102,z74,z2,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z841])],[(0,[z397,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z842]),(0,[z0,z1,z275,z2,z3,z31])],[(0,[z1,z14,z2,z3,z5,z474])],[(0,[z0,z1,z2,z3,z843,z6]),(0,[z1,z15,z2,z3,z5,z393])],[(0,[z41,z0,z202,z64,z5,z6]),(0,[z844,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z185,z5,z6]),(0,[z0,z1,z2,z845,z5,z6])],[(0,[z0,z1,z2,z846,z5,z6]),(0,[z0,z1,z2,z481,z5,z598]),(0,[z0,z1,z847,z3,z5,z6])],[(0,[z1,z2,z3,z5,z379,z848]),(0,[z849,z1,z2,z3,z5,z6])],[(0,[z22,z275,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z850]),(0,[z686,z1,z2,z559,z5,z6])],[(0,[z1,z267,z2,z3,z5,z6]),(0,[z1,z14,z282,z3,z5,z6]),(0,[z143,z0,z2,z330,z135,z6]),(0,[z851,z1,z2,z3,z5,z6])],[(0,[z1,z452,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z852,z6]),(0,[z853,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z854]),(0,[z0,z1,z2,z855,z5,z6]),(0,[z856,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z857]),(0,[z1,z2,z3,z858,z5,z6]),(0,[z0,z1,z56,z3,z5,z67])],[(0,[z22,z1,z2,z62,z5,z6]),(0,[z22,z1,z2,z289,z5,z6]),(0,[z859,z1,z2,z3,z5,z6])],[(0,[z22,z1,z2,z3,z293,z6]),(0,[z1,z3,z5,z271,z24,z20]),(0,[z860,z1,z2,z3,z5,z6]),(0,[z0,z1,z617,z26,z5,z6]),(0,[z0,z275,z2,z3,z76,z6])],[(0,[z14,z2,z3,z656,z5,z6]),(0,[z22,z1,z2,z3,z76,z77]),(0,[z216,z1,z92,z3,z5,z6]),(0,[z1,z2,z3,z5,z170,z24]),(0,[z36,z1,z145,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z861]),(0,[z86,z0,z275,z2,z3,z31])],[(0,[z1,z2,z3,z5,z6,z862]),(0,[z1,z2,z3,z863,z5,z6]),(0,[z0,z1,z2,z3,z5,z864])],[(0,[z1,z14,z45,z3,z46,z6]),(0,[z22,z575,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z865]),(0,[z0,z1,z56,z3,z5,z534]),(0,[z377,z1,z2,z58,z5,z6])],[(0,[z22,z413,z2,z3,z5,z6]),(0,[z1,z866,z2,z3,z5,z6])],[(0,[z36,z1,z2,z367,z152,z6]),(0,[z1,z867,z2,z3,z5,z6])],[(0,[z868,z1,z14,z2,z5,z6]),(0,[z869,z1,z2,z3,z5,z6]),(0,[z1,z870,z2,z3,z5,z6]),(0,[z0,z1,z871,z3,z5,z6]),(0,[z57,z74,z2,z3,z5,z19])],[(0,[z1,z215,z2,z3,z93,z6]),(0,[z1,z2,z3,z5,z6,z358]),(0,[z1,z872,z2,z3,z5,z6]),(0,[z873,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z289,z396,z6]),(0,[z0,z1,z2,z290,z396,z6])],[(0,[z1,z2,z3,z5,z24,z486]),(0,[z0,z1,z299,z3,z5,z168]),(0,[z0,z1,z2,z585,z152,z6]),(0,[z0,z1,z2,z23,z5,z466]),(0,[z0,z1,z2,z874,z5,z6]),(0,[z0,z1,z2,z3,z5,z875])],[(0,[z876,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z877]),(0,[z1,z2,z3,z5,z737,z24]),(0,[z878,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z598]),(0,[z1,z2,z5,z67,z24,z296]),(0,[z879,z1,z2,z3,z5,z6]),(0,[z0,z1,z880,z3,z5,z6]),(0,[z0,z1,z2,z881,z5,z6])],[(0,[z41,z36,z2,z64,z5,z6]),(0,[z27,z1,z202,z3,z5,z6]),(0,[z0,z1,z882,z3,z5,z6]),(0,[z8,z0,z2,z3,z135,z6]),(0,[z0,z1,z2,z3,z5,z800]),(0,[z0,z1,z444,z3,z5,z67]),(0,[z0,z1,z2,z3,z6,z883])],[(0,[z1,z14,z299,z3,z5,z6]),(0,[z1,z2,z3,z5,z68,z310]),(0,[z403,z2,z3,z5,z6,z10]),(0,[z36,z1,z2,z3,z5,z379]),(0,[z0,z1,z202,z3,z278,z6])],[(0,[z0,z1,z2,z5,z24,z296]),(0,[z0,z1,z2,z3,z5,z884])],[(0,[z99,z1,z2,z3,z93,z6]),(0,[z1,z45,z3,z46,z6,z24]),(0,[z0,z275,z2,z3,z5,z31])],[(0,[z53,z1,z2,z201,z5,z393]),(0,[z1,z2,z3,z5,z6,z885]),(0,[z0,z1,z238,z23,z5,z68])],[(0,[z1,z886,z2,z3,z5,z6]),(0,[z0,z1,z238,z5,z6,z11])]],
   [[(0,[z887,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z458,z10]),(0,[z888,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z5,z19,z296])],[(0,[z14,z2,z690,z3,z5,z6]),(0,[z275,z14,z2,z3,z5,z6]),(0,[z22,z1,z144,z3,z5,z6]),(0,[z216,z1,z52,z3,z5,z6]),(0,[z0,z1,z2,z3,z889,z6])],[(0,[z22,z1,z145,z3,z5,z6]),(0,[z41,z0,z2,z64,z278,z6]),(0,[z890,z1,z2,z3,z5,z6]),(0,[z1,z891,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z883])],[(0,[z222,z1,z2,z3,z5,z6]),(0,[z1,z2,z200,z34,z5,z6])],[(0,[z0,z1,z2,z3,z517,z6]),(0,[z242,z0,z1,z3,z96,z6]),(0,[z1,z2,z3,z5,z6,z892]),(0,[z86,z0,z1,z2,z3,z883])],[(0,[z0,z1,z893,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z894]),(0,[z1,z2,z5,z6,z629,z296])],[(0,[z1,z2,z3,z5,z6,z895]),(0,[z0,z1,z2,z896,z5,z6]),(1,[z1,z2,z3,z897,z6]),(0,[z1,z898,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z384,z24]),(0,[z1,z2,z3,z93,z219,z6]),(0,[z213,z1,z2,z3,z897,z6]),(0,[z899,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z900,z6])],[(0,[z0,z1,z2,z901,z5,z6]),(0,[z902,z1,z2,z3,z5,z6]),(0,[z903,z1,z2,z3,z5,z6]),(0,[z0,z326,z207,z3,z5,z6])],[(0,[z0,z1,z2,z3,z904,z6]),(0,[z0,z905,z2,z3,z5,z6]),(0,[z827,z326,z2,z3,z5,z6])],[(0,[z1,z2,z62,z5,z6,z24]),(0,[z1,z2,z3,z5,z497,z24]),(0,[z0,z570,z37,z3,z5,z6])],[(0,[z0,z1,z144,z559,z5,z6]),(0,[z0,z1,z145,z3,z396,z6]),(0,[z1,z2,z3,z5,z906,z6])],[],[(0,[z90,z1,z3,z5,z24,z20]),(0,[z907,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z908]),(0,[z22,z1,z2,z3,z5,z379]),(0,[z909,z0,z1,z2,z3,z5]),(0,[z1,z2,z129,z5,z6,z629])]],
   [[(0,[z1,z267,z2,z3,z5,z10]),(0,[z1,z2,z3,z93,z5,z393]),(0,[z1,z2,z3,z5,z6,z910])],[(0,[z22,z1,z2,z3,z5,z6]),(0,[z181,z1,z2,z201,z5,z6]),(0,[z0,z1,z2,z3,z5,z911]),(0,[z470,z1,z2,z3,z5,z24]),(0,[z912,z1,z2,z3,z5,z6])],[(0,[z443,z1,z229,z3,z5,z6]),(0,[z16,z14,z2,z3,z5,z6]),(0,[z1,z2,z3,z47,z5,z6]),(0,[z0,z1,z2,z753,z5,z6]),(0,[z0,z1,z238,z23,z5,z6])],[(0,[z28,z252,z2,z3,z29,z6]),(0,[z1,z2,z3,z5,z6,z913])],[(0,[z1,z14,z2,z3,z5,z780]),(0,[z1,z2,z3,z5,z474,z24]),(0,[z0,z1,z2,z107,z5,z168])],[(0,[z273,z0,z2,z3,z135,z6]),(0,[z0,z914,z2,z3,z5,z6])],[(0,[z53,z1,z2,z177,z5,z6]),(0,[z1,z2,z3,z5,z379,z24]),(0,[z915,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z26,z5,z916]),(0,[z0,z1,z2,z917,z5,z6])],[(0,[z22,z14,z2,z3,z5,z6]),(0,[z1,z14,z2,z3,z288,z6]),(0,[z0,z65,z2,z3,z5,z19])],[(0,[z377,z1,z2,z3,z5,z6]),(0,[z27,z1,z2,z3,z278,z6]),(0,[z0,z1,z2,z918,z5,z6]),(0,[z0,z1,z919,z3,z5,z6])],[(0,[z0,z1,z2,z920,z5,z6]),(0,[z53,z1,z2,z201,z5,z336]),(0,[z0,z1,z2,z448,z5,z68])],[(0,[z1,z2,z3,z5,z6,z921]),(0,[z922,z1,z2,z3,z5,z6]),(0,[z86,z0,z1,z207,z3,z31])],[(0,[z1,z14,z2,z330,z5,z6]),(0,[z22,z1,z218,z3,z5,z6]),(0,[z41,z0,z2,z64,z293,z6]),(0,[z302,z1,z2,z58,z5,z6])],[(0,[z14,z2,z105,z3,z5,z6]),(0,[z0,z1,z2,z62,z418,z6]),(0,[z433,z0,z1,z3,z5,z20])],[(0,[z167,z1,z2,z481,z5,z6]),(0,[z0,z1,z2,z3,z5,z923]),(0,[z0,z1,z2,z5,z10,z296]),(0,[z1,z924,z2,z3,z5,z6])],[(0,[z383,z14,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z371]),(0,[z1,z2,z3,z5,z594,z24])],[(0,[z925,z1,z2,z3,z5,z6]),(0,[z111,z1,z2,z5,z6,z390]),(0,[z388,z0,z1,z2,z5,z11])]],
   [[(0,[z0,z1,z2,z926,z5,z6]),(0,[z1,z196,z15,z3,z5,z6]),(0,[z0,z1,z927,z3,z5,z6]),(0,[z1,z2,z3,z418,z6,z24]),(0,[z1,z2,z3,z5,z598,z24]),(0,[z1,z2,z3,z928,z5,z6]),(0,[z0,z1,z2,z3,z5,z929]),(0,[z0,z1,z2,z5,z6,z930])],[(0,[z36,z1,z2,z3,z5,z378]),(0,[z0,z1,z2,z931,z5,z6]),(0,[z1,z2,z3,z5,z541,z24]),(0,[z122,z1,z2,z481,z5,z6]),(0,[z1,z932,z2,z3,z5,z6])],[(0,[z1,z14,z3,z5,z6,z164]),(0,[z0,z933,z2,z3,z5,z6]),(0,[z377,z1,z218,z3,z5,z6])],[(0,[z555,z1,z2,z177,z5,z6]),(0,[z86,z0,z1,z2,z58,z31])],[(0,[z1,z282,z3,z5,z6,z24]),(0,[z74,z2,z3,z5,z19,z24]),(0,[z1,z2,z3,z5,z6,z934]),(0,[z0,z1,z2,z290,z517,z6]),(0,[z935,z1,z2,z3,z5,z6]),(0,[z936,z1,z2,z3,z5,z6])],[(0,[z937,z1,z2,z3,z5,z6]),(0,[z938,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z165]),(0,[z133,z0,z25,z481,z5,z6]),(0,[z0,z2,z3,z5,z800,z10]),(0,[z0,z1,z2,z3,z939,z6]),(0,[z1,z2,z3,z5,z6,z940])],[(0,[z0,z1,z319,z44,z5,z6]),(0,[z941,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z68,z842])],[],[(0,[z442,z1,z2,z3,z76,z77])],[(0,[z1,z2,z3,z5,z622,z24]),(0,[z0,z1,z3,z5,z942,z20])],[(0,[z1,z2,z3,z5,z98,z20]),(0,[z326,z14,z2,z3,z5,z6]),(0,[z1,z15,z3,z5,z6,z271]),(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z1,z2,z944,z5,z6])],[(0,[z22,z1,z2,z3,z5,z945]),(0,[z946,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z742,z6])],[(0,[z0,z1,z2,z3,z5,z947]),(0,[z36,z1,z30,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z193]),(0,[z90,z1,z14,z3,z96,z6]),(0,[z552,z1,z2,z3,z5,z307]),(0,[z1,z2,z3,z5,z6,z948]),(0,[z36,z326,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z949]),(0,[z0,z1,z2,z950,z5,z6])],[(0,[z133,z22,z25,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z296])]],
   [[(0,[z22,z1,z2,z290,z5,z6]),(0,[z607,z1,z2,z3,z5,z6]),(0,[z694,z0,z1,z2,z5,z11]),(0,[z951,z1,z2,z3,z5,z6])],[(0,[z617,z14,z2,z3,z5,z6]),(0,[z637,z14,z2,z3,z5,z6]),(0,[z0,z706,z2,z107,z5,z6])],[(0,[z0,z1,z2,z3,z5,z952]),(0,[z36,z1,z2,z3,z5,z588]),(0,[z1,z2,z129,z5,z6,z24]),(0,[z953,z1,z2,z3,z5,z6])],[(0,[z377,z275,z2,z3,z5,z6])],[(0,[z888,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z5,z6,z954]),(0,[z0,z1,z955,z3,z5,z6])],[(0,[z1,z14,z2,z3,z396,z6]),(0,[z0,z1,z2,z3,z5,z956]),(0,[z0,z1,z30,z3,z517,z6])],[(0,[z1,z14,z207,z3,z5,z6]),(0,[z22,z523,z2,z3,z5,z6]),(0,[z957,z1,z2,z3,z5,z6]),(0,[z167,z1,z2,z3,z5,z544]),(0,[z958,z1,z2,z3,z5,z6])],[(0,[z1,z959,z2,z3,z5,z6]),(0,[z86,z1,z14,z2,z3,z31]),(0,[z0,z1,z2,z3,z897,z6]),(0,[z32,z1,z2,z5,z24,z11]),(0,[z80,z36,z2,z3,z5,z10]),(0,[z960,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z23,z5,z473])],[(0,[z0,z1,z961,z3,z5,z6]),(0,[z132,z1,z3,z5,z24,z20]),(0,[z1,z2,z3,z5,z6,z962]),(0,[z963,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z3,z658,z6]),(0,[z0,z1,z2,z3,z5,z964]),(0,[z0,z1,z2,z23,z5,z68])],[(0,[z1,z202,z3,z5,z6,z24])],[(0,[z1,z2,z3,z5,z6,z965]),(0,[z36,z59,z2,z107,z5,z6]),(0,[z0,z1,z2,z966,z5,z6]),(0,[z0,z1,z145,z3,z517,z6])],[(0,[z1,z967,z2,z3,z5,z6]),(0,[z1,z2,z3,z968,z5,z6]),(0,[z0,z1,z969,z3,z5,z6]),(0,[z432,z1,z3,z5,z24,z20]),(0,[z1,z2,z3,z5,z68,z358]),(0,[z970,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z971,z6])],[(0,[z41,z2,z64,z5,z6,z24]),(0,[z155,z1,z282,z3,z5,z6]),(0,[z972,z1,z2,z3,z5,z6])],[(0,[z524,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z973]),(0,[z1,z974,z2,z3,z5,z6]),(0,[z1,z975,z2,z3,z5,z6])],[(0,[z1,z2,z3,z976,z5,z6]),(0,[z216,z1,z149,z3,z5,z6]),(0,[z41,z0,z2,z64,z5,z6]),(0,[z1,z2,z3,z5,z6,z977])],[(0,[z0,z1,z2,z3,z5,z978]),(0,[z979,z1,z2,z3,z5,z6]),(0,[z1,z56,z3,z5,z67,z629]),(0,[z980,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z393]),(0,[z0,z1,z2,z3,z418,z6]),(0,[z386,z0,z2,z3,z135,z6]),(0,[z470,z1,z3,z5,z6,z164])],[(0,[z22,z1,z30,z3,z5,z6]),(0,[z22,z595,z2,z3,z5,z6]),(0,[z302,z1,z2,z3,z5,z6]),(0,[z0,z1,z282,z3,z29,z6]),(0,[z0,z1,z3,z5,z128,z20]),(0,[z0,z1,z56,z5,z67,z296])],[(0,[z32,z1,z14,z2,z5,z11]),(0,[z22,z1,z2,z3,z5,z981]),(0,[z22,z326,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z982,z6]),(0,[z1,z2,z3,z293,z6,z24]),(0,[z16,z2,z3,z5,z6,z98]),(0,[z0,z1,z299,z107,z5,z6]),(0,[z0,z498,z2,z107,z5,z6])],[(0,[z512,z1,z2,z3,z5,z6]),(0,[z1,z267,z2,z3,z5,z346]),(0,[z1,z2,z3,z5,z6,z983]),(0,[z1,z2,z330,z5,z6,z24]),(0,[z69,z1,z45,z3,z46,z6]),(0,[z1,z2,z3,z5,z6,z984])],[(0,[z213,z1,z2,z3,z374,z6]),(0,[z1,z2,z3,z5,z6,z723])],[(0,[z269,z1,z2,z3,z5,z6]),(0,[z0,z1,z985,z3,z5,z6]),(0,[z986,z1,z2,z3,z5,z6])],[(0,[z987,z1,z2,z3,z5,z165]),(0,[z512,z28,z2,z3,z29,z6]),(0,[z1,z2,z3,z988,z5,z6]),(0,[z0,z1,z989,z3,z5,z6]),(0,[z0,z1,z2,z23,z5,z842])],[(0,[z1,z990,z2,z3,z5,z6]),(0,[z80,z2,z3,z5,z24,z10]),(0,[z0,z1,z3,z5,z67,z942]),(0,[z1,z2,z3,z5,z6,z991])],[(0,[z0,z1,z2,z992,z5,z6]),(0,[z0,z1,z2,z481,z288,z6]),(0,[z143,z0,z2,z559,z135,z6])],[(0,[z0,z1,z2,z993,z5,z6]),(0,[z36,z1,z2,z481,z5,z6]),(0,[z0,z994,z2,z3,z5,z6]),(0,[z377,z326,z2,z3,z5,z6])],[(0,[z1,z14,z56,z3,z5,z67]),(0,[z1,z2,z3,z93,z897,z6]),(0,[z0,z1,z30,z3,z396,z6]),(0,[z0,z1,z2,z3,z5,z942])],[(0,[z22,z1,z2,z367,z152,z6]),(1,[z1,z2,z832,z5,z6]),(0,[z442,z1,z2,z3,z5,z6]),(0,[z302,z1,z218,z3,z5,z6])],[(0,[z1,z2,z3,z5,z687,z24]),(0,[z1,z2,z3,z5,z6,z995])],[(0,[z1,z2,z3,z5,z24,z220]),(0,[z0,z1,z2,z996,z5,z6])],[(0,[z1,z2,z58,z5,z6,z24]),(0,[z0,z1,z450,z3,z46,z6]),(0,[z686,z1,z144,z3,z5,z6]),(0,[z0,z51,z2,z3,z5,z19])],[(0,[z0,z1,z997,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z998,z6]),(0,[z1,z999,z2,z3,z5,z6]),(0,[z0,z1,z1000,z3,z5,z6]),(0,[z199,z1,z2,z3,z5,z239]),(0,[z1,z1001,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z598,z716]),(0,[z0,z1,z1002,z3,z5,z6]),(0,[z1003,z1,z2,z3,z5,z6]),(0,[z1004,z1,z2,z3,z5,z6]),(0,[z1005,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z310,z20]),(0,[z1,z2,z3,z5,z6,z1006])],[(0,[z27,z1,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z239])],[(0,[z111,z1,z2,z5,z24,z11])],[(0,[z88,z1,z2,z3,z453,z6]),(0,[z577,z14,z2,z3,z5,z6]),(0,[z1,z2,z3,z93,z6,z427]),(0,[z357,z1,z2,z3,z6,z241]),(0,[z0,z1,z2,z558,z152,z6]),(0,[z1,z2,z3,z5,z6,z1007])],[(0,[z1,z2,z3,z5,z581,z24]),(0,[z0,z1,z202,z3,z293,z6]),(0,[z1008,z1,z2,z3,z5,z6])],[(0,[z36,z1,z2,z3,z5,z168]),(0,[z167,z1,z2,z3,z5,z598]),(0,[z80,z0,z2,z289,z5,z10])],[(0,[z216,z1,z52,z3,z5,z239]),(0,[z1,z2,z3,z5,z24,z691]),(0,[z1009,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z741,z6])],[(0,[z0,z1,z2,z3,z1010,z6])],[(0,[z1011,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z336]),(0,[z0,z1,z2,z3,z5,z1012]),(0,[z0,z1,z1013,z3,z5,z6])],[(0,[z36,z1,z2,z3,z5,z458]),(0,[z36,z1,z2,z3,z5,z49]),(0,[z273,z0,z25,z3,z5,z6]),(0,[z302,z275,z2,z3,z5,z6])],[(0,[z686,z1,z2,z3,z5,z6]),(0,[z22,z1,z2,z481,z5,z6]),(0,[z1,z2,z3,z517,z6,z24]),(0,[z1,z2,z3,z396,z6,z24]),(0,[z0,z1,z282,z3,z135,z6]),(0,[z1014,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1015]),(0,[z0,z1,z2,z559,z5,z6]),(0,[z0,z1,z1016,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1017])],[(0,[z0,z1,z2,z3,z5,z1018]),(0,[z244,z1,z2,z3,z645,z6]),(0,[z1,z2,z3,z5,z6,z1019]),(0,[z169,z1,z2,z289,z5,z6]),(0,[z1,z1020,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z1021,z5,z6]),(0,[z0,z74,z2,z3,z5,z616])],[(0,[z59,z14,z2,z107,z5,z6]),(0,[z0,z1,z2,z3,z288,z544]),(0,[z1,z2,z3,z5,z6,z1022]),(0,[z0,z1,z2,z1023,z5,z6]),(0,[z0,z234,z2,z3,z29,z6]),(0,[z1,z2,z3,z5,z6,z1024])],[(0,[z14,z2,z333,z3,z5,z6]),(0,[z99,z1,z2,z3,z263,z6]),(0,[z0,z1025,z2,z3,z5,z6]),(0,[z1,z56,z3,z5,z67,z24]),(0,[z36,z1,z2,z3,z5,z544]),(0,[z0,z1,z2,z3,z5,z819])],[(0,[z1,z14,z2,z3,z517,z6]),(0,[z41,z116,z2,z64,z5,z6])],[(0,[z0,z1,z1026,z3,z5,z6])],[(0,[z216,z1,z707,z3,z5,z6]),(0,[z1,z2,z3,z5,z94,z24]),(0,[z1,z2,z3,z5,z6,z1027])],[(0,[z22,z103,z2,z3,z5,z6]),(0,[z1,z267,z2,z3,z5,z19]),(0,[z572,z0,z1,z2,z3,z31])],[(0,[z22,z1,z2,z3,z5,z239]),(0,[z79,z1,z2,z5,z24,z11]),(0,[z613,z1,z2,z506,z5,z6]),(0,[z1,z2,z3,z1028,z5,z6]),(0,[z1029,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1030,z3,z5,z6])],[(0,[z0,z1,z3,z1031,z5,z6]),(0,[z1,z2,z3,z5,z24,z296]),(0,[z535,z0,z25,z3,z5,z6]),(0,[z1032,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z58,z5,z6])],[(0,[z1,z2,z3,z5,z24,z71]),(0,[z36,z1,z2,z3,z5,z389]),(0,[z143,z2,z3,z135,z6,z24]),(0,[z269,z1,z2,z3,z5,z916]),(0,[z1,z2,z3,z1033,z5,z6])],[(0,[z22,z1,z2,z3,z5,z168]),(0,[z1,z1034,z2,z3,z5,z6])],[(0,[z21,z1,z2,z627,z5,z6]),(0,[z22,z708,z2,z3,z5,z6]),(0,[z1035,z0,z1,z3,z5,z6]),(0,[z0,z2,z107,z724,z5,z6])],[(0,[z1,z37,z3,z5,z24,z20]),(0,[z80,z0,z145,z3,z5,z10])],[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z0,z1,z2,z3,z5,z1037]),(0,[z0,z1,z2,z3,z517,z10]),(0,[z90,z0,z1,z3,z742,z6]),(0,[z1038,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z911]),(0,[z1,z2,z3,z5,z131,z737]),(0,[z0,z1,z2,z1039,z5,z6]),(0,[z1040,z1,z2,z3,z5,z6]),(0,[z1041,z1,z2,z3,z5,z6])]],
   [[(0,[z14,z2,z3,z5,z6,z310]),(0,[z127,z1,z2,z5,z24,z11]),(0,[z275,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z64,z293,z6]),(0,[z79,z0,z1,z281,z5,z6])],[(0,[z133,z14,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1042]),(0,[z1,z2,z3,z5,z168,z24]),(0,[z0,z1,z37,z3,z5,z544])],[(0,[z0,z1,z1043,z3,z5,z6]),(0,[z302,z326,z2,z3,z5,z6])],[(0,[z383,z708,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z24,z11]),(0,[z478,z0,z25,z3,z5,z6]),(0,[z27,z1,z2,z3,z293,z6]),(0,[z0,z1,z218,z58,z5,z6])],[(0,[z0,z1,z2,z1044,z5,z6]),(0,[z36,z1,z282,z3,z5,z6]),(0,[z143,z686,z2,z3,z135,z6]),(0,[z1045,z1,z2,z3,z5,z6])],[(0,[z1046,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1047])],[(0,[z1,z1048,z2,z3,z5,z6])],[(0,[z0,z1,z202,z3,z5,z379]),(1,[z0,z2,z724,z5,z6]),(0,[z0,z1,z282,z330,z5,z6])],[(0,[z1,z2,z3,z201,z5,z393]),(0,[z1,z2,z5,z68,z24,z11])],[(0,[z1,z14,z2,z559,z5,z6]),(0,[z1,z218,z3,z5,z6,z24]),(0,[z1049,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z3,z5,z6]),(0,[z1050,z1,z2,z3,z5,z6])],[(0,[z1,z1051,z2,z3,z5,z6]),(0,[z0,z1,z2,z129,z5,z6])],[(0,[z0,z1,z2,z1052,z5,z6]),(0,[z0,z1,z2,z832,z5,z6]),(0,[z87,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z1053,z5,z6]),(0,[z80,z0,z2,z3,z5,z10]),(1,[z0,z1,z2,z5,z842]),(0,[z1054,z1,z2,z3,z5,z6])],[(0,[z1055,z1,z2,z3,z5,z6]),(0,[z1056,z1,z2,z3,z5,z6])],[(0,[z122,z1,z2,z3,z5,z544]),(0,[z0,z1,z2,z3,z29,z165])],[(0,[z1,z1057,z2,z3,z5,z6])],[(0,[z0,z1,z1058,z3,z5,z6]),(0,[z1,z2,z3,z5,z67,z458]),(0,[z41,z0,z2,z64,z5,z379]),(0,[z81,z1,z2,z3,z396,z6]),(0,[z0,z1,z2,z1059,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z458,z20]),(0,[z0,z1060,z2,z3,z5,z6]),(0,[z783,z1,z2,z3,z5,z598]),(0,[z155,z1,z2,z3,z5,z193]),(0,[z1061,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1062,z3,z5,z6])],[(0,[z0,z1,z2,z3,z288,z598]),(0,[z133,z0,z25,z3,z5,z544]),(0,[z0,z1,z282,z3,z5,z165])],[(0,[z1,z252,z2,z3,z5,z6]),(0,[z169,z1,z2,z3,z5,z6]),(0,[z382,z1,z2,z3,z5,z474]),(0,[z0,z1,z1063,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z598]),(0,[z1,z2,z3,z1064,z5,z6]),(0,[z1065,z1,z2,z3,z5,z6])],[(0,[z88,z1,z2,z3,z85,z6]),(0,[z1,z2,z3,z1066,z5,z6]),(0,[z1,z1067,z2,z3,z5,z6]),(0,[z79,z36,z1,z26,z5,z6]),(0,[z222,z59,z2,z107,z5,z6]),(0,[z1,z3,z5,z6,z342,z164]),(0,[z0,z275,z2,z58,z5,z6])],[(0,[z36,z1,z299,z3,z5,z6]),(0,[z0,z1,z2,z1068,z5,z6]),(0,[z0,z1,z2,z3,z5,z1069]),(0,[z79,z0,z1,z26,z5,z6])],[(0,[z116,z1,z202,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1070])],[(0,[z0,z1,z1071,z3,z5,z6]),(0,[z1,z2,z200,z3,z5,z239]),(0,[z1,z2,z3,z5,z6,z1072]),(0,[z1073,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1074,z5,z6])],[(0,[z1,z2,z200,z5,z6,z456]),(0,[z36,z74,z2,z3,z5,z19]),(0,[z1075,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z135,z165]),(0,[z1076,z1,z2,z3,z5,z6])],[(0,[z22,z309,z2,z3,z5,z6]),(0,[z1077,z1,z2,z3,z5,z6]),(0,[z0,z1,z282,z3,z5,z193])],[(0,[z1,z14,z2,z3,z5,z947]),(0,[z0,z2,z3,z5,z741,z6])],[(0,[z0,z1078,z2,z3,z5,z6])],[(0,[z685,z14,z2,z3,z5,z6]),(0,[z1,z14,z2,z5,z6,z296]),(0,[z1079,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z742,z5,z6])],[(0,[z0,z1,z2,z330,z135,z6]),(0,[z0,z1,z391,z3,z46,z6]),(0,[z0,z1,z207,z185,z5,z6])],[]],
   [[(0,[z1,z1080,z2,z3,z5,z6]),(0,[z53,z1,z2,z201,z5,z6]),(0,[z1,z2,z3,z288,z6,z24]),(0,[z1,z2,z3,z5,z6,z1081]),(0,[z0,z1,z1082,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1083]),(0,[z22,z59,z2,z107,z5,z6]),(0,[z213,z1,z2,z3,z645,z6]),(0,[z1084,z1,z2,z3,z5,z6])],[(0,[z0,z1,z25,z3,z5,z544]),(0,[z0,z28,z2,z3,z29,z6])],[(0,[z41,z22,z2,z64,z5,z6])],[(0,[z552,z1,z2,z3,z5,z6]),(0,[z1,z14,z202,z3,z5,z6]),(0,[z0,z1,z3,z5,z131,z164]),(0,[z27,z1,z2,z3,z5,z379]),(0,[z1085,z1,z2,z3,z5,z6])],[(0,[z132,z36,z1,z3,z5,z20]),(0,[z0,z1,z2,z3,z278,z379])],[(0,[z1,z14,z2,z23,z5,z68]),(0,[z1086,z1,z2,z3,z5,z6]),(0,[z1087,z1,z2,z3,z5,z6]),(0,[z0,z1,z520,z3,z5,z20]),(0,[z132,z0,z1,z3,z5,z20])],[(0,[z0,z1,z2,z3,z278,z6]),(0,[z1,z2,z3,z5,z6,z1088])],[(0,[z0,z1,z238,z3,z5,z6])],[(0,[z1,z2,z832,z201,z5,z6]),(0,[z326,z2,z3,z5,z6,z24]),(0,[z432,z0,z1,z3,z5,z20]),(0,[z0,z1,z2,z3,z135,z165]),(0,[z1089,z1,z2,z3,z5,z6])],[(0,[z80,z0,z2,z290,z5,z10]),(0,[z381,z0,z1,z3,z5,z20]),(0,[z0,z326,z2,z58,z5,z6])],[],[(0,[z717,z1,z14,z3,z5,z6]),(0,[z257,z1,z2,z345,z5,z6]),(0,[z0,z1,z2,z1090,z5,z6])],[(0,[z1,z2,z3,z76,z5,z458]),(0,[z22,z74,z2,z3,z5,z19]),(0,[z1091,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z418,z6]),(0,[z1,z14,z2,z3,z5,z393]),(0,[z1,z2,z161,z5,z6,z456]),(0,[z122,z1,z2,z3,z5,z598]),(0,[z1092,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z835]),(0,[z1,z2,z3,z5,z24,z164]),(0,[z0,z1,z1093,z3,z5,z6]),(0,[z1,z1094,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z5,z6,z1095]),(0,[z79,z1,z3,z5,z24,z20])],[(0,[z1,z299,z3,z5,z6,z24]),(0,[z0,z2,z3,z5,z517,z10])],[(0,[z169,z1,z2,z290,z5,z6]),(0,[z1096,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1097,z5,z6])],[(0,[z74,z14,z2,z3,z5,z19]),(0,[z1,z101,z2,z3,z5,z6]),(0,[z657,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z5,z193,z24]),(0,[z133,z0,z25,z3,z5,z598]),(0,[z0,z1,z2,z23,z5,z246]),(0,[z0,z1,z2,z3,z1098,z6]),(0,[z1,z1099,z2,z3,z5,z6])],[(0,[z22,z197,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1100]),(0,[z116,z1,z2,z3,z278,z6]),(0,[z1101,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1102]),(0,[z1103,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1104]),(0,[z1,z2,z3,z5,z24,z451]),(0,[z0,z1,z1105,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1106])],[(0,[z1,z14,z2,z993,z5,z6]),(0,[z1,z2,z3,z5,z544,z24]),(0,[z1,z2,z3,z5,z1107,z6]),(0,[z1,z2,z3,z1108,z5,z6])],[(0,[z22,z1,z2,z3,z5,z1109]),(0,[z1110,z1,z2,z3,z5,z6]),(0,[z1111,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1112,z3,z5,z6])],[(0,[z0,z275,z2,z3,z5,z6])],[(0,[z2,z3,z5,z6,z310,z10]),(0,[z1113,z1,z2,z3,z5,z6]),(0,[z80,z0,z30,z3,z5,z10]),(0,[z1,z1114,z2,z3,z5,z6])],[(0,[z36,z1,z3,z5,z6,z164]),(0,[z0,z1,z2,z3,z1115,z6]),(0,[z1116,z1,z2,z3,z5,z6]),(0,[z1117,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z758,z152,z6])],[(0,[z1,z267,z2,z3,z5,z24]),(0,[z1118,z1,z2,z3,z5,z6]),(0,[z74,z2,z3,z5,z6,z310]),(0,[z143,z0,z144,z3,z135,z6]),(0,[z81,z1,z2,z3,z517,z6]),(0,[z1119,z1,z2,z3,z5,z6])],[(0,[z22,z285,z2,z3,z5,z6]),(0,[z0,z1,z2,z62,z5,z6]),(0,[z0,z1,z2,z289,z5,z6])],[(0,[z1,z2,z3,z5,z336,z24]),(0,[z1,z25,z3,z5,z24,z20]),(0,[z90,z1,z3,z96,z6,z24]),(0,[z734,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z1120]),(0,[z0,z1,z2,z3,z293,z6]),(0,[z0,z1,z1121,z3,z5,z6]),(0,[z1122,z1,z2,z3,z5,z6])]],
   [[(0,[z36,z1,z2,z3,z5,z474]),(0,[z1,z2,z3,z5,z340,z24]),(0,[z36,z1,z2,z3,z5,z165]),(0,[z155,z1,z2,z330,z5,z6]),(0,[z0,z2,z3,z135,z6,z165]),(0,[z0,z1,z2,z758,z3,z6]),(0,[z0,z1,z2,z3,z76,z77])],[(0,[z53,z1,z2,z832,z5,z6]),(0,[z1123,z1,z2,z3,z5,z6]),(0,[z1124,z1,z2,z3,z5,z6]),(0,[z1125,z1,z2,z3,z5,z6])],[(0,[z1,z267,z2,z3,z5,z98]),(0,[z1,z2,z3,z343,z5,z24]),(0,[z199,z1,z245,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1126])],[(0,[z36,z1,z2,z185,z5,z6]),(0,[z1127,z1,z2,z3,z5,z6]),(0,[z1128,z1,z2,z3,z5,z379]),(0,[z0,z1,z2,z330,z5,z165]),(0,[z1,z2,z3,z5,z6,z1129])],[(0,[z1,z2,z3,z5,z24,z484]),(0,[z470,z1,z2,z23,z5,z68]),(0,[z0,z275,z218,z3,z5,z6])],[(0,[z216,z1,z52,z3,z5,z474]),(0,[z0,z1,z1130,z3,z5,z6]),(0,[z0,z1,z2,z1131,z5,z6]),(0,[z1128,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z330,z29,z6]),(0,[z1132,z1,z2,z3,z5,z6])],[(0,[z1133,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z842,z11])],[(0,[z1,z43,z2,z5,z24,z11])],[(0,[z0,z1,z1134,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z193]),(0,[z167,z1,z2,z3,z288,z6]),(0,[z0,z2,z3,z135,z10,z31]),(0,[z169,z1,z145,z3,z5,z6]),(0,[z1135,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z3,z5,z336]),(0,[z22,z1,z2,z3,z5,z544]),(0,[z106,z1,z2,z3,z543,z6]),(0,[z1136,z1,z2,z3,z5,z6]),(0,[z1137,z0,z1,z2,z3,z5])],[(0,[z14,z2,z3,z5,z551,z6]),(0,[z1,z2,z3,z5,z6,z1138]),(0,[z1139,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z5,z942])],[(0,[z648,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z5,z6,z814]),(0,[z1,z3,z5,z46,z24,z20]),(0,[z143,z36,z2,z3,z135,z6]),(0,[z1140,z1,z2,z3,z5,z6]),(0,[z155,z1,z2,z3,z5,z165]),(0,[z0,z1,z2,z330,z5,z193]),(0,[z0,z1,z2,z1141,z5,z6])],[(0,[z125,z1,z2,z3,z5,z6]),(0,[z122,z1,z2,z3,z288,z6]),(0,[z116,z1,z2,z3,z293,z6]),(0,[z599,z0,z1,z2,z5,z11]),(0,[z143,z0,z2,z3,z135,z6]),(0,[z1,z2,z3,z1142,z5,z6])],[(0,[z0,z1,z2,z3,z1143,z6]),(0,[z199,z1,z2,z3,z5,z24]),(0,[z1,z2,z368,z3,z5,z24]),(0,[z1,z2,z3,z5,z6,z916])],[(0,[z443,z1,z52,z3,z5,z6]),(0,[z1,z1144,z2,z3,z5,z6]),(0,[z79,z0,z1,z5,z6,z486])],[(0,[z1,z2,z3,z5,z372,z24]),(0,[z36,z1,z45,z3,z46,z6]),(0,[z74,z2,z3,z5,z19,z358]),(0,[z0,z1,z3,z5,z6,z942]),(0,[z0,z1,z2,z3,z5,z883])]],
   [[(0,[z28,z14,z2,z3,z29,z6]),(0,[z36,z1,z2,z3,z5,z24]),(0,[z36,z1,z207,z3,z5,z6])],[(0,[z22,z403,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z737]),(0,[z133,z0,z25,z3,z288,z6])],[(0,[z1,z2,z3,z897,z85,z6]),(0,[z1,z2,z3,z5,z897,z6]),(0,[z1145,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z1146]),(0,[z1147,z1,z2,z3,z5,z6]),(0,[z1148,z1,z2,z3,z5,z6])],[(0,[z59,z2,z107,z5,z6,z24]),(0,[z0,z1,z144,z3,z5,z6]),(0,[z794,z1,z2,z3,z5,z193])],[(0,[z103,z708,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z474]),(0,[z1,z2,z3,z5,z6,z1149]),(0,[z0,z1,z145,z3,z5,z6]),(0,[z0,z2,z724,z64,z5,z6]),(0,[z1150,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z517,z19])],[(0,[z1,z313,z2,z200,z5,z6]),(0,[z1151,z1,z2,z3,z5,z6])],[(0,[z1152,z1,z2,z3,z5,z6])],[(0,[z1,z14,z3,z1031,z5,z6]),(0,[z1,z14,z2,z58,z5,z6]),(0,[z22,z1,z2,z185,z5,z6]),(0,[z0,z1,z173,z3,z5,z67]),(0,[z1,z2,z3,z5,z6,z1153]),(0,[z80,z2,z3,z5,z10,z98]),(1,[z1,z2,z3,z5,z916]),(0,[z132,z125,z1,z3,z5,z20])],[(0,[z1,z1154,z2,z3,z5,z6]),(0,[z1155,z1,z2,z3,z5,z6])],[(0,[z1156,z1,z2,z3,z5,z6])],[],[(0,[z22,z1,z282,z3,z5,z6]),(0,[z41,z27,z2,z64,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1157]),(0,[z1,z2,z3,z5,z24,z549]),(0,[z1,z2,z3,z5,z193,z799]),(0,[z0,z1,z2,z3,z5,z842])],[(0,[z0,z1,z2,z3,z1158,z6]),(0,[z1159,z1,z2,z3,z5,z6]),(0,[z1160,z1,z2,z3,z5,z6])],[(0,[z50,z1,z2,z3,z5,z458]),(0,[z1,z2,z3,z1161,z5,z6]),(0,[z1162,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z481,z418,z6]),(0,[z0,z1,z2,z3,z1163,z6]),(0,[z0,z1,z2,z1164,z5,z6]),(0,[z1165,z1,z2,z3,z5,z6])]],
   [[(0,[z80,z22,z2,z3,z5,z10]),(0,[z1,z2,z200,z5,z464,z6]),(0,[z0,z1,z2,z3,z5,z379]),(0,[z540,z0,z2,z64,z5,z6])],[(0,[z0,z1,z1166,z3,z5,z6]),(0,[z74,z403,z2,z3,z5,z6]),(0,[z133,z0,z760,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z257,z1,z2,z3,z5,z393]),(0,[z1,z207,z3,z5,z6,z24])],[(0,[z22,z1,z45,z3,z46,z6]),(0,[z126,z1,z2,z3,z5,z24]),(0,[z1167,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z3,z5,z168]),(0,[z0,z28,z2,z3,z5,z165]),(0,[z32,z305,z1,z2,z5,z11])],[(0,[z1,z2,z3,z93,z698,z6]),(0,[z1,z2,z3,z236,z6,z427]),(0,[z0,z1,z56,z3,z5,z942])],[(0,[z41,z14,z2,z64,z5,z6]),(0,[z1,z2,z707,z3,z5,z6]),(0,[z1,z30,z3,z5,z6,z24]),(0,[z1168,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1169,z6]),(0,[z0,z1,z3,z5,z6,z1170]),(0,[z1,z1171,z2,z3,z5,z6])],[(0,[z382,z1,z2,z3,z5,z24])],[(0,[z470,z1,z2,z3,z5,z336]),(0,[z0,z1,z2,z1172,z5,z6]),(0,[z1173,z1,z2,z3,z5,z6])],[(0,[z1,z14,z2,z129,z5,z6]),(0,[z1,z2,z3,z5,z1174,z6])],[(0,[z97,z1,z15,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1175])],[(0,[z22,z1,z2,z3,z5,z598]),(0,[z79,z22,z1,z26,z5,z6]),(0,[z1176,z1,z2,z3,z5,z6])],[(0,[z41,z0,z2,z64,z5,z168]),(0,[z1,z2,z3,z1177,z5,z6]),(0,[z1178,z1,z2,z3,z5,z6]),(0,[z1179,z1,z2,z3,z5,z6])],[(0,[z22,z1,z299,z3,z5,z6]),(0,[z0,z1,z218,z3,z5,z6])],[(0,[z116,z1,z2,z3,z5,z379]),(0,[z1,z2,z3,z5,z358,z11])],[(0,[z1,z14,z144,z3,z5,z6]),(0,[z216,z1,z2,z3,z5,z393]),(0,[z0,z1,z2,z3,z1180,z6]),(0,[z316,z0,z2,z3,z5,z10]),(0,[z1181,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1182,z5,z6]),(0,[z1,z826,z2,z3,z5,z6])],[(0,[z116,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1183]),(0,[z86,z0,z1,z2,z185,z31])]],
   [[],[(0,[z0,z1,z760,z3,z5,z6])],[(0,[z1,z1184,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z212])],[(0,[z1,z2,z3,z5,z67,z24]),(0,[z41,z0,z2,z724,z5,z6]),(0,[z0,z1,z145,z289,z5,z6]),(0,[z0,z1,z145,z290,z5,z6])],[(0,[z36,z1,z2,z3,z288,z6])],[(0,[z1,z2,z3,z5,z466,z24]),(0,[z1,z145,z3,z5,z6,z24])],[(0,[z708,z14,z2,z3,z5,z6]),(0,[z868,z0,z1,z2,z5,z6]),(0,[z1185,z1,z2,z3,z5,z6])],[(0,[z1186,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z278,z6,z24])],[(0,[z1,z2,z3,z5,z67,z98]),(0,[z1,z2,z3,z5,z473,z24]),(0,[z36,z1,z2,z330,z5,z6]),(0,[z0,z1,z2,z3,z418,z544])],[(0,[z0,z2,z3,z29,z741,z6]),(0,[z1,z1187,z2,z3,z5,z6])],[],[(0,[z132,z22,z1,z3,z5,z20]),(0,[z111,z1,z2,z201,z5,z6])],[(0,[z1,z1188,z2,z3,z5,z6]),(0,[z86,z0,z326,z2,z3,z31])],[(0,[z0,z1,z2,z3,z5,z945]),(0,[z0,z1,z1189,z3,z5,z6])],[],[(0,[z1,z2,z3,z5,z6,z1190]),(0,[z1191,z1,z2,z3,z5,z6]),(0,[z1192,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1193]),(0,[z27,z1,z2,z3,z5,z168]),(0,[z0,z1,z2,z3,z293,z379])],[(0,[z0,z1,z2,z3,z278,z168]),(0,[z0,z1,z2,z290,z5,z6])],[(0,[z0,z1194,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1195,z6]),(0,[z552,z1,z2,z3,z5,z458]),(0,[z0,z1,z2,z1196,z5,z6]),(0,[z0,z1,z1197,z3,z5,z6])],[],[(0,[z1,z14,z2,z3,z278,z6]),(0,[z103,z2,z3,z5,z6,z310]),(0,[z1,z2,z3,z5,z6,z1198]),(0,[z1,z2,z3,z5,z508,z24]),(0,[z1199,z1,z2,z3,z5,z6]),(0,[z1200,z1,z2,z3,z5,z6])],[(0,[z1,z14,z238,z3,z5,z6]),(0,[z169,z1,z30,z3,z5,z6]),(1,[z0,z2,z3,z5,z800])],[(0,[z1,z2,z3,z5,z6,z458]),(0,[z1,z14,z218,z3,z5,z6]),(0,[z0,z1,z1201,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z916])],[(0,[z22,z1,z2,z3,z288,z6]),(0,[z1,z2,z3,z93,z5,z239]),(0,[z0,z1,z2,z3,z5,z1202]),(0,[z1,z2,z23,z5,z68,z24])],[(0,[z213,z1,z2,z3,z5,z239]),(0,[z1,z2,z3,z5,z6,z1203])],[],[(0,[z0,z1,z2,z3,z5,z1204]),(0,[z0,z1,z2,z1205,z5,z6]),(0,[z0,z1,z2,z1206,z5,z6]),(0,[z0,z1,z2,z3,z5,z1207])],[(0,[z22,z1,z2,z330,z5,z6])],[(1,[z708,z2,z3,z5,z6]),(0,[z1,z1208,z2,z3,z5,z6]),(0,[z361,z14,z2,z3,z5,z6]),(0,[z99,z1,z2,z3,z543,z6])],[(0,[z0,z1,z2,z3,z5,z1209]),(0,[z1210,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z534,z24]),(0,[z0,z1,z2,z5,z131,z296]),(0,[z0,z1,z2,z3,z5,z1211]),(0,[z0,z1,z1212,z3,z5,z6])]],
   [[],[(0,[z0,z118,z2,z3,z29,z6]),(0,[z0,z1,z2,z1213,z5,z6])],[(0,[z216,z1,z647,z3,z5,z6]),(0,[z1,z2,z481,z5,z6,z24]),(0,[z36,z1,z2,z3,z396,z6]),(0,[z0,z1,z30,z3,z5,z6])],[(0,[z22,z1,z3,z5,z6,z164]),(0,[z0,z1,z2,z3,z5,z981]),(0,[z0,z1,z2,z3,z5,z1214]),(0,[z1,z3,z5,z67,z24,z20]),(0,[z133,z122,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1215]),(0,[z0,z326,z2,z3,z5,z6]),(0,[z607,z1,z2,z3,z5,z67])],[(0,[z1,z196,z156,z3,z5,z6]),(0,[z1,z2,z3,z1216,z5,z6]),(0,[z0,z1,z2,z3,z1217,z6])],[(0,[z0,z1,z2,z1218,z5,z6]),(0,[z1,z2,z3,z5,z24,z663])],[(0,[z1219,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1220,z5,z6]),(0,[z0,z1,z129,z5,z6,z20])],[(0,[z22,z1,z2,z3,z5,z165]),(0,[z0,z1221,z2,z3,z5,z6]),(0,[z0,z1,z1222,z3,z5,z6]),(0,[z0,z1,z2,z3,z1223,z6]),(0,[z86,z377,z1,z2,z3,z31])],[(0,[z36,z1,z2,z3,z5,z347]),(0,[z0,z1,z2,z3,z1224,z6])],[(0,[z97,z1,z651,z3,z5,z6]),(0,[z0,z1,z2,z3,z418,z598]),(0,[z41,z0,z299,z64,z5,z6])],[(0,[z2,z3,z5,z6,z310,z98]),(0,[z1,z1225,z2,z3,z5,z6]),(0,[z1226,z1,z2,z3,z5,z6])],[(0,[z383,z403,z2,z3,z5,z6]),(0,[z1,z2,z52,z3,z5,z239])],[(0,[z1,z14,z2,z62,z5,z6]),(0,[z1,z14,z2,z289,z5,z6]),(0,[z1,z2,z3,z5,z19,z458]),(0,[z1227,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z367,z152,z6])],[(0,[z0,z1,z1228,z3,z5,z6]),(0,[z1,z14,z2,z3,z293,z6]),(0,[z257,z1,z2,z832,z5,z6]),(0,[z0,z326,z218,z3,z5,z6])],[(0,[z292,z1,z2,z3,z5,z6]),(0,[z1,z14,z2,z3,z76,z77]),(0,[z155,z1,z2,z559,z5,z6])],[(0,[z22,z1,z2,z3,z5,z193]),(0,[z97,z1,z2,z3,z5,z239])]],
   [[(0,[z1,z215,z2,z3,z632,z6]),(0,[z0,z1,z2,z1229,z5,z6]),(0,[z0,z1,z2,z1230,z5,z6])],[(0,[z695,z14,z2,z3,z5,z6]),(0,[z143,z22,z2,z3,z135,z6]),(0,[z1231,z1,z2,z3,z5,z6]),(0,[z377,z1,z2,z185,z5,z6])],[(0,[z80,z14,z2,z3,z5,z10])],[(0,[z0,z59,z2,z724,z5,z6]),(0,[z0,z1,z2,z3,z883,z31])],[(0,[z0,z1,z2,z3,z1232,z6]),(0,[z0,z1233,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z165,z1149]),(0,[z1,z1234,z2,z3,z5,z6]),(0,[z470,z1,z238,z3,z5,z6])],[(0,[z0,z434,z37,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1235])],[(0,[z22,z1,z2,z3,z396,z6])],[(0,[z22,z1,z207,z3,z5,z6]),(0,[z36,z1,z56,z3,z5,z67]),(0,[z686,z1,z282,z3,z5,z6]),(0,[z0,z1,z2,z289,z5,z10])],[(0,[z22,z1,z2,z3,z5,z823]),(0,[z657,z1,z2,z345,z5,z6]),(0,[z1236,z1,z2,z3,z5,z6]),(0,[z0,z1,z282,z559,z5,z6]),(0,[z0,z1,z1237,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1238,z6]),(0,[z305,z1,z2,z3,z5,z68])],[(0,[z1239,z1,z2,z3,z5,z6]),(0,[z1240,z1,z2,z3,z5,z6]),(0,[z357,z1,z2,z3,z85,z6])],[(0,[z0,z1,z1241,z3,z5,z6])],[(0,[z636,z1,z2,z3,z5,z24]),(0,[z1,z2,z290,z5,z6,z24]),(0,[z1145,z1,z2,z3,z5,z168])],[(0,[z327,z14,z2,z3,z5,z6]),(0,[z1,z2,z3,z592,z5,z24]),(0,[z86,z302,z1,z2,z3,z31])],[(0,[z432,z1,z3,z5,z6,z360]),(1,[z1,z3,z5,z24,z164]),(0,[z90,z36,z1,z3,z96,z6]),(0,[z0,z1,z2,z481,z5,z6]),(0,[z1242,z1,z2,z3,z5,z6]),(0,[z27,z1,z299,z3,z5,z6]),(0,[z1243,z1,z2,z3,z5,z6]),(0,[z377,z1,z207,z3,z5,z6])],[(0,[z1244,z1,z2,z3,z5,z6]),(0,[z0,z1,z299,z3,z278,z6]),(0,[z1245,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1246,z5,z6]),(0,[z32,z0,z1,z2,z5,z842])]],
   [[(0,[z36,z1,z2,z23,z5,z68]),(0,[z0,z1,z2,z1247,z5,z6]),(0,[z1248,z1,z2,z3,z5,z6])],[(0,[z1,z1249,z2,z3,z5,z6]),(0,[z1250,z1,z2,z3,z5,z6]),(0,[z0,z1,z30,z289,z5,z6]),(0,[z0,z1,z30,z290,z5,z6]),(1,[z0,z275,z2,z3,z31])],[(0,[z1,z14,z145,z3,z5,z6]),(0,[z0,z1,z1251,z3,z5,z6])],[(0,[z22,z258,z2,z3,z5,z6]),(0,[z0,z1,z56,z3,z5,z594])],[(0,[z22,z668,z2,z3,z5,z6]),(0,[z1252,z1,z2,z3,z5,z6]),(0,[z1,z2,z367,z297,z152,z6])],[(0,[z623,z0,z1,z3,z5,z20]),(0,[z0,z1,z1253,z3,z5,z6]),(0,[z1,z1254,z2,z3,z5,z6])],[(0,[z228,z1,z2,z3,z5,z24])],[(0,[z1,z204,z2,z3,z5,z6]),(0,[z86,z36,z1,z2,z3,z31]),(0,[z1255,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1256,z5,z6])],[(0,[z0,z1,z2,z3,z5,z239]),(0,[z36,z1,z2,z3,z5,z393])],[(0,[z133,z25,z3,z5,z6,z24])],[(0,[z1,z15,z3,z7,z5,z6]),(0,[z1,z2,z3,z5,z6,z1257])],[(0,[z228,z1,z2,z3,z5,z98]),(0,[z22,z1,z2,z3,z5,z854]),(0,[z22,z1,z56,z3,z5,z67]),(0,[z1,z2,z3,z832,z5,z6])],[(0,[z1,z2,z3,z5,z239,z24]),(0,[z0,z1,z2,z3,z5,z168])],[(0,[z0,z708,z2,z3,z5,z6]),(0,[z1,z1258,z2,z3,z5,z6]),(0,[z1259,z1,z2,z3,z5,z6]),(0,[z305,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z848]),(0,[z0,z306,z2,z3,z5,z19]),(0,[z1260,z1,z2,z3,z5,z6]),(0,[z382,z1,z56,z3,z5,z67])],[(0,[z1,z14,z2,z3,z5,z379]),(0,[z99,z1,z2,z3,z897,z6]),(0,[z1261,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1262,z3,z5,z6]),(0,[z0,z1,z1263,z3,z5,z6]),(0,[z1,z144,z3,z5,z6,z24])]],
   [[(0,[z1,z14,z2,z3,z5,z6]),(0,[z36,z1,z2,z3,z517,z6]),(0,[z0,z1,z2,z64,z5,z168]),(0,[z386,z0,z2,z64,z5,z6]),(0,[z79,z1,z110,z26,z5,z6]),(0,[z0,z1,z2,z3,z5,z1264])],[],[(0,[z50,z1,z2,z3,z5,z24]),(0,[z32,z36,z1,z2,z5,z11]),(0,[z79,z0,z1,z83,z5,z6])],[(0,[z1,z2,z3,z297,z5,z6]),(0,[z50,z1,z2,z3,z5,z737]),(0,[z0,z1265,z2,z3,z5,z6]),(0,[z32,z0,z1,z2,z5,z11])],[(0,[z1266,z1,z2,z3,z5,z6]),(0,[z1267,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1268,z5,z6])],[(0,[z370,z1,z2,z3,z5,z24])],[(0,[z1269,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1270]),(1,[z0,z1,z2,z3,z883])],[(0,[z1,z2,z5,z6,z24,z296]),(0,[z0,z1,z37,z3,z418,z6]),(0,[z0,z1,z2,z1271,z5,z6])],[(0,[z1,z2,z3,z5,z6,z629]),(0,[z1,z2,z3,z1272,z5,z6]),(0,[z1,z2,z3,z506,z5,z24]),(0,[z0,z1,z2,z724,z5,z6]),(0,[z0,z275,z2,z3,z6,z31])],[(0,[z116,z1,z2,z3,z5,z168]),(0,[z1273,z1,z2,z3,z5,z6]),(0,[z86,z0,z1,z218,z3,z31])],[(0,[z257,z1,z2,z627,z5,z6]),(0,[z22,z495,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1274]),(0,[z80,z0,z2,z3,z5,z800]),(0,[z0,z2,z3,z5,z19,z800]),(0,[z1275,z1,z2,z3,z5,z6]),(0,[z302,z1,z2,z185,z5,z6])],[(0,[z0,z1,z1276,z3,z5,z6]),(0,[z1,z2,z3,z5,z67,z358]),(0,[z305,z1,z2,z3,z5,z11])],[(0,[z660,z14,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z68,z458])],[(0,[z22,z618,z2,z3,z5,z6]),(0,[z1277,z1,z2,z3,z5,z6]),(0,[z1278,z1,z2,z3,z5,z6])],[(0,[z14,z2,z3,z5,z231,z6]),(0,[z69,z1,z2,z3,z5,z6]),(0,[z70,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z67,z310]),(0,[z0,z1,z2,z3,z77,z883])],[(0,[z1,z2,z3,z5,z665,z24]),(0,[z167,z1,z2,z3,z418,z6]),(0,[z0,z1,z43,z394,z5,z6]),(0,[z0,z1,z2,z1279,z5,z6])]],
   [[(0,[z0,z1,z2,z5,z6,z1280])],[(0,[z563,z1,z149,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1281,z6]),(0,[z1282,z1,z2,z3,z5,z6])],[(0,[z36,z1,z2,z3,z5,z336]),(0,[z122,z1,z2,z3,z418,z6])],[(0,[z552,z403,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z517,z6]),(0,[z182,z2,z3,z5,z6,z310]),(0,[z0,z1,z2,z5,z6,z1283])],[(0,[z583,z1,z651,z3,z5,z6]),(0,[z0,z1,z1284,z3,z5,z6])],[(0,[z36,z1,z2,z559,z5,z6]),(0,[z0,z1,z2,z1285,z5,z6]),(0,[z316,z0,z2,z3,z135,z6]),(0,[z1286,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z96,z742,z6])],[(0,[z1,z2,z678,z3,z5,z24]),(0,[z1,z2,z3,z5,z6,z1287]),(0,[z0,z1,z56,z129,z5,z6]),(0,[z302,z1,z207,z3,z5,z6])],[(0,[z1288,z1,z2,z3,z5,z6]),(0,[z133,z0,z25,z3,z418,z6]),(0,[z132,z607,z1,z3,z5,z20])],[(0,[z0,z1,z2,z1289,z5,z6]),(0,[z1,z2,z3,z5,z6,z1290])],[(0,[z1,z2,z3,z5,z6,z1291]),(0,[z1292,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z5,z340,z11]),(0,[z1,z1293,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1294,z6]),(0,[z1,z1295,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z293,z168]),(0,[z1,z45,z3,z47,z46,z6]),(0,[z1296,z1,z2,z3,z5,z6]),(0,[z275,z959,z2,z3,z5,z6])],[(0,[z0,z1,z1297,z3,z5,z6]),(0,[z1,z2,z3,z5,z24,z20]),(0,[z87,z0,z2,z3,z5,z10])],[(0,[z657,z1,z2,z3,z5,z393]),(0,[z470,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z24,z164]),(0,[z1,z1298,z2,z3,z5,z6]),(0,[z1299,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1300,z5,z6])],[(0,[z1,z14,z2,z290,z5,z6]),(0,[z1,z2,z3,z5,z6,z1301]),(0,[z1,z707,z52,z3,z5,z6]),(0,[z1,z2,z107,z5,z24,z11]),(0,[z479,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z38,z5,z68]),(0,[z470,z1,z2,z3,z5,z131]),(0,[z0,z1,z2,z3,z5,z1302])]],
   [[(0,[z1,z3,z5,z68,z24,z164]),(0,[z111,z0,z1,z2,z5,z11]),(0,[z987,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z98,z11])],[(0,[z36,z1,z2,z3,z5,z503]),(0,[z1,z2,z185,z5,z6,z24]),(0,[z0,z59,z2,z107,z5,z6])],[(0,[z143,z14,z2,z3,z135,z6]),(0,[z686,z1,z2,z3,z5,z165]),(0,[z1303,z1,z2,z3,z5,z6])],[(0,[z22,z214,z2,z3,z5,z6]),(1,[z1,z707,z3,z5,z6]),(0,[z1304,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1305,z5,z6]),(0,[z0,z1,z2,z559,z5,z165])],[(0,[z102,z1,z2,z3,z5,z6]),(0,[z14,z2,z3,z5,z6,z287]),(0,[z0,z1,z2,z3,z5,z1306]),(0,[z0,z1307,z2,z3,z5,z6]),(0,[z1,z2,z367,z152,z6,z24]),(0,[z1,z2,z3,z5,z1308,z6]),(0,[z79,z269,z1,z26,z5,z6]),(0,[z1,z1309,z2,z3,z5,z6])],[(0,[z414,z1,z2,z3,z91,z6]),(0,[z0,z1,z2,z62,z5,z544]),(0,[z81,z1,z2,z289,z5,z6]),(0,[z79,z0,z1,z753,z5,z6])],[(0,[z0,z1,z3,z1310,z5,z6])],[(0,[z0,z1,z25,z3,z418,z6]),(0,[z1311,z1,z2,z3,z5,z6]),(0,[z1312,z1,z2,z3,z5,z6])],[(0,[z1,z44,z3,z5,z24,z20])],[(0,[z1,z2,z289,z5,z6,z24]),(0,[z36,z1,z2,z5,z6,z296]),(0,[z0,z1,z2,z3,z5,z1313]),(0,[z1314,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z24]),(0,[z22,z178,z2,z3,z5,z6]),(0,[z686,z1,z2,z3,z5,z193]),(0,[z607,z1,z2,z3,z5,z20]),(0,[z1,z2,z23,z5,z68,z342])],[(0,[z36,z1,z2,z3,z5,z130]),(0,[z1,z2,z3,z5,z6,z737]),(0,[z1,z2,z3,z5,z24,z260]),(0,[z1315,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z559,z5,z193]),(0,[z0,z527,z2,z3,z29,z6]),(0,[z1316,z1,z2,z3,z5,z6]),(0,[z32,z70,z1,z2,z5,z11])],[(0,[z0,z1,z2,z3,z5,z786])],[(0,[z1,z2,z3,z5,z6,z1317]),(0,[z53,z1,z2,z3,z5,z239]),(0,[z0,z1,z2,z3,z5,z1318]),(0,[z1319,z1,z2,z3,z5,z6]),(0,[z0,z1,z299,z64,z5,z6]),(0,[z0,z74,z2,z3,z5,z19]),(0,[z74,z452,z2,z3,z5,z19]),(0,[z1320,z1,z2,z3,z5,z6])],[(0,[z478,z0,z2,z64,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z98]),(0,[z1,z14,z30,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1321])],[(0,[z36,z1,z202,z3,z5,z6]),(0,[z262,z0,z1,z26,z5,z6]),(0,[z0,z1,z1322,z3,z5,z6]),(0,[z0,z1,z23,z5,z68,z164])],[(0,[z1,z313,z2,z531,z5,z6]),(0,[z53,z1,z2,z279,z5,z6]),(0,[z1139,z1,z2,z3,z5,z544]),(0,[z90,z0,z1,z3,z96,z6])],[(0,[z0,z1,z2,z1323,z5,z6]),(0,[z0,z28,z2,z3,z741,z6]),(0,[z1324,z1,z2,z3,z5,z6]),(0,[z1288,z275,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1325]),(0,[z1326,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1327,z5,z6])],[],[(1,[z1,z2,z3,z5,z737])],[(0,[z0,z1,z2,z3,z1328,z6])],[(0,[z0,z1,z2,z1329,z5,z6]),(0,[z0,z2,z3,z517,z6,z10]),(0,[z0,z2,z3,z5,z6,z800]),(0,[z0,z1,z2,z3,z532,z77]),(0,[z1330,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1331,z5,z6])],[(0,[z57,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1109]),(0,[z143,z155,z2,z3,z135,z6]),(0,[z1,z1332,z2,z3,z5,z6]),(0,[z132,z0,z1,z3,z5,z942])],[(0,[z0,z1,z2,z3,z5,z1333]),(0,[z1,z14,z2,z367,z152,z6]),(0,[z167,z1,z2,z62,z5,z6]),(0,[z359,z1,z2,z367,z152,z6])],[(0,[z1334,z1,z2,z3,z5,z6]),(0,[z97,z1,z707,z3,z5,z6]),(0,[z1,z15,z707,z3,z5,z6]),(0,[z1,z2,z5,z456,z24,z11]),(0,[z36,z1,z2,z3,z418,z6]),(0,[z0,z1,z2,z3,z1335,z6]),(0,[z0,z1,z30,z3,z5,z10]),(0,[z86,z0,z1,z2,z3,z31])],[(0,[z121,z14,z2,z3,z5,z6]),(0,[z1336,z1,z2,z3,z5,z6]),(0,[z0,z1,z1337,z3,z5,z6]),(0,[z81,z1,z145,z3,z5,z6]),(0,[z1338,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z128,z24]),(0,[z0,z1,z2,z289,z5,z19])],[(0,[z22,z1,z2,z5,z6,z296]),(0,[z1339,z1,z2,z3,z5,z6]),(0,[z1340,z1,z2,z3,z5,z6]),(0,[z1341,z1,z2,z3,z5,z6])],[(0,[z0,z1,z3,z5,z10,z164]),(0,[z0,z1,z207,z58,z5,z6])]],
   [[(0,[z1,z2,z64,z5,z24,z11]),(0,[z1,z2,z3,z1342,z5,z6]),(0,[z1343,z1,z2,z3,z5,z6]),(0,[z0,z1,z1344,z3,z5,z6]),(0,[z0,z1,z1345,z3,z5,z6]),(0,[z382,z1,z2,z5,z6,z296])],[(0,[z1,z15,z3,z5,z277,z6]),(0,[z0,z1,z2,z3,z5,z1346]),(0,[z888,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z753,z5,z6]),(0,[z0,z1,z2,z601,z152,z6])],[(0,[z1,z2,z3,z1347,z5,z6]),(0,[z1,z2,z3,z5,z6,z1348]),(0,[z0,z1,z45,z3,z742,z6])],[(0,[z359,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1349,z6]),(0,[z155,z1,z144,z3,z5,z6])],[(0,[z0,z1350,z2,z3,z5,z6]),(0,[z412,z1,z368,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1351])],[(0,[z1,z2,z3,z110,z5,z6]),(0,[z0,z1,z2,z1352,z5,z6]),(0,[z0,z1,z2,z3,z5,z1353])],[(0,[z435,z1,z2,z3,z5,z458]),(0,[z143,z0,z282,z3,z135,z6]),(0,[z0,z1,z1354,z3,z5,z6]),(0,[z251,z0,z2,z3,z5,z10])],[(0,[z1355,z1,z2,z3,z5,z6]),(0,[z22,z1,z2,z23,z5,z68]),(0,[z0,z1,z2,z3,z1356,z6]),(0,[z1,z2,z129,z5,z67,z24]),(0,[z0,z1,z2,z62,z5,z598])],[(0,[z1357,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z310,z11]),(0,[z540,z0,z2,z3,z5,z10])],[(0,[z1,z238,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z1358]),(0,[z0,z1,z2,z3,z1359,z6]),(0,[z1360,z1,z2,z3,z5,z6])],[(0,[z81,z1,z2,z3,z5,z6]),(0,[z1,z2,z559,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z544]),(0,[z0,z1,z299,z3,z293,z6]),(0,[z80,z552,z2,z3,z5,z10])],[],[(0,[z1,z14,z2,z481,z5,z6]),(0,[z0,z1,z2,z3,z1361,z6]),(0,[z1362,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1363,z5,z6])],[(0,[z213,z1,z2,z3,z522,z6]),(0,[z80,z169,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1364])],[(0,[z22,z1,z2,z3,z418,z6]),(0,[z22,z1,z2,z3,z5,z393]),(0,[z36,z1,z2,z3,z278,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 508) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 508).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1013).take 394) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1407)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [508, 505, 394] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 151).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 151).take 145).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 296).take 151).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 447).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [151, 145, 151, 65] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_46220

theorem PEqualNP.Outside.L_meta_46220 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46220.solve