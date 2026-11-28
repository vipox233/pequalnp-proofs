import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46266

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
  Nat.testBit (4278124200 * 2 ^ 32 + 4274585216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0080c09b830d22c4#64 ++ 0x040203026e0c348b#64 ++ 0x8281c1ff871d27f7#64 ++ 0xfa0a0707fe1c749f#64 : BitVec 256),
   (0x0106224508762958#64 ++ 0x680418891421d8a5#64 ++ 0xc50e264719fe39fe#64 ++ 0xf71438991c67f8e7#64 : BitVec 256),
   (0x01b02868a1a34190#64 ++ 0xb006c0a1a2868d06#64 ++ 0xb9f03878e1e3c1ed#64 ++ 0xaee7c0e1e3878f07#64 : BitVec 256),
   (0x0e00150054009421#64 ++ 0x0038005401500250#64 ++ 0xbe003f80fe03fe3f#64 ++ 0x9ef800fe03f80ff8#64 : BitVec 256),
   (0x1edb4000ffd80001#64 ++ 0xc07b6d0003ff6000#64 ++ 0xdfffc000fffc001c#64 ++ 0x7f7fff0003fff000#64 : BitVec 256),
   (0x2f6dbff60000003e#64 ++ 0x00bdb6ffd8000000#64 ++ 0xefffffff00000003#64 ++ 0xffbffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff871d27f7 0xfa0a0707fe1c749f

def z1 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264719fe39fe 0xf71438991c67f8e7

def z2 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878e1e3c1ed 0xaee7c0e1e3878f07

def z3 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003f80fe03fe3f 0x9ef800fe03f80ff8

def z4 : W := mkw 0x0e00959b5405b6e5 0x043802566d5016db 0xbe003ffffe03ffff 0x9ef800fffff80fff

def z5 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000fffc001c 0x7f7fff0003fff000

def z6 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff00000003 0xffbffffffc000000

def z7 : W := mkw 0x11df6245abfe2958 0xe8477d8916aff8a5 0x41ffc04701fc01c0 0x6107ff011c07f007

def z8 : W := mkw 0x0120286000000010 0x000480a180000000 0xa9f0387800000001 0xaea7c0e1e0000000

def z9 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x41ffc00001fc0000 0x6107ff000007f000

def z10 : W := mkw 0x00900008a1a34180 0xb002400022868d06 0x10000000e1e3c1ec 0x0040000003878f07

def z11 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffff80fffffe3f 0xfffffffe03fffff8

def z12 : W := mkw 0x0120286000000010 0x000480a180000000 0xb9f03878e003c02d 0xaee7c0e1e3800f00

def z13 : W := mkw 0x00904000a3880000 0x80024100028e2000 0x9bf1c000e7fc001c 0x7e6fc700039ff000

def z14 : W := mkw 0x0000809200000004 0x0000020248000000 0x8281c1ff00000003 0xfa0a0707fc000000

def z15 : W := mkw 0x2fedffff830d22fe 0x04bfb7fffe0c348b 0xefffffff871d27f7 0xffbffffffe1c749f

def z16 : W := mkw 0x01242a6400000018 0x000490a990000000 0xedfe3e7f00000003 0xffb7f8f9fc000000

def z17 : W := mkw 0x1e5b00007cd00001 0xc0796c0001f34000 0x5d7e000078e00008 0x0575f80001e38000

def z18 : W := mkw 0x1edbc09bffdd22c5 0xc47b6f026fff748b 0xdfffc1fffffd27ff 0xff7fff07fffff49f

def z19 : W := mkw 0x2f6dbff60022013e 0x20bdb6ffd8008804 0xefffffff01e201ef 0xffbffffffc078807

def z20 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffffe03fe3f 0xfffffffffff80ff8

def z21 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x99f00078e1e001cc 0x2e67c001e3878007

def z22 : W := mkw 0x0006c2970a5c2a4c 0x4c001b0a5c2970a9 0x460fc7871e1c3e12 0x51183f1e1c7870f8

def z23 : W := mkw 0x0104224400000018 0x0004108910000000 0xc50e264700000002 0xf71438991c000000

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8003800e003c02d 0x8ee000e003800f00

def z25 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x01f0007801e001c0 0x2007c001e0078007

def z26 : W := mkw 0x0e49000000000000 0x0039240000000000 0xcfffc00000000000 0x7f3fff0000000000

def z27 : W := mkw 0x0106224408720918 0x680418891021c824 0xc50e260018e2383e 0x97143898006388e0

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x840026001802383e 0x96100098006008e0

def z29 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6bffd9ff00000001 0x69afff67fc000000

def z30 : W := mkw 0x1edb4001fffe2941 0xe87b6d0007fff8a5 0xdfffc000fffe39fc 0x7f7fff0003fff8e7

def z31 : W := mkw 0x0049000000000000 0x0001240000000000 0x41ffc00000000000 0x6107ff0000000000

def z32 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x41ffc07f00000000 0x6107ff01fc000000

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200018086012637 0x9a08000602180498

def z34 : W := mkw 0x0e80d59bd70db6e5 0x043a03566f5c36db 0xbe81ffffff1fffff 0xfefa07fffffc7fff

def z35 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc5ffe67f00000002 0xf717ff99fc000000

def z36 : W := mkw 0x0000150000009420 0x0000005400000250 0x20003f800003fe23 0x808000fe00000ff8

def z37 : W := mkw 0x216d2a640000001a 0x0085b4a990000000 0x417e000000000000 0x0105f80000000000

def z38 : W := mkw 0x2124bff60000003e 0x008492ffd8000000 0x20003fff00000003 0x808000fffc000000

def z39 : W := mkw 0x0100204000220110 0x2004008100008804 0x0100200000e20008 0x0404008000038800

def z40 : W := mkw 0x1edb4008ffd90081 0xc07b6d0023ff6402 0xdfffc078fffd01fd 0xff7fff01e3fff407

def z41 : W := mkw 0x01b0e8fba3af63d4 0xb406c3a3ee8ebd8f 0xbbf1f9ffe7ffe7ff 0xfeefc7e7ff9fff9f

def z42 : W := mkw 0x0100204000220110 0x2004008100008804 0x8100204001e201ec 0xa604008100078807

def z43 : W := mkw 0x00b00828a1814080 0x9002c020a2860502 0x38f01838e001c001 0x08e3c060e3800700

def z44 : W := mkw 0x01b62a6da9f769d8 0xf806d8a9b6a7dda7 0xfdfe3e7ff9fff9ff 0xfff7f8f9ffe7ffe7

def z45 : W := mkw 0x0004020400000008 0x0000100810000000 0x440e060700000002 0x511038181c000000

def z46 : W := mkw 0x0006020508542848 0x48001808142150a1 0x440e0607181c3812 0x511038181c6070e0

def z47 : W := mkw 0x0000809b000522c4 0x040002026c00148b 0x800001ff011d27f7 0xf2000007fc04749f

def z48 : W := mkw 0x3efbddb2ffd80027 0xc0fbef76cbff6000 0xffffd9b8fffc001d 0x7fffff66e3fff000

def z49 : W := mkw 0x10924000ffd80001 0xc042490003ff6000 0xd50e0000fffc001c 0x7754380003fff000

def z50 : W := mkw 0x2e699db254009427 0x00b9a676c9500250 0x3af1d9b8e601c601 0x08ebc766e3980718

def z51 : W := mkw 0x0000000100042040 0x0000000004001081 0x80000047011c21f6 0xf20000011c047087

def z52 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff071c27d2 0x700a0707fc1c709f

def z53 : W := mkw 0x0fb03d68f5a3d5b1 0xb03ec0f5a3d68f56 0xbff03ff8ffe3ffff 0xbeffc0ffe3ff8fff

def z54 : W := mkw 0x0000c09b020d22c4 0x040003026c08348b 0x0201c1ff061d27f3 0xd0080707fc18749f

def z55 : W := mkw 0x00900000a1800000 0x8002400002860000 0x99f00000e1e0000c 0x2e67c00003878000

def z56 : W := mkw 0x0000000100042040 0x0000000004001081 0x820001c7871d27f7 0xfa0800071e1c749f

def z57 : W := mkw 0x0000000054009401 0x0000000001500250 0x10000000e601c600 0x0040000003980718

def z58 : W := mkw 0x0104224500262958 0x28041089140098a5 0x00002647000239e2 0x800000991c0008e7

def z59 : W := mkw 0x1fdf6245fffe2959 0xe87f7d8917fff8a5 0xdfffe647fffe39fe 0xff7fff991ffff8e7

def z60 : W := mkw 0x0e00000054000001 0x0038000001500000 0xbe003800fe03c03d 0x9ef800e003f80f00

def z61 : W := mkw 0x0106224408720918 0x680418891021c824 0x450e260018e21808 0x0514389800638860

def z62 : W := mkw 0x2f6d3f640000003a 0x00bdb4fd90000000 0x6d7e3e0000000000 0x05b5f8f800000000

def z63 : W := mkw 0x206988b200000006 0x0081a622c8000000 0x00f1c03800000000 0x0003c700e0000000

def z64 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe001980fe01c61d 0x1ef8006603f80718

def z65 : W := mkw 0x01b62a6da9f769d8 0xf806d8a9b6a7dda7 0xc5fe267f19fe39fe 0xf717f899fc67f8e7

def z66 : W := mkw 0x2e4d97960000002e 0x00b9365e58000000 0xee0fff8700000003 0xdfb83ffe1c000000

def z67 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x410e264701fe39e2 0xe10438991c07f8e7

def z68 : W := mkw 0x3ffffff6ffd8003f 0xc0ffffffdbff6000 0xfffffffffffc001f 0xfffffffffffff000

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0xba003980e603e63f 0x9ee800e603980f98

def z70 : W := mkw 0x018662458b7e2958 0x68061989162df8a5 0xc78fe6479ffe39fe 0xff1e3f991e7ff8e7

def z71 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8081c07f811d01e5 0xea020701fe047407

def z72 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0081c1ff011d27e3 0xe0020707fc04749f

def z73 : W := mkw 0x10d94000a3880000 0x80436500028e2000 0x00f1c00000000000 0x0003c70000000000

def z74 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0081c07f011c01c0 0x60020701fc047007

def z75 : W := mkw 0x0e00150000000020 0x0038005400000000 0x0600078000000002 0x1018001e00000000

def z76 : W := mkw 0x0000000000000000 0x0000000000000000 0xc50e000000000000 0x7714380000000000

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200018086010601 0x0808000602180418

def z79 : W := mkw 0x0104224400000018 0x0004108910000000 0x450e260000000000 0x0514389800000000

def z80 : W := mkw 0x2f6fbff75c76bd7f 0x68bdbeffdd71daf5 0xffffffffffffffff 0xffffffffffffffff

def z81 : W := mkw 0x0e00150054009421 0x0038005401500250 0x060007801e003e12 0x1018001e007800f8

def z82 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xefffffff1e003e13 0xffbffffffc7800f8

def z83 : W := mkw 0x0120286800234190 0x300480a1a0008d06 0xa9f038780003c1e1 0xaea7c0e1e0000f07

def z84 : W := mkw 0x0000000100042040 0x0000000004001081 0x00000007001c2012 0x500000001c007080

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000004700000002 0xf20000011c000000

def z86 : W := mkw 0x0006020508762948 0x680018081421d8a5 0x440e060719fe39fe 0x511038181c67f8e7

def z87 : W := mkw 0x00900008a1a34180 0xb002400022868d06 0x99f00000e1e3c1ec 0x2e67c00003878f07

def z88 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3a003f80e603fe23 0x88e800fe03980ff8

def z89 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x47ffc0001ffc0010 0x711fff00007ff000

def z90 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xd9ffc000e1fc000c 0x6f67ff000387f000

def z91 : W := mkw 0x105b000028d00000 0xc0416c0000a34000 0x417e000000e00000 0x0105f80000038000

def z92 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xdfffc000fffffe3c 0x7f7fff0003fffff8

def z93 : W := mkw 0x0000c093020c2244 0x040003024c083089 0x0201c187061c2612 0x500807061c187098

def z94 : W := mkw 0x0100204000220110 0x2004008100008804 0xb9003840e1e3c1ed 0xaee400e103878f07

def z95 : W := mkw 0x0102204008720110 0x600408810021c804 0xc50e204019fe01fc 0xf71438810067f807

def z96 : W := mkw 0x01b02868f5a3d591 0xb006c0a1a3d68f56 0xb9f03878ffe3fffd 0xaee7c0e1e3ff8fff

def z97 : W := mkw 0x0080000881010080 0x0002000022040402 0x80800078810101e5 0xaa020001e2040407

def z98 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc180fffd263f 0xff7fff0603fff498

def z99 : W := mkw 0x2fedffff830d22fe 0x04bfb7fffe0c348b 0xefffffff011c01c3 0xffbffffffc047007

def z100 : W := mkw 0x1e4b40005e580001 0x40792d0001796000 0x460fc0001e1c0010 0x51183f0000787000

def z101 : W := mkw 0x1ffb6868fffb4191 0xf07feda1a3ffed06 0xfffff878ffffc1fd 0xffffffe1e3ffff07

def z102 : W := mkw 0x2e4d97960000002e 0x00b9365e58000000 0x460fc78700000002 0x51183f1e1c000000

def z103 : W := mkw 0x0e00150000000020 0x0038005400000000 0xae003f8000000003 0x9eb800fe00000000

def z104 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0x51ffc000fffc001c 0x6147ff0003fff000

def z105 : W := mkw 0x21fdaafea1a3419e 0xb087f6abfa868d06 0xf9fff87fe1e3c1ed 0xefe7ffe1ff878f07

def z106 : W := mkw 0x0000809b000522c4 0x040002026c00148b 0x000001ff000127e3 0x80000007fc00049f

def z107 : W := mkw 0x01b0a8fba1a763d4 0xb406c2a3ee869d8f 0xb9f039ffe1e3e7ef 0xaee7c0e7ff878f9f

def z108 : W := mkw 0x2f6fbff70876297e 0x68bdbeffdc21d8a5 0xefffffff19fe39ff 0xffbffffffc67f8e7

def z109 : W := mkw 0x0080400083080000 0x00020100020c2000 0x8281c000871c0014 0x7a0a0700021c7000

def z110 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x410e004701fc01c0 0x610438011c07f007

def z111 : W := mkw 0x0e49000054000001 0x0039240001500000 0xdfffc000fe00001c 0x7f7fff0003f80000

def z112 : W := mkw 0x0002000008500000 0x4000080000214000 0xc50e000019fc001c 0x771438000067f000

def z113 : W := mkw 0x0120286000220110 0x200480a180008804 0xa9f0387801e201ed 0xaea7c0e1e0078807

def z114 : W := mkw 0x1ed95500f7889421 0x807b655403de2250 0x3af1d980e601c601 0x08ebc76603980718

def z115 : W := mkw 0x0080c09a83090284 0x040203026a0c240a 0x8281c1f8870107e5 0xaa0a0707e21c041f

def z116 : W := mkw 0x0184e2df830d22dc 0x0406138b7e0c348b 0xc78fe7ff871d27f7 0xff1e3f9ffe1c749f

def z117 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1b8871d27f5 0x080a0706e21c749f

def z118 : W := mkw 0x3fffeaf6ffd8001f 0xc0ffffabdbff6000 0xdfffc07ffffc001c 0x7f7fff01fffff000

def z119 : W := mkw 0x0e00150054009421 0x0038005401500250 0x860027801e023e3e 0x9618009e007808f8

def z120 : W := mkw 0x01b62a6da9f769d8 0xf806d8a9b6a7dda7 0xf9fe387fe1ffc1ed 0xefe7f8e1ff87ff07

def z121 : W := mkw 0x0130286020a24110 0xb004c0a180828904 0x3970380060e2c008 0x04e5c0e001838b00

def z122 : W := mkw 0x1edbc09bffdd22c5 0xc47b6f026fff748b 0xdfffc07ffffc01dc 0x7f7fff01fffff007

def z123 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3c003e007802d808 0x04f000f801e00b60

def z124 : W := mkw 0x1ed94000f7880001 0x807b650003de2000 0x1af1c000e6000000 0x086bc70003980000

def z125 : W := mkw 0x0002000108762940 0x680008000421d8a5 0x0000000019fe39fc 0x000000000067f8e7

def z126 : W := mkw 0x2124bffe002341be 0x308492fff8008d06 0x20003fff0003c1e3 0x808000fffc000f07

def z127 : W := mkw 0x11b26868fffb4191 0xf046c9a1a3ffed06 0xb9f03878ffffc1fd 0xaee7c0e1e3ffff07

def z128 : W := mkw 0x0e80d59ad70996a5 0x043a03566b5c265a 0xbe81ffb8fe03fe3f 0x9efa07fee3f80ff8

def z129 : W := mkw 0x0080000081000000 0x0002000002040000 0x8080000081000004 0x2a02000002040000

def z130 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6fffffb800000001 0x0dbffffee0000000

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400260018021808 0x0410009800600860

def z132 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f0387861e2c1c8 0x24e7c0e1e1878b07

def z133 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3a001980e601c601 0x08e8006603980718

def z134 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x410e004719fe39fc 0x610438011c67f8e7

def z135 : W := mkw 0x0080000881010080 0x0002000022040402 0x828001f8870127f7 0xba0a0007e21c049f

def z136 : W := mkw 0x2e4d97965400942f 0x00b9365e59500250 0x460fc7871e003e12 0x51183f1e1c7800f8

def z137 : W := mkw 0x0130286820a34190 0xb004c0a1a0828d06 0x3970387860e3c1e9 0x84e5c0e1e1838f07

def z138 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbdf03e78f9e3f9ff 0xbef7c0f9e3e78fe7

def z139 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xe9fff87f00000001 0xefa7ffe1fc000000

def z140 : W := mkw 0x11fb6868abfb4190 0xf047eda1a2afed06 0xf9fff878e1ffc1ed 0xefe7ffe1e387ff07

def z141 : W := mkw 0x21edeaff830d22de 0x0487b7abfe0c348b 0xc3ffc1ff871d27f7 0xfb0fff07fe1c749f

def z142 : W := mkw 0x0080c09a83090284 0x040203026a0c240a 0x0081c03800000000 0x00020700e0000000

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc003e00f803f83f 0x9ef000f803e00fe0

def z144 : W := mkw 0x2f6fbff70876297e 0x68bdbeffdc21d8a5 0xefffffff01fc01c3 0xffbffffffc07f007

def z145 : W := mkw 0x1ffb6868fffb4191 0xf07feda1a3ffed06 0xdfffc078fffc01dc 0x7f7fff01e3fff007

def z146 : W := mkw 0x0ed90000a1800000 0x803b640002860000 0xdfffc000e1e0000c 0x7f7fff0003878000

def z147 : W := mkw 0x01b06869a3af63d0 0xb406c1a1a68ebd8f 0xb9f03878e7ffe7fd 0xaee7c0e1e39fff9f

def z148 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x560fc000fffc001c 0x51583f0003fff000

def z149 : W := mkw 0x0e49809200000004 0x0039260248000000 0xcfffc1ff00000003 0xff3fff07fc000000

def z150 : W := mkw 0x0e00150000000020 0x0038005400000000 0xae003f801802383f 0x9eb800fe006008e0

def z151 : W := mkw 0x0090c09ba38d22c4 0x840243026e8e348b 0x9bf1c1ffe7fd27ff 0xfe6fc707ff9ff49f

def z152 : W := mkw 0x01962245a9f62958 0xe806588916a7d8a5 0xddfe2647f9fe39fe 0xff77f8991fe7f8e7

def z153 : W := mkw 0x01a0e8fb832f63d4 0x340683a3ee0cbd8f 0xa281f9ff871fe7f7 0xfa8a07e7fe1c7f9f

def z154 : W := mkw 0x3ffffff6ffd8943f 0xc0ffffffdbff6250 0xfffffffffffffe3f 0xfffffffffffffff8

def z155 : W := mkw 0x2f69bdf200000036 0x00bda6f7c8000000 0xabf1f9f800000001 0xaeafc7e7e0000000

def z156 : W := mkw 0x0f04374454009439 0x003c10dd11500250 0xff0e3fc7fe03fe3f 0xfffc38ff1ff80ff8

def z157 : W := mkw 0x2e699db200000026 0x00b9a676c8000000 0x2af1d9b800000001 0x08abc766e0000000

def z158 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xfffffffffe00001f 0xfffffffffff80000

def z159 : W := mkw 0x00904009a3af63c0 0xb4024100268ebd8f 0x10000000e7ffe7fc 0x00400000039fff9f

def z160 : W := mkw 0x00804009830d22c0 0x04020100260c348b 0x00000000871d27f4 0x00000000021c749f

def z161 : W := mkw 0x10924000ffd80001 0xc042490003ff6000 0x10000000fffc001c 0x0040000003fff000

def z162 : W := mkw 0x2ffdbffea1a341be 0xb0bff6fffa868d06 0xffffffffe1e3c1ef 0xffffffffff878f07

def z163 : W := mkw 0x0fb02868f5a34191 0xb03ec0a1a3d68d06 0xbff03878ffe3c1fd 0xbeffc0e1e3ff8f07

def z164 : W := mkw 0x2f6d3f640000003a 0x00bdb4fd90000000 0xed7e3e4700000002 0xf7b5f8f91c000000

def z165 : W := mkw 0x1e5b40007ed80001 0xc0796d0001fb6000 0x5f7fc0007efc0018 0x557dff0001fbf000

def z166 : W := mkw 0x00004001020c2240 0x0400010004083089 0x00000000061c2610 0x0000000000187098

def z167 : W := mkw 0x2e4d97960000002e 0x00b9365e58000000 0xc68fc7ff00000003 0xfb1a3f1ffc000000

def z168 : W := mkw 0x10924009ffdd22c1 0xc442490027ff748b 0x10000000fffd27fc 0x0040000003fff49f

def z169 : W := mkw 0x0100204000000010 0x0004008100000000 0x8100204000000000 0xa604008100000000

def z170 : W := mkw 0x0e00150054009421 0x0038005401500250 0xba003980e603c62d 0x8ee800e603980f18

def z171 : W := mkw 0x0002000008500000 0x4000080000214000 0xc50e260019fe383e 0xf71438980067f8e0

def z172 : W := mkw 0x0104224500262958 0x28041089140098a5 0x00000047000001c0 0x000000011c000007

def z173 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6dfffe7f00000000 0x65b7fff9fc000000

def z174 : W := mkw 0x0e805500d7089421 0x003a0154035c2250 0xbe81ff80ff1ffe3f 0xfefa07fe03fc7ff8

def z175 : W := mkw 0x01b42a6ca1a34198 0xb006d0a9b2868d06 0xfdfe3e7fe1e3c1ef 0xfff7f8f9ff878f07

def z176 : W := mkw 0x1e4b55005e589421 0x40792d5401796250 0xfe0fff80fe1ffe3f 0xdff83ffe03f87ff8

def z177 : W := mkw 0x2124bff60000943e 0x008492ffd8000250 0x20003fff0003fe23 0x808000fffc000ff8

def z178 : W := mkw 0x0080c09bd70db6c5 0x040203026f5c36db 0x9281c1ffff1fffff 0xfa4a0707fffc7fff

def z179 : W := mkw 0x10924001fffe2941 0xe842490007fff8a5 0x10000000fffe39fc 0x0040000003fff8e7

def z180 : W := mkw 0x10dbc09babdd22c4 0xc4436f026eaf748b 0xc3ffc1ff87fd27f7 0xfb0fff07fe1ff49f

def z181 : W := mkw 0x0000400002080000 0x0000010000082000 0x0201c000061c0010 0x5008070000187000

def z182 : W := mkw 0x2ffdbffea18140be 0x90bff6fffa860502 0xffffffffe001c003 0xffffffffff800700

def z183 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffe600fffe383e 0xff7fff9803fff8e0

def z184 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x47ffc7ff00000002 0x711fff1ffc000000

def z185 : W := mkw 0x0e80c09bd70d22c5 0x043a03026f5c348b 0x9e81c1ffff1d27ff 0xfe7a0707fffc749f

def z186 : W := mkw 0x0186e2df8b7f2bdc 0x6c061b8b7e2dfcaf 0x418fc07f01fc01c0 0x61063f01fc07f007

def z187 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xdfffc780fffc3e1e 0x7f7fff1e03fff0f8

def z188 : W := mkw 0x0000000800234180 0x3000000020008d06 0x000000000003c1e0 0x0000000000000f07

def z189 : W := mkw 0x0186e2df8b7f2bdc 0x6c061b8b7e2dfcaf 0xc78fe7ff9fff3fff 0xff1e3f9ffe7ffcff

def z190 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080007800000001 0xaa020001e0000000

def z191 : W := mkw 0x0020082800014080 0x10008020a0000502 0x200018380001c001 0x00800060e0000700

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400060018003812 0x10100018006000e0

def z193 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc5ffc00019fc001c 0x7717ff000067f000

def z194 : W := mkw 0x00b00828a1814080 0x9002c020a2860502 0xb9f01838e1e1c00d 0x2ee7c060e3878700

def z195 : W := mkw 0x1edb4008fffb4181 0xf07b6d0023ffed06 0xdfffc000ffffc1fc 0x7f7fff0003ffff07

def z196 : W := mkw 0x0080400083080000 0x00020100020c2000 0x0081c000011c0000 0x6002070000047000

def z197 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0081c07f871d27f4 0x60020701fe1c749f

def z198 : W := mkw 0x0f203d6054009431 0x003c80f581500250 0xbff03ff8fe03fe3f 0xbeffc0ffe3f80ff8

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000040010001e4 0xa200000100040007

def z200 : W := mkw 0x0180204881230190 0x2006008122048c06 0x8180207881e301ed 0xae060081e2078c07

def z201 : W := mkw 0x0e4b000008500000 0x40392c0000214000 0xcfffc00019fc001c 0x7f3fff000067f000

def z202 : W := mkw 0x0120286800234190 0x300480a1a0008d06 0x200038780003c1e1 0x808000e1e0000f07

def z203 : W := mkw 0x0000000054009401 0x0000000001500250 0x10000000fe03fe3c 0x0040000003f80ff8

def z204 : W := mkw 0x0120a8f200000014 0x000482a3c8000000 0xabf1f9ff00000003 0xfeafc7e7fc000000

def z205 : W := mkw 0x1e4bc0935e5c2245 0x44792f024d797089 0x460fc1871e1c2612 0x51183f061c787098

def z206 : W := mkw 0x0fb0fdfbf7aff7f5 0xb43ec3f7efdebfdf 0xbff1ffffffffffff 0xfeffc7ffffffffff

def z207 : W := mkw 0x00b00828a1814080 0x9002c020a2860502 0xb8f03838e003c02d 0x8ee3c0e0e3800f00

def z208 : W := mkw 0x0e49150000000020 0x0039245400000000 0xefffff8000000003 0xffbffffe00000000

def z209 : W := mkw 0x10924000abd80000 0xc042490002af6000 0x0000000001fc0000 0x000000000007f000

def z210 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003e00fe02d81c 0x1ef800f803f80b60

def z211 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200018000000003 0x9a08000600000000

def z212 : W := mkw 0x2ee9ddbb830d22e6 0x04bba776ee0c348b 0xaaf1d9ff871d27f7 0xfaabc767fe1c749f

def z213 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e064719fc39d2 0x711438191c67f0e7

def z214 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xfffff800ffffc03d 0xffffffe003ffff00

def z215 : W := mkw 0x0e80d59ad70996a5 0x043a03566b5c265a 0x3a81d9b8e601c601 0x08ea0766e3980718

def z216 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0201c187871d27f6 0x500807061e1c749f

def z217 : W := mkw 0x00900008a1a34180 0xb002400022868d06 0x0000000001e001c0 0x0000000000078007

def z218 : W := mkw 0x0004020500042848 0x08001008140010a1 0x0000060700003802 0x000000181c0000e0

def z219 : W := mkw 0x0080809b810522c4 0x040202026e04148b 0x808001ff810127e7 0xaa020007fe04049f

def z220 : W := mkw 0x0080400083080000 0x00020100020c2000 0x8281c180871d2637 0xfa0a0706021c7498

def z221 : W := mkw 0x2fedffffd70db6ff 0x04bfb7ffff5c36db 0xffffffffff1fffff 0xfffffffffffc7fff

def z222 : W := mkw 0x3f7fbff67cd0003f 0xc0fdfeffd9f34000 0xffffffff78e0000b 0xfffffffffde38000

def z223 : W := mkw 0x0f0437455426bd79 0x283c10dd15509af5 0xbe003fc7fe03ffff 0x9ef800ff1ff80fff

def z224 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x440e2647181e39f2 0xd11038991c6078e7

def z225 : W := mkw 0x0080c093830c2244 0x040203024e0c3089 0x8281c187871c2616 0x7a0a07061e1c7098

def z226 : W := mkw 0x0f0637455c76bd79 0x683c18dd1571daf5 0xff0e3fc7ffffffff 0xfffc38ff1fffffff

def z227 : W := mkw 0x2124bff70026297e 0x288492ffdc0098a5 0x20003fff000239e3 0x808000fffc0008e7

def z228 : W := mkw 0x0130286020a24110 0xb004c0a180828904 0x0170000000e00000 0x0005c00000038000

def z229 : W := mkw 0x216faaf70876295e 0x6885beabdc21d8a5 0x41ffc07f01fc01c0 0x6107ff01fc07f007

def z230 : W := mkw 0x100240005e580001 0x4040090001796000 0x000000001e1c0010 0x0000000000787000

def z231 : W := mkw 0x2124aaf60000001e 0x008492abd8000000 0x0000007f00000000 0x00000001fc000000

def z232 : W := mkw 0x0080c09a83090284 0x040203026a0c240a 0x0281c1b886010601 0x080a0706e2180418

def z233 : W := mkw 0x0000809200000004 0x0000020248000000 0x0201c18700000002 0x500807061c000000

def z234 : W := mkw 0x1fdf7745fffebd79 0xe87f7ddd17fffaf5 0xffffffc7ffffffff 0xffffffff1fffffff

def z235 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff86012637 0xffbffffffe180498

def z236 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5bffc000e7fc0000 0x696fff00039ff000

def z237 : W := mkw 0x00900000a1800000 0x8002400002860000 0x01f0000001e00000 0x2007c00000078000

def z238 : W := mkw 0x2e691d2000000022 0x00b9a47480000000 0x2870180000000000 0x00a1c06000000000

def z239 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff860127e3 0x880a0707fe18049f

def z240 : W := mkw 0x0006020508542848 0x48001808142150a1 0xc40e2607181e383e 0xd71038981c6078e0

def z241 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xffffff80fffc001f 0xfffffffe03fff000

def z242 : W := mkw 0x0186e2df8b7f2bdc 0x6c061b8b7e2dfcaf 0xc58fe67f19fe39fe 0xf7163f99fc67f8e7

def z243 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc10e004701fc21f6 0xf30438011c07f087

def z244 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264718e239ea 0x851438991c6388e7

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000260000023822 0x80000098000008e0

def z246 : W := mkw 0x1f4f62455e7e2959 0x687d3d891579f8a5 0xc70fe6471ffe39fe 0xf71c3f991c7ff8e7

def z247 : W := mkw 0x2e4d97965400942f 0x00b9365e59500250 0xfe0fff87fe03fe3f 0xdff83ffe1ff80ff8

def z248 : W := mkw 0x216faaf70876295e 0x6885beabdc21d8a5 0xc5ffe67f19fe39fe 0xf717ff99fc67f8e7

def z249 : W := mkw 0x01b06868a3ab4190 0xb006c1a1a28ead06 0xbbf1f878e7ffc1fd 0xfeefc7e1e39fff07

def z250 : W := mkw 0x1e5b15007cd09421 0xc0796c5401f34250 0xff7e3f80fee3fe3f 0x9ffdf8fe03fb8ff8

def z251 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0xba81f9ffe71fe7ff 0xfeea07e7ff9c7f9f

def z252 : W := mkw 0x0e901500f5809421 0x803a405403d60250 0xbff03f80ffe3fe3f 0xbeffc0fe03ff8ff8

def z253 : W := mkw 0x21edeaff830d22de 0x0487b7abfe0c348b 0x41ffc07f011c01c0 0x6107ff01fc047007

def z254 : W := mkw 0x1edf4205ffdc2849 0xc87b7d0817ff70a1 0xdfffc607fffc381e 0x7f7fff181ffff0e0

def z255 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xefffffff0003fe23 0xffbffffffc000ff8

def z256 : W := mkw 0x1edb0000fdd00001 0xc07b6c0003f74000 0xddfe0000f9e0000c 0x2f77f80003e78000

def z257 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0xcfffc07f00000000 0x7f3fff01fc000000

def z258 : W := mkw 0x0120286000224110 0x300480a180008904 0x200038000002c000 0x008000e000000b00

def z259 : W := mkw 0x00900008a1814080 0x9002400022860502 0x10000000e001c000 0x0040000003800700

def z260 : W := mkw 0x0002000008500000 0x4000080000214000 0x0000000019fc001c 0x000000000067f000

def z261 : W := mkw 0x10904000f7880001 0x8042410003de2000 0x10000000e6000000 0x0040000003980000

def z262 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x0000264719fe39fe 0x800000991c67f8e7

def z263 : W := mkw 0x01362a6528f66958 0xf804d8a994a3d9a5 0xfd7e3e4779fef9fe 0xf7f5f8f91de7fbe7

def z264 : W := mkw 0x0000150000009420 0x0000005400000250 0x0000078000003e02 0x0000001e000000f8

def z265 : W := mkw 0x11fb6868abfb4190 0xf047eda1a2afed06 0x41ffc07801fc01c0 0x6107ff01e007f007

def z266 : W := mkw 0x1ecbc09bdf5d22c5 0x447b2f026f7d748b 0xc68fc1ff9f1d27f7 0xfb1a3f07fe7c749f

def z267 : W := mkw 0x0002000008720900 0x680008000021c824 0x0000000018e21808 0x0000000000638860

def z268 : W := mkw 0x1e4b40005e580001 0x40792d0001796000 0xc70fc0001ffc001c 0x771c3f00007ff000

def z269 : W := mkw 0x0f69286000000010 0x003da4a180000000 0xeffff87800000001 0xffbfffe1e0000000

def z270 : W := mkw 0x0000c093020c2244 0x040003024c083089 0x0001c007001c0000 0x400007001c007000

def z271 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc70e27c79fff3fff 0xff1c389f1e7ffcff

def z272 : W := mkw 0x0080400083080000 0x00020100020c2000 0x00000000871c0014 0x00000000021c7000

def z273 : W := mkw 0x0106a2d70876295c 0x68041a8b5c21d8a5 0xc78fe7ff19fe39ff 0xff1e3f9ffc67f8e7

def z274 : W := mkw 0x0080d59b830db6e4 0x040203566e0c36db 0xa281ffff871ffff7 0xfa8a07fffe1c7fff

def z275 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f807e02fe1a 0x14f800fe01f80bf8

def z276 : W := mkw 0x0000150000009420 0x0000005400000250 0x20003e000002d800 0x008000f800000b60

def z277 : W := mkw 0x2ffdbff6a180003e 0x80bff6ffda860000 0xffffffffe1e0000f 0xffffffffff878000

def z278 : W := mkw 0x200497960000002e 0x0080125e58000000 0x0000078700000002 0x0000001e1c000000

def z279 : W := mkw 0x00804009d70db6c1 0x04020100275c36db 0x10000000ff1ffffc 0x0040000003fc7fff

def z280 : W := mkw 0x2ffdbffef5a3d5bf 0xb0bff6fffbd68f56 0xffffffffffe3ffff 0xffffffffffff8fff

def z281 : W := mkw 0x1e4b40005e580001 0x40792d0001796000 0xde0fc000fe1c001c 0x5f783f0003f87000

def z282 : W := mkw 0x0e0015015404b461 0x00380054055012d1 0xbe003fc7ff1fffff 0xfef800ff1ffc7fff

def z283 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6f7fff8700000002 0x55bdfffe1c000000

def z284 : W := mkw 0x0106224408720918 0x680418891021c824 0xc50e260019fe181c 0x771438980067f860

def z285 : W := mkw 0x00b0c8bba38d62c4 0x9402c322ee8e358b 0xbaf1d9ffe71de7f7 0xfaebc767ff9c779f

def z286 : W := mkw 0x0eb01d28f581d4a1 0x903ac074a3d60752 0xbef03fb8fe03fe3f 0x9efbc0fee3f80ff8

def z287 : W := mkw 0x0000c093020c2244 0x040003024c083089 0x8281c1ff061c2613 0xfa0a0707fc187098

def z288 : W := mkw 0x1fdfe2dfffff2bdd 0xec7f7f8b7ffffcaf 0xdfffe7ffffff3fff 0xff7fff9ffffffcff

def z289 : W := mkw 0x2e6d9fb60000002e 0x00b9b67ed8000000 0x6effdfbf00000003 0x59bbff7efc000000

def z290 : W := mkw 0x0184e2df832f2bdc 0x2c06138b7e0cbcaf 0x8281e7ff871f3ff7 0xfa0a079ffe1c7cff

def z291 : W := mkw 0x0e00150054009421 0x0038005401500250 0x380018006000c000 0x00e0006001800300

def z292 : W := mkw 0x0120a8fb002763d4 0x340482a3ec009d8f 0x200039ff0003e7e3 0x808000e7fc000f9f

def z293 : W := mkw 0x0080000881010080 0x0002000022040402 0xb8803878e103c1ed 0xaee200e1e3840f07

def z294 : W := mkw 0x1fff6a6dffff69d9 0xf87ffda9b7fffda7 0xfffffe7ffffff9ff 0xfffffff9ffffffe7

def z295 : W := mkw 0x0120286000000010 0x000480a180000000 0x2000387800000001 0x808000e1e0000000

def z296 : W := mkw 0x0000000054009401 0x0000000001500250 0x100000007802d808 0x0040000001e00b60

def z297 : W := mkw 0x0104224500262958 0x28041089140098a5 0x80002647011e39f6 0xf20000991c0478e7

def z298 : W := mkw 0x2f6dbff70026297e 0x28bdb6ffdc0098a5 0xefffffff000239e3 0xffbffffffc0008e7

def z299 : W := mkw 0x00900000a1800000 0x8002400002860000 0xb9f03800e1e3c02d 0xaee7c0e003878f00

def z300 : W := mkw 0x0f86f7dfdf7fbffd 0x6c3e1bdf7f7dfeff 0xff8fffffffffffff 0xfffe3fffffffffff

def z301 : W := mkw 0x00900008a1a34180 0xb002400022868d06 0x90800078e1e3c1ed 0xaa420001e3878f07

def z302 : W := mkw 0x20209db200000026 0x00808276c8000000 0x200019b800000001 0x00800066e0000000

def z303 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0xcfffc00001fc0000 0x7f3fff000007f000

def z304 : W := mkw 0x0000809200000004 0x0000020248000000 0x0081c07f00000000 0x60020701fc000000

def z305 : W := mkw 0x0e00150054009421 0x0038005401500250 0x0400060018001800 0x0010001800600060

def z306 : W := mkw 0x1ffbe8fbffff63d5 0xf47fefa3effffd8f 0xfffff9ffffffe7ff 0xffffffe7ffffff9f

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x38001800e001c001 0x08e0006003800700

def z308 : W := mkw 0x0120286800234190 0x300480a1a0008d06 0xa100387801e3c1ed 0xa68400e1e0078f07

def z309 : W := mkw 0x0e49000000000000 0x0039240000000000 0x0af1c00000000000 0x082bc70000000000

def z310 : W := mkw 0x0000000100042040 0x0000000004001081 0x84002647191e39fe 0xf61000991c6478e7

def z311 : W := mkw 0x0000c09202080204 0x0400030248082008 0x0201c18006000600 0x0008070600180018

def z312 : W := mkw 0x2f7dbff620a2413e 0xb0bdf6ffd8828904 0xffffffff60e2c00b 0xfffffffffd838b00

def z313 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xfffffe00fffed81c 0x7ffffff803fffb60

def z314 : W := mkw 0x2e4dd797020c226e 0x04b9375e5c083089 0x460fc787061c2612 0x51183f1e1c187098

def z315 : W := mkw 0x0020082000000000 0x0000802080000000 0x28f0183800000001 0x08a3c060e0000000

def z316 : W := mkw 0x1f5f22447cf20919 0xe87d7c8911f3c824 0x5d7e260078e21808 0x0575f89801e38860

def z317 : W := mkw 0x0e00000054000001 0x0038000001500000 0x9e002600fe02383e 0x9e78009803f808e0

def z318 : W := mkw 0x0104224500262958 0x28041089140098a5 0x8100264701e239ee 0xa60400991c0788e7

def z319 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8081c07f011c21f6 0xf2020701fc047087

def z320 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x2af1ffff00000003 0x88abc7fffc000000

def z321 : W := mkw 0x3f7f3f647cd0003b 0xc0fdfcfd91f34000 0x7d7e3e0078e00008 0x05f5f8f801e38000

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000080010025 0x8a00000002000400

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000018000012623 0x8000000600000498

def z324 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc3ffc00087fc0014 0x7b0fff00021ff000

def z325 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6d7e3fff00000003 0x85b5f8fffc000000

def z326 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5d7e0000fffc001c 0x0575f80003fff000

def z327 : W := mkw 0x0e00150054009421 0x0038005401500250 0x9e000780fe003e1e 0x1e78001e03f800f8

def z328 : W := mkw 0x00804001830c2040 0x00020100060c3081 0x8281c047871c21f6 0xfa0a07011e1c7087

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200018006002612 0x1008000600180098

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200000086000014 0x1a08000002180000

def z331 : W := mkw 0x2fefffff8b7f2bfe 0x6cbfbffffe2dfcaf 0xefffffff9fff3fff 0xffbffffffe7ffcff

def z332 : W := mkw 0x0f0637445c729d39 0x683c18dd1171ca74 0xff0e3f80fee3fe3f 0x9ffc38fe03fb8ff8

def z333 : W := mkw 0x10924000ffd80001 0xc042490003ff6000 0x9281c000fffc001c 0x7a4a070003fff000

def z334 : W := mkw 0x0ec9c09b830d22c4 0x043b27026e0c348b 0xcfffc1ff871d27f7 0xff3fff07fe1c749f

def z335 : W := mkw 0x0000809200000004 0x0000020248000000 0x0281c1b800000001 0x080a0706e0000000

def z336 : W := mkw 0x1ed94000f7880001 0x807b650003de2000 0x9ef1c000fe00001c 0x1e7bc70003f80000

def z337 : W := mkw 0x1f7b28607cf24111 0xf07deca181f3c904 0x7d7e380078e2c008 0x05f5f8e001e38b00

def z338 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f80fe03de09 0x0cf800fe03f80f78

def z339 : W := mkw 0x1f5f22457cf62959 0xe87d7c8915f3d8a5 0xdd7e264779fe39fe 0xf775f8991de7f8e7

def z340 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff1802383f 0xffbffffffc6008e0

def z341 : W := mkw 0x2ffdbffea1a341be 0xb0bff6fffa868d06 0xefffffff01e001c3 0xffbffffffc078007

def z342 : W := mkw 0x1fdf6245fffe2959 0xe87f7d8917fff8a5 0xdfffc047fffc01dc 0x7f7fff011ffff007

def z343 : W := mkw 0x0080400083080000 0x00020100020c2000 0x0281c00086000000 0x080a070002180000

def z344 : W := mkw 0x0010000020800000 0x8000400000820000 0x1970000060e00008 0x0465c00001838000

def z345 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x38f03878e003c1e1 0x88e3c0e1e3800f07

def z346 : W := mkw 0x0196224da9f769d8 0xf806588936a7dda7 0xd50e2647f9fff9fe 0xf75438991fe7ffe7

def z347 : W := mkw 0x11966245fffe2959 0xe846598917fff8a5 0xd50e2647fffe39fe 0xf75438991ffff8e7

def z348 : W := mkw 0x2e699db200000026 0x00b9a676c8000000 0xaef1ffb800000003 0x9ebbc7fee0000000

def z349 : W := mkw 0x2e4f97970854286e 0x48b93e5e5c2150a1 0x460fc787181c3812 0x51183f1e1c6070e0

def z350 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffd980fffdc61d 0x7fffff6603fff718

def z351 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003f80e601c603 0x9ef800fe03980718

def z352 : W := mkw 0x1e5b00007cd00001 0xc0796c0001f34000 0xdf7e0000fee0001c 0x1f7df80003fb8000

def z353 : W := mkw 0x0e00000000000000 0x0038000000000000 0x8e00000000000000 0x1e38000000000000

def z354 : W := mkw 0x00804009830d22c0 0x04020100260c348b 0x00000000011c01c0 0x0000000000047007

def z355 : W := mkw 0x1e4f42055e5c2849 0x48793d08157970a1 0x460fc6071e1c3812 0x51183f181c7870e0

def z356 : W := mkw 0x0120286000000010 0x000480a180000000 0x01f0007800000000 0x2007c001e0000000

def z357 : W := mkw 0x0e80d59b830d22e4 0x043a03566e0c348b 0xae81ffff871d27f7 0xfeba07fffe1c749f

def z358 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffffe601c603 0xffffffffff980718

def z359 : W := mkw 0x01262a6508762958 0x680498a99421d8a5 0xedfe3e7f19fe39ff 0xffb7f8f9fc67f8e7

def z360 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x000001ff871d27f7 0x80000007fe1c749f

def z361 : W := mkw 0x0002000008500000 0x4000080000214000 0x450e000018e00008 0x0514380000638000

def z362 : W := mkw 0x0000959b0005b6e4 0x040002566c0016db 0x20003fff0003ffe3 0x808000fffc000fff

def z363 : W := mkw 0x01b02860a1a24110 0xb006c0a182868904 0xb9f03800e1e2c00c 0x2ee7c0e003878b00

def z364 : W := mkw 0x01a0e8fb830d22d4 0x040683a3ee0c348b 0xabf1f9ff871d27f7 0xfeafc7e7fe1c749f

def z365 : W := mkw 0x0120286800234190 0x300480a1a0008d06 0xb8003878e003c1ed 0x8ee000e1e3800f07

def z366 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3c003e00fe03fe3c 0x04f000f803f80ff8

def z367 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8681e7ff9f1f3fff 0xfe1a079ffe7c7cff

def z368 : W := mkw 0x0104224400000018 0x0004108910000000 0x410e004700000000 0x610438011c000000

def z369 : W := mkw 0x0eb01d28f581d4a1 0x903ac074a3d60752 0x3af019b8e601c601 0x08ebc066e3980718

def z370 : W := mkw 0x0000000054000001 0x0000000001500000 0x10000000fe00001c 0x0040000003f80000

def z371 : W := mkw 0x1e5b15007cd09421 0xc0796c5401f34250 0x7d7e3e0078e2d808 0x05f5f8f801e38b60

def z372 : W := mkw 0x0002000008500000 0x4000080000214000 0x440e0000181c0010 0x5110380000607000

def z373 : W := mkw 0x01b02868a1814090 0x9006c0a1a2860502 0xb9f03878e001c001 0xaee7c0e1e3800700

def z374 : W := mkw 0x01b0e8fba3af63d4 0xb406c3a3ee8ebd8f 0x01f1c07f01fc01c0 0x6007c701fc07f007

def z375 : W := mkw 0x0e00959254009425 0x0038025649500250 0xbe81fffffe03fe3f 0xfefa07fffff80ff8

def z376 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff871d07c1 0x680a0707fe1c741f

def z377 : W := mkw 0x00804009830d22c0 0x04020100260c348b 0x8281c000871d27f4 0x7a0a0700021c749f

def z378 : W := mkw 0x3ffffff7fffe297f 0xe8ffffffdffff8a5 0xfffffffffffe39ff 0xfffffffffffff8e7

def z379 : W := mkw 0x0000150000009420 0x0000005400000250 0xa4003f801803fe3f 0x969000fe00600ff8

def z380 : W := mkw 0x00900000a1800000 0x8002400002860000 0x18f00000e0000000 0x0863c00003800000

def z381 : W := mkw 0x0010000020a24100 0xb000400000828904 0x1000000060e2c008 0x0040000001838b00

def z382 : W := mkw 0x2ee9ddba830902a6 0x04bba776ea0c240a 0x2af1d9b886010601 0x08abc766e2180418

def z383 : W := mkw 0x1e4b40005e580001 0x40792d0001796000 0xcfffc0001e1c0010 0x7f3fff0000787000

def z384 : W := mkw 0x0f06374508762978 0x683c18dd1421d8a5 0xef0e3fc719fe39ff 0xffbc38ff1c67f8e7

def z385 : W := mkw 0x0080c09283080004 0x000203024a0c2000 0x8281c1ff871c0017 0xfa0a0707fe1c7000

def z386 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264719fe19c8 0x651438991c67f867

def z387 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x81f0007881e101e5 0xaa07c001e2078407

def z388 : W := mkw 0x0e0215005c509421 0x4038085401714250 0xff0e3f80fffffe3f 0xfffc38fe03fffff8

def z389 : W := mkw 0x0f4f224508762958 0x683d3c891421d8a5 0xcfffe64719fe39fe 0xff3fff991c67f8e7

def z390 : W := mkw 0x0000000100042040 0x0000000004001081 0x00000000011c21f4 0x0000000000047087

def z391 : W := mkw 0x3ef9ddb2f7880027 0x80fbe776cbde2000 0x3af1d9b8e6000001 0x08ebc766e3980000

def z392 : W := mkw 0x0106e2d70a7e2b5c 0x6c041b8b5c29f8ad 0xc70fe7c71ffe3ffe 0xf71c3f9f1c7ff8ff

def z393 : W := mkw 0x3f6ffff65e58003f 0x40fdbfffd9796000 0xefffffff1e1c0013 0xffbffffffc787000

def z394 : W := mkw 0x01b6eaffabff6bdc 0xfc06dbabfeaffdaf 0xffffffffffffffff 0xffffffffffffffff

def z395 : W := mkw 0x2f6d3f645400943b 0x00bdb4fd91500250 0xff7e3f80fe03fe3f 0x9ffdf8fe03f80ff8

def z396 : W := mkw 0x0e00150000000020 0x0038005400000000 0xbe003f80e003c02f 0x9ef800fe03800f00

def z397 : W := mkw 0x1edbc09affd90285 0xc47b6f026bff640a 0xdfffc1b8fffd061d 0x7f7fff06e3fff418

def z398 : W := mkw 0x1fdf6244fffa0919 0xe87f7d8913ffe824 0xdfffe600fffe181c 0x7f7fff9803fff860

def z399 : W := mkw 0x0006020508542848 0x48001808142150a1 0x400e0007001c0000 0x410038001c007000

def z400 : W := mkw 0x0000000100262940 0x28000000040098a5 0x00000000000239e0 0x00000000000008e7

def z401 : W := mkw 0x2f7d3f6420a2413a 0xb0bdf4fd90828904 0x7d7e3e0060e2c008 0x05f5f8f801838b00

def z402 : W := mkw 0x01b02860a1800010 0x8006c0a182860000 0xb9f03878e1e0000d 0xaee7c0e1e3878000

def z403 : W := mkw 0x0e00150000009420 0x0038005400000250 0xae003f800003fe23 0x9eb800fe00000ff8

def z404 : W := mkw 0x1efb4828ffd94081 0xd07bed20a3ff6502 0xffffd838fffdc01d 0x7fffff60e3fff700

def z405 : W := mkw 0x0e00000054000001 0x0038000001500000 0x9e000000fe00001c 0x1e78000003f80000

def z406 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5dffc00079fc0008 0x6577ff0001e7f000

def z407 : W := mkw 0x2124bff60000003e 0x008492ffd8000000 0xa9f03fff00000003 0xaea7c0fffc000000

def z408 : W := mkw 0x31ffeaf6abd8001e 0xc0c7ffabdaaf6000 0x41ffc07f01fc0000 0x6107ff01fc07f000

def z409 : W := mkw 0x0000809300042244 0x040002024c001089 0x0000018700002602 0x000000061c000098

def z410 : W := mkw 0x00900008a1810080 0x8002400022860402 0x99f00078e1e101ed 0xae67c001e3878407

def z411 : W := mkw 0x01a0286881234190 0x300680a1a2048d06 0xa08038788103c1e5 0xaa8200e1e2040f07

def z412 : W := mkw 0x1ed94000f7880001 0x807b650003de2000 0xdfffc000e6000000 0x7f7fff0003980000

def z413 : W := mkw 0x1e925500ffd89421 0xc07a495403ff6250 0xbe003f80fffffe3f 0x9ef800fe03fffff8

def z414 : W := mkw 0x21b4bffea1a341be 0xb086d2fffa868d06 0xb9f03fffe1e3c1ef 0xaee7c0ffff878f07

def z415 : W := mkw 0x01b22869a9f769d0 0xf806c8a1a6a7dda7 0xb9f03878f9fff9fd 0xaee7c0e1e3e7ffe7

def z416 : W := mkw 0x0082c09b8b7f2bc4 0x6c020b026e2dfcaf 0x8281c1ff9fff3fff 0xfa0a0707fe7ffcff

def z417 : W := mkw 0x0000809b000522c4 0x040002026c00148b 0x820001ff860127f7 0x9a080007fe18049f

def z418 : W := mkw 0x2f6dfff7020c227e 0x04bdb7ffdc083089 0xefffffff061c2613 0xffbffffffc187098

def z419 : W := mkw 0x1ffb6860fffa4111 0xf07feda183ffe904 0xfffff800fffec01c 0x7fffffe003fffb00

def z420 : W := mkw 0x0e00150000000020 0x0038005400000000 0x2c003e0000000000 0x04b000f800000000

def z421 : W := mkw 0x01b22868a9f34190 0xf006c8a1a2a7cd06 0xfdfe3878f9ffc1fd 0xfff7f8e1e3e7ff07

def z422 : W := mkw 0x0f303d6074a2d531 0xb03cc0f581d28b54 0xbf703f80fee3fe3f 0x9efdc0fe03fb8ff8

def z423 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xffffffffe003c02f 0xffffffffff800f00

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000e003c02c 0x0040000003800f00

def z425 : W := mkw 0x2f6d3f640000003a 0x00bdb4fd90000000 0xef7e3f8000000003 0x9fbdf8fe00000000

def z426 : W := mkw 0x2f4fb7d70876297e 0x68bd3edf5c21d8a5 0xc70fe7c719fe39fe 0xf71c3f9f1c67f8e7

def z427 : W := mkw 0x01b0a8faa1a34194 0xb006c2a3ea868d06 0xbbf1f9ffe1e3c1ef 0xfeefc7e7ff878f07

def z428 : W := mkw 0x0100204100262150 0x2004008104009885 0x8100204701fe21fe 0xf60400811c07f887

def z429 : W := mkw 0x1ef94828f7894081 0x907be520a3de2502 0x3af1d838e601c001 0x08ebc760e3980700

def z430 : W := mkw 0x0002000108762940 0x680008000421d8a5 0xc50e000019fe39fc 0x771438000067f8e7

def z431 : W := mkw 0x0002000008500000 0x4000080000214000 0x410e000001fc0000 0x610438000007f000

def z432 : W := mkw 0x0f203d685423d5b1 0x303c80f5a1508f56 0xbe003ff8fe03ffff 0x9ef800ffe3f80fff

def z433 : W := mkw 0x1edbc092ffd80005 0xc07b6f024bff6000 0xdfffc1fffffc001f 0xff7fff07fffff000

def z434 : W := mkw 0x1edb4009ffdd22c1 0xc47b6d0027ff748b 0xdfffc000fffd27fc 0x7f7fff0003fff49f

def z435 : W := mkw 0x0002000108762940 0x680008000421d8a5 0x8000004719fe39fe 0xf20000011c67f8e7

def z436 : W := mkw 0x1fdb6040fffa0111 0xe07f6d8103ffe804 0xdfffe040fffe01fc 0xff7fff8103fff807

def z437 : W := mkw 0x0086c29f8b5d2acc 0x4c021b0a7e2d74ab 0xc68fc7ff9f1d3ff7 0xfb1a3f1ffe7c74ff

def z438 : W := mkw 0x0080400883090280 0x04020100220c240a 0x0000000086010600 0x0000000002180418

def z439 : W := mkw 0x0186224d897729d8 0x680618893625dca7 0xc58e267f99ff39ff 0xff163899fe67fce7

def z440 : W := mkw 0x1ed9c09af7890285 0x847b67026bde240a 0x1af1c1b8e6010601 0x086bc706e3980418

def z441 : W := mkw 0x0000000054009401 0x0000000001500250 0xb8003800fe03fe3d 0x8ee000e003f80ff8

def z442 : W := mkw 0x2fedfff68308003e 0x00bfb7ffda0c2000 0xefffffff871c0017 0xffbffffffe1c7000

def z443 : W := mkw 0x0006020508542848 0x48001808142150a1 0xc50e060719fc381e 0x771438181c67f0e0

def z444 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xa9f0387801e001c1 0xaea7c0e1e0078007

def z445 : W := mkw 0x0e801508d50194a1 0x003a005423540652 0xbe803ff8ff03ffff 0xbefa00ffe3fc0fff

def z446 : W := mkw 0x2fedbffe810100be 0x00bfb6fffa040402 0xefffffff810101e7 0xffbffffffe040407

def z447 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc3ffc1ff00000003 0xfb0fff07fc000000

def z448 : W := mkw 0x3edfd796ffd8002f 0xc0fb7f5e5bff6000 0xdfffc787fffc001e 0x7f7fff1e1ffff000

def z449 : W := mkw 0x1e59000074800001 0x8079640001d20000 0x1870000060000000 0x0061c00001800000

def z450 : W := mkw 0x01902040a1a20110 0xa006408102868804 0x99f02040e1e201ec 0xae67c08103878807

def z451 : W := mkw 0x0e0215015c76bd61 0x683808540571daf5 0xbe003f80ffffffff 0x9ef800fe03ffffff

def z452 : W := mkw 0x1e5b00007cd00001 0xc0796c0001f34000 0xdd7e000079fc001c 0x7775f80001e7f000

def z453 : W := mkw 0x1edbc093ffdc2245 0xc47b6f024fff7089 0xdfffc187fffc261e 0x7f7fff061ffff098

def z454 : W := mkw 0x0fb63f6dfdf7fdf9 0xf83ed8fdb7f7dff7 0xfffe3fffffffffff 0xfffff8ffffffffff

def z455 : W := mkw 0x1e49400056080001 0x0079250001582000 0x0201c00006000000 0x0008070000180000

def z456 : W := mkw 0x0104224500042058 0x0004108914001081 0xc50e2647011c21f6 0xf71438991c047087

def z457 : W := mkw 0x3fff7f64ffd8003b 0xc0fffdfd93ff6000 0xfffffe00fffc001c 0x7ffffff803fff000

def z458 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5effc000fe1c0010 0x597bff0003f87000

def z459 : W := mkw 0x01203d680023d5b0 0x300480f5a0008f56 0x20003ff80003ffe3 0x808000ffe0000fff

def z460 : W := mkw 0x2f6dbff70004207e 0x00bdb6ffdc001081 0xefffffff011c21f7 0xffbffffffc047087

def z461 : W := mkw 0x0f04374400000038 0x003c10dd10000000 0xef0e3fc700000003 0xffbc38ff1c000000

def z462 : W := mkw 0x3ffdfff6f788003f 0x80fff7ffdbde2000 0xffffffffe6000003 0xffffffffff980000

def z463 : W := mkw 0x1edbd59bffddb6e5 0xc47b6f566fff76db 0xffffffffffffffff 0xffffffffffffffff

def z464 : W := mkw 0x0104224500262958 0x28041089140098a5 0x84002647180239fe 0x961000991c6008e7

def z465 : W := mkw 0x0f4d224400000018 0x003d348910000000 0xcfffe64700000002 0xff3fff991c000000

def z466 : W := mkw 0x10924008fffb4181 0xf042490023ffed06 0x10000000ffffc1fc 0x0040000003ffff07

def z467 : W := mkw 0x21a4ffff830d22fe 0x048693fffe0c348b 0xa281ffff871d27f7 0xfa8a07fffe1c749f

def z468 : W := mkw 0x0130286020a24110 0xb004c0a180828904 0xb9703800e0e3c02d 0x8ee5c0e003838f00

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x98000000e000000c 0x0e60000003800000

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x860027809e033e3f 0x9e18009e02780cf8

def z471 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x21f0387801e3c1e1 0xa087c0e1e0078f07

def z472 : W := mkw 0x0000000100042040 0x0000000004001081 0x00000047011c01c0 0x600000011c047007

def z473 : W := mkw 0x0100204000220110 0x2004008100008804 0x0100004001e001c0 0x2004000100078007

def z474 : W := mkw 0x0002000108762940 0x680008000421d8a5 0x8400260019fe39fe 0x961000980067f8e7

def z475 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbbf039f8e7e3e7ff 0xbeefc0e7e39f8f9f

def z476 : W := mkw 0x0e804000d7080001 0x003a0100035c2000 0x9e81c000ff1c001c 0x7e7a070003fc7000

def z477 : W := mkw 0x2f6fbff70854287e 0x48bdbeffdc2150a1 0xefffffff181c3813 0xffbffffffc6070e0

def z478 : W := mkw 0x1ffb7d68fffbd5b1 0xf07fedf5a3ffef56 0xfffffff8ffffffff 0xffffffffe3ffffff

def z479 : W := mkw 0x0104224500262958 0x28041089140098a5 0xc50e2647000239e2 0xf71438991c0008e7

def z480 : W := mkw 0x1edb4001ffdc2041 0xc07b6d0007ff7081 0xdfffc047fffc21fe 0xff7fff011ffff087

def z481 : W := mkw 0x0080c09a83090284 0x040203026a0c240a 0x8281c1b886012637 0x9a0a0706e2180498

def z482 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x81f0207801e201ec 0xa607c081e0078807

def z483 : W := mkw 0x00900008f5a3d581 0xb002400023d68f56 0x10000000ffe3fffc 0x0040000003ff8fff

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x380038006002c008 0x04e000e001800b00

def z485 : W := mkw 0x1ed94000f7880001 0x807b650003de2000 0x9af1c000e71c0014 0x7a6bc700039c7000

def z486 : W := mkw 0x0106224408720918 0x680418891021c824 0xc50e264718e2180a 0xf71438991c638860

def z487 : W := mkw 0x2f6dbffe002341be 0x30bdb6fff8008d06 0xefffffff0003c1e3 0xffbffffffc000f07

def z488 : W := mkw 0x0180e0db832f23d4 0x240603836e0cbc8f 0x8381e1ff87ff27ff 0xfe0e0787fe1ffc9f

def z489 : W := mkw 0x0000c093020c2244 0x040003024c083089 0x8201c1c7071c27f6 0xf20807071c1c709f

def z490 : W := mkw 0x0104224400220118 0x2004108910008804 0xc50e264701e201ee 0xf71438991c078807

def z491 : W := mkw 0x21243f640000003a 0x008490fd90000000 0x20003e0000000000 0x008000f800000000

def z492 : W := mkw 0x101200007cd00001 0xc040480001f34000 0x1000000078e00008 0x0040000001e38000

def z493 : W := mkw 0x01362a6428f24918 0xf804d8a990a3c924 0x7d7e3e0078e2d808 0x05f5f8f801e38b60

def z494 : W := mkw 0x0e00000054000001 0x0038000001500000 0x060000001e000010 0x1018000000780000

def z495 : W := mkw 0x0e00000054009401 0x0038000001500250 0x9e000000fe03fe3c 0x1e78000003f80ff8

def z496 : W := mkw 0x0104224400000018 0x0004108910000000 0x0000264700000002 0x800000991c000000

def z497 : W := mkw 0x0f203d6000000030 0x003c80f580000000 0xaff03ff800000003 0xbebfc0ffe0000000

def z498 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc10e204701fe01ec 0xe70438811c07f807

def z499 : W := mkw 0x0000000054009401 0x0000000001500250 0x000000001e003e10 0x00000000007800f8

def z500 : W := mkw 0x010637450876bd78 0x680418dd1421daf5 0xe50e3fc719ffffff 0xf79438ff1c67ffff

def z501 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0x61ffffff00000003 0xe187fffffc000000

def z502 : W := mkw 0x0e00d593560cb665 0x043803564d5832d9 0x0601c7871e1c3e12 0x5018071e1c7870f8

def z503 : W := mkw 0x0f0637455c76bd79 0x683c18dd1571daf5 0xfd0e3e4779fef9fe 0xf7f438f91de7fbe7

def z504 : W := mkw 0x0ff92868a1a34190 0xb03fe4a1a2868d06 0xfffff878e1e3c1ed 0xffffffe1e3878f07

def z505 : W := mkw 0x0006020408500808 0x4800180810214020 0x440e060018001800 0x0110381800600060

def z506 : W := mkw 0x2f4db7d60000003e 0x00bd36df58000000 0xc70fe7c700000002 0xf71c3f9f1c000000

def z507 : W := mkw 0x10924000ffd80001 0xc042490003ff6000 0x99f00000fffc001c 0x2e67c00003fff000

def z508 : W := mkw 0x3fffffffffdd22ff 0xc4ffffffffff748b 0xfffffffffffd27ff 0xfffffffffffff49f

def z509 : W := mkw 0x00b00828a1a34180 0xb002c020a2868d06 0x38f01838e1e3c1ed 0x08e3c060e3878f07

def z510 : W := mkw 0x0000809300042044 0x000002024c001081 0x8281c1ff011c21f7 0xfa0a0707fc047087

def z511 : W := mkw 0x2e699db254009427 0x00b9a676c9500250 0xbef1ffb8fe03fe3f 0x9efbc7fee3f80ff8

def z512 : W := mkw 0x2e4d97960000002e 0x00b9365e58000000 0xcfffc78700000002 0x7f3fff1e1c000000

def z513 : W := mkw 0x0104224400000018 0x0004108910000000 0xc50e26471802383e 0xf71438991c6008e0

def z514 : W := mkw 0x0000000100042040 0x0000000004001081 0x00000047000021e2 0x800000011c000087

def z515 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5fffc000fee00008 0x0d7fff0003fb8000

def z516 : W := mkw 0x0e00d593560cb665 0x043803564d5832d9 0xbe01ff87fe1ffe3f 0xdef807fe1ff87ff8

def z517 : W := mkw 0x010437450026bd78 0x280410dd14009af5 0x20003fc70003ffe3 0x808000ff1c000fff

def z518 : W := mkw 0x3ffffff6abd8003e 0xc0ffffffdaaf6000 0xefffffff01fc0003 0xffbffffffc07f000

def z519 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffff7802d80b 0xfffffffffde00b60

def z520 : W := mkw 0x0e00150000000020 0x0038005400000000 0xae003f8086012637 0x9eb800fe02180498

def z521 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff011c01c3 0xfa0a0707fc047007

def z522 : W := mkw 0x1ff96868f7ab4191 0xb07fe5a1a3dead06 0xbbf1f878e7e3c1ed 0xaeefc7e1e39f8f07

def z523 : W := mkw 0x0000809b000522c4 0x040002026c00148b 0x0000007f000001c0 0x00000001fc000007

def z524 : W := mkw 0x2e699db200000026 0x00b9a676c8000000 0xaaf1d9ff00000003 0xfaabc767fc000000

def z525 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003f807802d80b 0x9ef800fe01e00b60

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x200038000003c021 0x808000e000000f00

def z527 : W := mkw 0x11df6245abfe2958 0xe8477d8916aff8a5 0xc5ffe64719fe39fe 0xf717ff991c67f8e7

def z528 : W := mkw 0x2e699db200000026 0x00b9a676c8000000 0xefffd9b800000001 0x7fbfff66e0000000

def z529 : W := mkw 0x0080000881010080 0x0002000022040402 0x00800078010001c0 0x20020001e0040007

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x89f0000000000000 0x2e27c00000000000

def z531 : W := mkw 0x0002000108542040 0x4000080004215081 0xc50e004719fc21fe 0xf71438011c67f087

def z532 : W := mkw 0x2ffd3f6ca1a341ba 0xb0bff4fdb2868d06 0xfdfe3e78e1e3c1ed 0xaff7f8f9e3878f07

def z533 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e260718fe381a 0x551438981c63f8e0

def z534 : W := mkw 0x01b62a6da9f769d8 0xf806d8a9b6a7dda7 0x41fe007f01fc01c0 0x6107f801fc07f007

def z535 : W := mkw 0x0000150000009420 0x0000005400000250 0x200019800001c601 0x0080006600000718

def z536 : W := mkw 0x0e900000f5800001 0x803a400003d60000 0x9ff00000ffe0001c 0x3e7fc00003ff8000

def z537 : W := mkw 0x0e00150054009421 0x0038005401500250 0x26003f801e03fe33 0x909800fe00780ff8

def z538 : W := mkw 0x00920000a9d00000 0xc002480002a74000 0xddfe0000f9fc001c 0x7f77f80003e7f000

def z539 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xfd0e3e47f9fff9ff 0xfff438f91fe7ffe7

def z540 : W := mkw 0x0186e2df8b7f2bdc 0x6c061b8b7e2dfcaf 0xc38fc1ff87fd27f7 0xfb0e3f07fe1ff49f

def z541 : W := mkw 0x204d82960000000e 0x0081360a58000000 0x400fc00700000000 0x41003f001c000000

def z542 : W := mkw 0x01262a6d087769d8 0x780498a9b421dda7 0xe50e3e7f19fff9ff 0xf79438f9fc67ffe7

def z543 : W := mkw 0x0000000000009400 0x0000000000000250 0x000000000003fe20 0x0000000000000ff8

def z544 : W := mkw 0x1ecb4000df580001 0x407b2d00037d6000 0xc68fc0009f1c0014 0x7b1a3f00027c7000

def z545 : W := mkw 0x0fb03d68f5a3d5b1 0xb03ec0f5a3d68f56 0xbbf039f8e7e3c7ed 0xaeefc0e7e39f8f1f

def z546 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x30003878e1e3c1ed 0x80c000e1e3878f07

def z547 : W := mkw 0x0e0617055c54bc69 0x4838185c157152f1 0x460e07871e1c3e12 0x5118381e1c7870f8

def z548 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbc003e007802f83e 0x96f000f801e00be0

def z549 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3a001980fe03fe3d 0x08e8006603f80ff8

def z550 : W := mkw 0x0e80d59bd70db6e5 0x043a03566f5c36db 0x8681c7ff9f1d3ff7 0xfa1a071ffe7c74ff

def z551 : W := mkw 0x0106a2df08772bdc 0x6c041a8b7c21dcaf 0xc50e27ff19ff3fff 0xf714389ffc67fcff

def z552 : W := mkw 0x00000009000522c0 0x040000002400148b 0x00000000000127e0 0x000000000000049f

def z553 : W := mkw 0x104b40000a580000 0x40412d0000296000 0x400fc000001c0000 0x41003f0000007000

def z554 : W := mkw 0x2124bfff000522fe 0x048492fffc00148b 0x20003fff000127e3 0x808000fffc00049f

def z555 : W := mkw 0x0186624d8b7f2bd8 0x6c061989362dfcaf 0xc50e26479fff3ffe 0xf71438991e7ffcff

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800380000000001 0x8ea000e000000000

def z557 : W := mkw 0x00900000a1800000 0x8002400002860000 0x10000000e1e0000c 0x0040000003878000

def z558 : W := mkw 0x3ffffffefffb41bf 0xf0fffffffbffed06 0xffffffffffffc1ff 0xffffffffffffff07

def z559 : W := mkw 0x2f24bff65400943f 0x00bc92ffd9500250 0xbe003ffffe03fe3f 0x9ef800fffff80ff8

def z560 : W := mkw 0x0000809200000004 0x0000020248000000 0x000001ff00000003 0x80000007fc000000

def z561 : W := mkw 0x0120286800234190 0x300480a1a0008d06 0x00000078000001c0 0x00000001e0000007

def z562 : W := mkw 0x0e00150054009421 0x0038005401500250 0xba001980e601e637 0x9ae8006603980798

def z563 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264701fc01c2 0xf71438991c07f007

def z564 : W := mkw 0x01b62a6ca9f34998 0xf806d8a9b2a7cd26 0xfdfe3e78f9e3d9ed 0xaff7f8f9e3e78f67

def z565 : W := mkw 0x0082c09b8b5d22c4 0x44020b026e2d748b 0xc78fc1ff9ffd27ff 0xff1e3f07fe7ff49f

def z566 : W := mkw 0x0e805509d70db6e1 0x043a0154275c36db 0xbe003f80ff1fffff 0x9ef800fe03fc7fff

def z567 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x1af1c000fffc001c 0x086bc70003fff000

def z568 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f03838e0e3c009 0x0ce7c0e0e3838f00

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x8281c00000000000 0x7a0a070000000000

def z570 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f01878e1e1c1c1 0x28e7c061e3878707

def z571 : W := mkw 0x00900008a1a34180 0xb002400022868d06 0xb8003800e1e3c1ed 0x8ee000e003878f07

def z572 : W := mkw 0x2f6fbff60872093e 0x68bdbeffd821c824 0xefffffff18e2180b 0xffbffffffc638860

def z573 : W := mkw 0x0e00150054009421 0x0038005401500250 0x860007809e013e37 0x9a18001e027804f8

def z574 : W := mkw 0x0f00354054229531 0x203c00d501508a54 0xbf003fc0ffe3ffff 0xbefc00ff03ff8fff

def z575 : W := mkw 0x0e00150054009421 0x0038005401500250 0x0200018006000600 0x0008000600180018

def z576 : W := mkw 0x10924000ffd89401 0xc042490003ff6250 0x10000000fffffe3c 0x0040000003fffff8

def z577 : W := mkw 0x2ffdffffa3af63fe 0xb4bff7fffe8ebd8f 0xffffffffe7ffe7ff 0xffffffffff9fff9f

def z578 : W := mkw 0x2ecdd79f830d22ee 0x04bb375e7e0c348b 0xc68fc7ff871d27f7 0xfb1a3f1ffe1c749f

def z579 : W := mkw 0x2f24bff60000003e 0x00bc92ffd8000000 0xae003fff00000003 0x9eb800fffc000000

def z580 : W := mkw 0x2fedfffe830902be 0x04bfb7fffa0c240a 0xefffffff86010603 0xffbffffffe180418

def z581 : W := mkw 0x01242a6d002769d8 0x380490a9b4009da7 0x20003e7f0003f9e3 0x808000f9fc000fe7

def z582 : W := mkw 0x008240098b7f2bc0 0x6c020900262dfcaf 0x000000009fff3ffc 0x00000000027ffcff

def z583 : W := mkw 0x10dbc09babdd22c4 0xc4436f026eaf748b 0x41ffc07f01fc01c0 0x6107ff01fc07f007

def z584 : W := mkw 0x0e49000000000000 0x0039240000000000 0x460fc00000000000 0x51183f0000000000

def z585 : W := mkw 0x0130286020a24110 0xb004c0a180828904 0xb9f0387860e2c009 0xaee7c0e1e1838b00

def z586 : W := mkw 0x0000c093020c2244 0x040003024c083089 0x8201c187861d2637 0xda0807061e187498

def z587 : W := mkw 0x1e4b55005e589421 0x40792d5401796250 0x460fc7801e1c3e12 0x51183f1e007870f8

def z588 : W := mkw 0x3e4fd7965e58002f 0x40f93f5e59796000 0x460fc7871e1c0012 0x51183f1e1c787000

def z589 : W := mkw 0x00b00828a1814080 0x9002c020a2860502 0xb8f01878e101c1e5 0xaae3c061e3840707

def z590 : W := mkw 0x0106224408720918 0x680418891021c824 0x410e000000e00000 0x0104380000038000

def z591 : W := mkw 0x0000150000009420 0x0000005400000250 0xa2003f808603fe37 0x9a8800fe02180ff8

def z592 : W := mkw 0x1e924000ffd80001 0xc07a490003ff6000 0x9e000000fffc001c 0x1e78000003fff000

def z593 : W := mkw 0x1ffb2868fdf34191 0xf07feca1a3f7cd06 0xfdfe3878f9e3c1ed 0xaff7f8e1e3e78f07

def z594 : W := mkw 0x000200015c76bd41 0x680008000571daf5 0x10000000fffffffc 0x0040000003ffffff

def z595 : W := mkw 0x0e00150000000020 0x0038005400000000 0x2a00198000000001 0x08a8006600000000

def z596 : W := mkw 0x01b02869a1a761d0 0xb006c0a1a6869d87 0xb9f0387fe1ffe1ff 0xfee7c0e1ff87ff87

def z597 : W := mkw 0x2f6dbfff000522fe 0x04bdb6fffc00148b 0xefffffff000127e3 0xffbffffffc00049f

def z598 : W := mkw 0x2ff9bdfaa1a341b6 0xb0bfe6f7ea868d06 0xbbf1f9f8e1e3c1ed 0xaeefc7e7e3878f07

def z599 : W := mkw 0x0ec9400083080000 0x003b2500020c2000 0xcfffc000871c0014 0x7f3fff00021c7000

def z600 : W := mkw 0x00804009830d22c0 0x04020100260c348b 0x80000047871d27f6 0xf20000011e1c749f

def z601 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x11f00078e1e3c1ec 0x2047c001e3878f07

def z602 : W := mkw 0x2e4d17040000002a 0x00b9345c10000000 0x440e060000000000 0x0110381800000000

def z603 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbc003e00f803d82d 0x8ef000f803e00f60

def z604 : W := mkw 0x01a0286881010090 0x000680a1a2040402 0xa9f03878810101e5 0xaea7c0e1e2040407

def z605 : W := mkw 0x2ef99dbaa18140a6 0x90bbe676ea860502 0x3af1d9b8e001c001 0x08ebc766e3800700

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000086012634 0x0000000002180498

def z607 : W := mkw 0x01b03d68a1a3d5b0 0xb006c0f5a2868f56 0xb9f03ff8e1e3ffef 0xaee7c0ffe3878fff

def z608 : W := mkw 0x0000809a00010284 0x040002026800040a 0x000001b800010601 0x00000006e0000418

def z609 : W := mkw 0x1fdf6244ffd80019 0xc07f7d8913ff6000 0xdfffe647fffc001e 0xff7fff991ffff000

def z610 : W := mkw 0x21fdaafea1a3419e 0xb087f6abfa868d06 0x41ffc07f01e001c0 0x6107ff01fc078007

def z611 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c07f871c01d4 0x7a0a0701fe1c7007

def z612 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e004719fc01dc 0x771438011c67f007

def z613 : W := mkw 0x0e00000054000001 0x0038000001500000 0x1c00000078000008 0x0470000001e00000

def z614 : W := mkw 0x0000000054009401 0x0000000001500250 0x92000180fe03fe3f 0x9a48000603f80ff8

def z615 : W := mkw 0x0080c09a83090284 0x040203026a0c240a 0x8281c1b8871d0615 0x7a0a0706e21c7418

def z616 : W := mkw 0x0e00150054000021 0x0038005401500000 0xbe003f80fe00001f 0x9ef800fe03f80000

def z617 : W := mkw 0x0104a2d60000001c 0x0004128b58000000 0xc78fe7ff00000003 0xff1e3f9ffc000000

def z618 : W := mkw 0x00800009810520c0 0x0002000026041483 0x8080007f811d21f7 0xfa020001fe047487

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x840000001800001c 0x1610000000600000

def z620 : W := mkw 0x01902048a1a34190 0xb006408122868d06 0x91002040e1e3c1ec 0xa644008103878f07

def z621 : W := mkw 0x0e00150054009421 0x0038005401500250 0xae003f801e003e13 0x9eb800fe007800f8

def z622 : W := mkw 0x00804009830d22c0 0x04020100260c348b 0x82000180871d27f7 0x9a080006021c749f

def z623 : W := mkw 0x1e5b00007cd00001 0xc0796c0001f34000 0xdfffc00078e00008 0x7f7fff0001e38000

def z624 : W := mkw 0x0000000054009401 0x0000000001500250 0x94002600fe03fe3e 0x9650009803f80ff8

def z625 : W := mkw 0x2fffbfffa9f769fe 0xf8bffefffea7dda7 0xfffffffff9fff9ff 0xffffffffffe7ffe7

def z626 : W := mkw 0x0106224508542858 0x48041889142150a1 0xc50e2647181c3812 0xf71438991c6070e0

def z627 : W := mkw 0x2f6d3f645400943b 0x00bdb4fd91500250 0x7d7e3e007802d808 0x05f5f8f801e00b60

def z628 : W := mkw 0x00b0c8baa3894284 0x9402c322ea8e250a 0x3af1d9b8e601c601 0x08ebc766e3980718

def z629 : W := mkw 0x1ffb6860ffd80011 0xc07feda183ff6000 0xfffff878fffc001d 0xffffffe1e3fff000

def z630 : W := mkw 0x0080000881010080 0x0002000022040402 0x0080003880010001 0x08020000e2000400

def z631 : W := mkw 0x0120286000000010 0x000480a180000000 0x2970380000000000 0x04a5c0e000000000

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000001802383c 0x00000000006008e0

def z633 : W := mkw 0x0f303d6074a2d531 0xb03cc0f581d28b54 0x3d703e0078e2d808 0x04f5c0f801e38b60

def z634 : W := mkw 0x0000150054009421 0x0000005401500250 0x30003f80fe03fe3f 0x80c000fe03f80ff8

def z635 : W := mkw 0x0100204000220110 0x2004008100008804 0x8500264019e239fe 0xb6140099006788e7

def z636 : W := mkw 0x0106224408500018 0x4004188910214000 0xc50e264719fc001e 0xf71438991c67f000

def z637 : W := mkw 0x01b0e8fba3af63d4 0xb406c3a3ee8ebd8f 0x83f1c1ff87fd27f7 0xfa0fc707fe1ff49f

def z638 : W := mkw 0x0e49150054009421 0x0039245401500250 0xffffff80fe03fe3f 0xfffffffe03f80ff8

def z639 : W := mkw 0x0104224400220918 0x2804108910008824 0x0000260000021800 0x0000009800000860

def z640 : W := mkw 0x0080000881010080 0x0002000022040402 0x00000000810101e4 0x0000000002040407

def z641 : W := mkw 0x0102204108762950 0x680408810421d8a5 0x8100204019fe39fc 0xa60400810067f8e7

def z642 : W := mkw 0x0000000000220100 0x2000000000008804 0x0000000001e201ec 0x0000000000078807

def z643 : W := mkw 0x010622455c76bd59 0x680418891571daf5 0xd50e2647fffffffe 0xf75438991fffffff

def z644 : W := mkw 0x0e00959200000024 0x0038025648000000 0xae81ffff00000003 0xfeba07fffc000000

def z645 : W := mkw 0x0100204000220110 0x2004008100008804 0x00002040000201e0 0x8000008100000807

def z646 : W := mkw 0x0006020508542848 0x48001808142150a1 0xc40e0647191c39f6 0xf31038191c6470e7

def z647 : W := mkw 0x0e901508f5a3d5a1 0xb03a405423d68f56 0xbe003f80ffe3ffff 0x9ef800fe03ff8fff

def z648 : W := mkw 0x0000809b000522c4 0x040002026c00148b 0x8281c1ff000127e3 0xfa0a0707fc00049f

def z649 : W := mkw 0x2f6f3f650876297a 0x68bdbcfd9421d8a5 0xed7e3e4719fe39fe 0xf7b5f8f91c67f8e7

def z650 : W := mkw 0x2f6f3f640872093a 0x68bdbcfd9021c824 0x6d7e3e0018e21808 0x05b5f8f800638860

def z651 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3c003f807803fe2b 0x84f000fe01e00ff8

def z652 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x660fffff00000003 0xd1983ffffc000000

def z653 : W := mkw 0x0002000108762940 0x680008000421d8a5 0x0000000001fc01c0 0x000000000007f007

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x800020000002002c 0x8600008000000800

def z655 : W := mkw 0x0e0200005c500001 0x4038080001714000 0xdf0e0000fffc001c 0x7f7c380003fff000

def z656 : W := mkw 0x0000809200000004 0x0000020248000000 0x8281c1ff86012637 0xfa0a0707fe180498

def z657 : W := mkw 0x01b0e8fba3af63d4 0xb406c3a3ee8ebd8f 0xb9f1f87fe1ffc1ed 0xeee7c7e1ff87ff07

def z658 : W := mkw 0x01b0e8faa3ab4394 0xb406c3a3ea8ead0e 0xbbf1f9f8e7e3c7ed 0xaeefc7e7e39f8f1f

def z659 : W := mkw 0x0104a2df00272bdc 0x2c04128b7c009caf 0x000027ff00033fe3 0x8000009ffc000cff

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x8100000001e0000c 0x2604000000078000

def z661 : W := mkw 0x0e80d59bd70db6e5 0x043a03566f5c36db 0xba81d9ffe71de7f7 0xfaea0767ff9c779f

def z662 : W := mkw 0x2126bff70876297e 0x68849affdc21d8a5 0xe50e3fff19fe39ff 0xf79438fffc67f8e7

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000011c0014 0x7200000000047000

def z664 : W := mkw 0x1e4b00005c500001 0x40792c0001714000 0x440e000018000000 0x0110380000600000

def z665 : W := mkw 0x0090c09ba3af63c4 0xb40243026e8ebd8f 0x9281c1ffe7ffe7ff 0xfa4a0707ff9fff9f

def z666 : W := mkw 0x0fb03d68f5a3d5b1 0xb03ec0f5a3d68f56 0xbdf03e78f9e3d9ed 0xaef7c0f9e3e78f67

def z667 : W := mkw 0x00804009830d22c0 0x04020100260c348b 0x80800078871d27f5 0xaa020001e21c749f

def z668 : W := mkw 0x0106224408720918 0x680418891021c824 0xc50e264019e219ec 0xa714389900678867

def z669 : W := mkw 0x2f6d3f640000003a 0x00bdb4fd90000000 0xeffffe0000000000 0x7fbffff800000000

def z670 : W := mkw 0x0002000108542840 0x48000800042150a1 0x00000000181c3810 0x00000000006070e0

def z671 : W := mkw 0x0000000800010080 0x0000000020000402 0x00000078000101e1 0x80000001e0000407

def z672 : W := mkw 0x0e00000054000001 0x0038000001500000 0x9e000180fe01263f 0x9e78000603f80498

def z673 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39703800e1e3c1ec 0x04e5c0e003878f07

def z674 : W := mkw 0x1ed94000f7880001 0x807b650003de2000 0x9bf1c000e7e0000c 0x2e6fc700039f8000

def z675 : W := mkw 0x0fb03d68a1a341b0 0xb03ec0f5a2868d06 0xbff03ff8e1e3c1ef 0xbeffc0ffe3878f07

def z676 : W := mkw 0x0080400883090080 0x00020100220c2402 0x8281c078871d01f5 0xfa0a0701e21c7407

def z677 : W := mkw 0x008240008b580000 0x40020900022d6000 0xc78fc0009ffc001c 0x7f1e3f00027ff000

def z678 : W := mkw 0x1ed9c09bf78d22c5 0x847b67026fde348b 0x9af1c1ffe71d27f7 0xfa6bc707ff9c749f

def z679 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e001f80fe01fe13 0x18f8007e03f807f8

def z680 : W := mkw 0x0f0637455c76bd79 0x683c18dd1571daf5 0xc70e27c71ffe3ffe 0xf71c389f1c7ff8ff

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000002036 0x9200000000000080

def z682 : W := mkw 0x0130286020a24110 0xb004c0a180828904 0xb970384061e2c1ec 0xa6e5c0e101878b07

def z683 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1bf861d2613 0x580a0706fe187498

def z684 : W := mkw 0x00920009a9f769c0 0xf802480026a7dda7 0x10000000f9fff9fc 0x0040000003e7ffe7

def z685 : W := mkw 0x0f0637445c729d39 0x683c18dd1171ca74 0x7d0e3e0078e2d808 0x05f438f801e38b60

def z686 : W := mkw 0x0080c09a83090284 0x040203026a0c240a 0x8281c1ff86010603 0xfa0a0707fe180418

def z687 : W := mkw 0x0000150000009420 0x0000005400000250 0xb8003f80e003fe2f 0x8ee000fe03800ff8

def z688 : W := mkw 0x2f6d3f640000003a 0x00bdb4fd90000000 0xedfe3e7800000001 0xafb7f8f9e0000000

def z689 : W := mkw 0x2f6fbff60850003e 0x40bdbeffd8214000 0xefffffff19fc001f 0xffbffffffc67f000

def z690 : W := mkw 0x0e0617055c54bc69 0x4838185c157152f1 0xfe0e3f87fe1ffe3f 0xdff838fe1ff87ff8

def z691 : W := mkw 0x2e49959200000026 0x00b9265648000000 0x0201c18000000000 0x0008070600000000

def z692 : W := mkw 0x00b00828a1814080 0x9002c020a2860502 0x00f0003800000000 0x0003c000e0000000

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0x8400260000000002 0x9610009800000000

def z694 : W := mkw 0x1ed95500f7889421 0x807b655403de2250 0xbef1ff80fe03fe3f 0x9efbc7fe03f80ff8

def z695 : W := mkw 0x0e00150054009421 0x0038005401500250 0x16000780fe03fe3e 0x1058001e03f80ff8

def z696 : W := mkw 0x0f0622455c762959 0x683c18891571d8a5 0xdf0e2647fffe39fe 0xff7c38991ffff8e7

def z697 : W := mkw 0x01b42a6da1a769d8 0xb806d0a9b6869da7 0xb9f03e7fe1e3f9ef 0xaee7c0f9ff878fe7

def z698 : W := mkw 0x0030082020804000 0x9000c02080820100 0x387018006000c000 0x00e1c06001800300

def z699 : W := mkw 0x2124bff60000003e 0x008492ffd8000000 0xa281ffff00000003 0xfa8a07fffc000000

def z700 : W := mkw 0x1092c09bffdd22c5 0xc4424b026fff748b 0x9281c1fffffd27ff 0xfa4a0707fffff49f

def z701 : W := mkw 0x2124bff60000003e 0x008492ffd8000000 0xe50e3fff00000003 0xf79438fffc000000

def z702 : W := mkw 0x0e49000000000000 0x0039240000000000 0x4d7e000000000000 0x0535f80000000000

def z703 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e260019fe39fc 0x051438980067f8e7

def z704 : W := mkw 0x0e00000054000001 0x0038000001500000 0x1a000000e6000000 0x0868000003980000

def z705 : W := mkw 0x0080809a81010084 0x000202026a040402 0x8281c1ff810101e7 0xfa0a0707fe040407

def z706 : W := mkw 0x0000150000000020 0x0000005400000000 0x20003f8000000003 0x808000fe00000000

def z707 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xfffffe00fffef83e 0xfffffff803fffbe0

def z708 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03e78e1e3f9ef 0xaee7c0f9e3878fe7

def z709 : W := mkw 0x0e80d59bd70db6e5 0x043a03566f5c36db 0x3c81fe7f791ed9c8 0x64f207f9fde47b67

def z710 : W := mkw 0x00900008a1810080 0x8002400022860402 0xb9f03878e1e3c1ed 0xaee7c0e1e3878f07

def z711 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x61fff87f00000001 0xe187ffe1fc000000

def z712 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f80fe03fe3e 0x14f800fe03f80ff8

def z713 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc5ffe67f1802383e 0xf717ff99fc6008e0

def z714 : W := mkw 0x1edb5500abd80020 0xc07b6d5402af6000 0xefffff8001fc0003 0xffbffffe0007f000

def z715 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff0002002f 0xffbffffffc000800

def z716 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff871d27e3 0xe80a0707fe1c749f

def z717 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xdfffe600fffffe3e 0xff7fff9803fffff8

def z718 : W := mkw 0x10db4000ffd89401 0xc0436d0003ff6250 0x51ffc000fffffe3c 0x6147ff0003fffff8

def z719 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5fffc0007ffc0018 0x757fff0001fff000

def z720 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000fffd263c 0x7f7fff0003fff498

def z721 : W := mkw 0x00b00828a1a34180 0xb002c020a2868d06 0x38f01838e1e1c1c1 0x08e3c060e3878707

def z722 : W := mkw 0x2e6d9fb60000002e 0x00b9b67ed8000000 0xeeffdfff00000003 0xfbbbff7ffc000000

def z723 : W := mkw 0x2e6d9fb60000002e 0x00b9b67ed8000000 0x6affd9bf00000001 0x49abff66fc000000

def z724 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe81ff80fe03fe3f 0xfefa07fe03f80ff8

def z725 : W := mkw 0x10924009abdd22c0 0xc442490026af748b 0x0000000087fd27f4 0x00000000021ff49f

def z726 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe803ff8fe03fe3f 0xbefa00ffe3f80ff8

def z727 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0x4dffc07f00000000 0x6537ff01fc000000

def z728 : W := mkw 0x2fed7f6d830d22fa 0x04bfb5fdb60c348b 0x6d7e3e00871d27f4 0x05b5f8f8021c749f

def z729 : W := mkw 0x2edd979ea1a341ae 0xb0bb765e7a868d06 0x560fc787e1e3c1ee 0x51583f1e1f878f07

def z730 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x43ffc00007fc0010 0x710fff00001ff000

def z731 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0xe5ffffff00000003 0xf797fffffc000000

def z732 : W := mkw 0x10924009ffddb6c1 0xc442490027ff76db 0x10000000fffffffc 0x0040000003ffffff

def z733 : W := mkw 0x00b00828a1a34180 0xb002c020a2868d06 0xb8f03838e1e3c1ed 0x8ee3c0e0e3878f07

def z734 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff011c0017 0xffbffffffc047000

def z735 : W := mkw 0x0049809200000004 0x0001260248000000 0x41ffc07f00000000 0x6107ff01fc000000

def z736 : W := mkw 0x1e4b40005e580001 0x40792d0001796000 0xcfffc0001ffc001c 0x7f3fff00007ff000

def z737 : W := mkw 0x0f0637455c76bd79 0x683c18dd1571daf5 0x7b0e19c7e7fdc7c1 0x69ec38671f9ff71f

def z738 : W := mkw 0x01262a6508762958 0x680498a99421d8a5 0xfdfe3e7ff9fff9ff 0xfff7f8f9ffe7ffe7

def z739 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xffffffff6002c00b 0xfffffffffd800b00

def z740 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f0387861e3c1e9 0xa4e7c0e1e1878f07

def z741 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281e7ff871f3ff7 0xfa0a079ffe1c7cff

def z742 : W := mkw 0x0ecb40008b580000 0x403b2d00022d6000 0xcfffc0009ffc001c 0x7f3fff00027ff000

def z743 : W := mkw 0x10db5500abd89420 0xc0436d5402af6250 0x61ffff8001fffe23 0xe187fffe0007fff8

def z744 : W := mkw 0x1ed9d59af78996a5 0x847b67566bde265a 0x3af1d9b8e601c601 0x08ebc766e3980718

def z745 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000fffe383c 0x7f7fff0003fff8e0

def z746 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5fffc000fffc0008 0x6d7fff0003fff000

def z747 : W := mkw 0x0124aaf60000001c 0x000492abd8000000 0xefffffff00000003 0xffbffffffc000000

def z748 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffff80fffc3e1f 0xfffffffe03fff0f8

def z749 : W := mkw 0x216daaf65400941f 0x0085b6abd9500250 0x51ffc07ffe03fe3c 0x6147ff01fff80ff8

def z750 : W := mkw 0x1fdd6245f7ae2959 0xa87f758917deb8a5 0x1af1e647e60239e2 0x886bc7991f9808e7

def z751 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6fffffff00000002 0x75bffffffc000000

def z752 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc1ffc07f00000001 0xeb07ff01fc000000

def z753 : W := mkw 0x0120286000220110 0x200480a180008804 0xb9f03878e1e3c1ed 0xaee7c0e1e3878f07

def z754 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000ffffc03c 0x7f7fff0003ffff00

def z755 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x43ffc00087fc0000 0x690fff00021ff000

def z756 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffff80fffdc61f 0xfffffffe03fff718

def z757 : W := mkw 0x0fb03d68f5a3d5b1 0xb03ec0f5a3d68f56 0x07f007f81fe03fd2 0x301fc01fe07f80ff

def z758 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f0387861e2c1ec 0xa6e7c0e1e1878b07

def z759 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x45ffc67f00000002 0x7117ff19fc000000

def z760 : W := mkw 0x216dbff60000943e 0x0085b6ffd8000250 0x61ffffff0003fe23 0xe187fffffc000ff8

def z761 : W := mkw 0x2124aaf70026295e 0x288492abdc0098a5 0x0000267f000239e2 0x80000099fc0008e7

def z762 : W := mkw 0x1edb4008ffd90281 0xc47b6d0023ff640a 0xdfffc000fffd061c 0x7f7fff0003fff418

def z763 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xefffffff0002d803 0xffbffffffc000b60

def z764 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc70e27c71ffe3ffe 0xf71c389f1c7ff8ff

def z765 : W := mkw 0x1edb4008ffd90081 0xc07b6d0023ff6402 0xfffff878ffffc1fd 0xffffffe1e3ffff07

def z766 : W := mkw 0x216daaf60022011e 0x2085b6abd8008804 0xc1ffe07f01e201ec 0xe707ff81fc078807

def z767 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xedfffe7f00000003 0xffb7fff9fc000000

def z768 : W := mkw 0x01262a6508766958 0x780498a99421d9a5 0xe50e3e4719fef9fe 0xf79438f91c67fbe7

def z769 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffffe603c62f 0xffffffffff980f18

def z770 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xc7ffc0001ffc001c 0x771fff00007ff000

def z771 : W := mkw 0x004b000008500000 0x40012c0000214000 0x41ffc00001fc0000 0x6107ff000007f000

def z772 : W := mkw 0x1f6b68685e7b4191 0x707dada1a179ed06 0x660ff8781e1fc1f1 0xd1983fe1e0787f07

def z773 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc58e267f19fe39ff 0xff163899fc67f8e7

def z774 : W := mkw 0x01b06868a3ab4190 0xb006c1a1a28ead06 0xb9f1f878e1ffc1ed 0xeee7c7e1e387ff07

def z775 : W := mkw 0x01b42a6ca1a34198 0xb006d0a9b2868d06 0xb9f03e7fe1e3c1ef 0xaee7c0f9ff878f07

def z776 : W := mkw 0x01262a6508762958 0x680498a99421d8a5 0xe50e3e7f19fe39ff 0xf79438f9fc67f8e7

def z777 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878e1e3e1ff 0xbee7c0e1e3878f87

def z778 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0xe3ffffff00000003 0xfb8ffffffc000000

def z779 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0xcfffc00019fc001c 0x7f3fff000067f000

def z780 : W := mkw 0x0130286820a34190 0xb004c0a1a0828d06 0xb9703878e0e3c1ed 0x8ee5c0e1e3838f07

def z781 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xfffffffffe01263f 0xfffffffffff80498

def z782 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f80fe03fe33 0x98f800fe03f80ff8

def z783 : W := mkw 0x2f6dbff60022013e 0x20bdb6ffd8008804 0xefffffff000201e3 0xffbffffffc000807

def z784 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0xc78fc1ff871d27f7 0xff1e3f07fe1c749f

def z785 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x41ffe67f00000002 0xe107ff99fc000000

def z786 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xefffffff00003e03 0xffbffffffc0000f8

def z787 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc7ffc0009ffc001c 0x7f1fff00027ff000

def z788 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e26479fff3ffe 0xf71438991e7ffcff

def z789 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffff80fffed81f 0xfffffffe03fffb60

def z790 : W := mkw 0x2e6d9fb60000002e 0x00b9b67ed8000000 0xefffdfbf00000003 0x7fbfff7efc000000

def z791 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xf9fff800e1ffc02d 0xefe7ffe00387ff00

def z792 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbbf039f8e7e3c7ed 0xaeefc0e7e39f8f1f

def z793 : W := mkw 0x0e4b15005c509421 0x40392c5401714250 0xffffff80fffffe3f 0xfffffffe03fffff8

def z794 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x67ffffff00000003 0xf19ffffffc000000

def z795 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x9281c1ffe71fe7ff 0xfa4a0707ff9c7f9f

def z796 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xffffd980fffc001d 0x7fffff6603fff000

def z797 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0201c1ff871d27f7 0xd0080707fe1c749f

def z798 : W := mkw 0x31b6fff6ffd8003f 0xc0c6dbffdbff6000 0x30003ffffffc001f 0x80c000fffffff000

def z799 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffff6000c003 0xfffffffffd800300

def z800 : W := mkw 0x00b60a2da9d568c8 0xd802d828b6a755a3 0x7cfe1e3ff81df813 0x59f3f878ffe077e0

def z801 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8681c7ff9f1d3ff7 0xfa1a071ffe7c74ff

def z802 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbff03f80fe03fe3f 0xbeffc0fe03f80ff8

def z803 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xcfffc7ff00000002 0x7f3fff1ffc000000

def z804 : W := mkw 0x0090c09ba38d22c4 0x840243026e8e348b 0xbbf1f9ffe7ffe7ff 0xfeefc7e7ff9fff9f

def z805 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc047fffc001e 0xff7fff011ffff000

def z806 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc180fffd061d 0x7f7fff0603fff418

def z807 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x38f03878e1e3c1ed 0x88e3c0e1e3878f07

def z808 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878f9e3f9fd 0xaee7c0e1e3e78fe7

def z809 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f0387fe1e3c1ef 0xfee7c0e1ff878f07

def z810 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xffffd800fffdc01d 0x7fffff6003fff700

def z811 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xdfffc780fffffe3e 0x7f7fff1e03fffff8

def z812 : W := mkw 0x0e00150054009421 0x0038005401500250 0x36003f80fe03fe3f 0x90d800fe03f80ff8

def z813 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xefffffff9e013e37 0xffbffffffe7804f8

def z814 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff871d07d5 0x7a0a0707fe1c741f

def z815 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0x41ffc0001ffc0010 0x6107ff00007ff000

def z816 : W := mkw 0x0186e2de8b7b0b9c 0x6c061b8b7a2dec2e 0x478fe7b89ee31e09 0x0d1e3f9ee27b8c78

def z817 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000e7fc0000 0x7f7fff00039ff000

def z818 : W := mkw 0x2124bfff00272bfe 0x2c8492fffc009caf 0x20003fff00033fe3 0x808000fffc000cff

def z819 : W := mkw 0x2e6b9db308762966 0x68b9ae76cc21d8a5 0x2af1d9b819fe39fd 0x08abc766e067f8e7

def z820 : W := mkw 0x1edb5508ffd994a1 0xc07b6d5423ff6652 0xfffffff8ffffffff 0xffffffffe3ffffff

def z821 : W := mkw 0x1e5b809b7cd522c5 0xc4796e026df3548b 0x5d7e01ff78e127eb 0x8575f807fde3849f

def z822 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xefffffff1e000013 0xffbffffffc780000

def z823 : W := mkw 0x0090c09ba38d62c4 0x940243026e8e358b 0x9281c1ffe71de7f7 0xfa4a0707ff9c779f

def z824 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f03878e1e3c1e1 0xa8e7c0e1e3878f07

def z825 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xffffffffe000000f 0xffffffffff800000

def z826 : W := mkw 0x01262a6508762958 0x680498a99421d8a5 0xed7e3e4719fe39fe 0xf7b5f8f91c67f8e7

def z827 : W := mkw 0x1e924009ffdd22c1 0xc47a490027ff748b 0x9e000180fffd27ff 0x9e78000603fff49f

def z828 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xcdfe264719fe39fe 0xff37f8991c67f8e7

def z829 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f03878e0e3c1e9 0x8ce7c0e1e3838f07

def z830 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x45ffc00019fc0010 0x7117ff000067f000

def z831 : W := mkw 0x0e49150054009421 0x0039245401500250 0xbef1ff80fe03fe3f 0x9efbc7fe03f80ff8

def z832 : W := mkw 0x0130e8f322ae6354 0xb404c3a3cc8ab98d 0x3b71f98766fee61a 0x54edc7e61d9bfb98

def z833 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffffe01fe13 0xfffffffffff807f8

def z834 : W := mkw 0x10db4008abd90080 0xc0436d0022af6402 0xc1ffc07881fd01e5 0xeb07ff01e207f407

def z835 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xfffff980ffffc63d 0xffffffe603ffff18

def z836 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x69fff87f00000000 0x65a7ffe1fc000000

def z837 : W := mkw 0x0000c093020c2244 0x040003024c083089 0x8281c1ff071c27f7 0xfa0a0707fc1c709f

def z838 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xfffff800fffffe3d 0xffffffe003fffff8

def z839 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e260719fe39fe 0x551438981c67f8e7

def z840 : W := mkw 0x2124bfff002769fe 0x388492fffc009da7 0x20003fff0003f9e3 0x808000fffc000fe7

def z841 : W := mkw 0x0006020508762948 0x680018081421d8a5 0xc40e260719fe39fe 0xd71038981c67f8e7

def z842 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff071c27d3 0xfa0a0707fc1c709f

def z843 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e064719fc19c0 0x611438191c67f067

def z844 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264719fe39f2 0xf11438991c67f8e7

def z845 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x45ffc00019fc0000 0x6117ff000067f000

def z846 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffdf80fffdfe1f 0x7fffff7e03fff7f8

def z847 : W := mkw 0x0000c09b020d22c4 0x040003026c08348b 0x8281c1ff061d27f3 0xfa0a0707fc18749f

def z848 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff86010603 0xffbffffffe180418

def z849 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000fffc203e 0xff7fff0003fff080

def z850 : W := mkw 0x2f6daaf65400001f 0x00bdb6abd9500000 0xdfffc07ffe00001c 0x7f7fff01fff80000

def z851 : W := mkw 0x01b42a6ca1a34198 0xb006d0a9b2868d06 0xfdfe3e7ff9e3f9ff 0xfff7f8f9ffe78fe7

def z852 : W := mkw 0x1edb4008ffd90081 0xc07b6d0023ff6402 0xdfffc038fffd001d 0x7f7fff00e3fff400

def z853 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xfd0e3e4779fef9fe 0xf7f438f91de7fbe7

def z854 : W := mkw 0x2124bff70026bd7e 0x288492ffdc009af5 0x20003fff0003ffe3 0x808000fffc000fff

def z855 : W := mkw 0x0130286820a34190 0xb004c0a1a0828d06 0x3970387860e2c1c8 0x04e5c0e1e1838b07

def z856 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc1ffc07f00000002 0xf307ff01fc000000

def z857 : W := mkw 0x00924000abd80000 0xc002490002af6000 0xdfffc000fffc001c 0x7f7fff0003fff000

def z858 : W := mkw 0x01b06868a3ab4190 0xb006c1a1a28ead06 0xbbf1f878e7e3c1ed 0xaeefc7e1e39f8f07

def z859 : W := mkw 0x0e4b00005c500001 0x40392c0001714000 0xdfffc000fffc001c 0x7f7fff0003fff000

def z860 : W := mkw 0x0e4b000008500000 0x40392c0000214000 0xcfffc00001fc0000 0x7f3fff000007f000

def z861 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x45ffe67f00000000 0x6517ff99fc000000

def z862 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0x51ffc00079fc0008 0x6147ff0001e7f000

def z863 : W := mkw 0x0e49959254009425 0x0039265649500250 0xfffffffffe03fe3f 0xfffffffffff80ff8

def z864 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc9ffc07f00000000 0x6f27ff01fc000000

def z865 : W := mkw 0x1e4bd5935e5cb665 0x44792f564d7972d9 0x460fc7871e1c3e12 0x51183f1e1c7870f8

def z866 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3c003f80fe03fe3f 0x84f000fe03f80ff8

def z867 : W := mkw 0x2e6d9fb60000002e 0x00b9b67ed8000000 0x46ffc7bf00000002 0x511bff1efc000000

def z868 : W := mkw 0x0000150054009421 0x0000005401500250 0xb4003f80fe03fe3f 0x96d000fe03f80ff8

def z869 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003fc7fe03fe3f 0xfef800ff1ff80ff8

def z870 : W := mkw 0x0f6d2a6400000018 0x003db4a990000000 0xeffffe7f00000003 0xffbffff9fc000000

def z871 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xefffffff1e03fe33 0xffbffffffc780ff8

def z872 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f0187861e0c1c0 0x20e7c061e1878307

def z873 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281e1ff871f27ff 0xfe0a0787fe1c7c9f

def z874 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffd9ff00000001 0x7fbfff67fc000000

def z875 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff00012623 0xffbffffffc000498

def z876 : W := mkw 0x2e6d9fb60000002e 0x00b9b67ed8000000 0xeeffffbf00000003 0xdfbbfffefc000000

def z877 : W := mkw 0x0e00150054009421 0x0038005401500250 0xff0e3f80fe03fe3f 0xfffc38fe03f80ff8

def z878 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0x47ffc7801ffc3e12 0x711fff1e007ff0f8

def z879 : W := mkw 0x0006020508762948 0x680018081421d8a5 0xc50e060719fe39fe 0x771438181c67f8e7

def z880 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xffffffffe003fe2f 0xffffffffff800ff8

def z881 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f03838e1e3c1ed 0x0ce7c0e0e3878f07

def z882 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f03878e1e3c1ec 0x24e7c0e1e3878f07

def z883 : W := mkw 0x01b42a6ca1a34198 0xb006d0a9b2868d06 0xfdfe3e78e1e3c1ed 0xaff7f8f9e3878f07

def z884 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264719fe19dc 0x771438991c67f867

def z885 : W := mkw 0x2124bff70026297e 0x288492ffdc0098a5 0x20003fff000001c3 0x808000fffc000007

def z886 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x43ffc1ff00000000 0x610fff07fc000000

def z887 : W := mkw 0x0049809200000004 0x0001260248000000 0xc3ffc1ff00000003 0xfb0fff07fc000000

def z888 : W := mkw 0x1edb4008ffd90081 0xc07b6d0023ff6402 0xdfffc078fffc01dc 0x7f7fff01e3fff007

def z889 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f039f8e1e3e7ef 0xaee7c0e7e3878f9f

def z890 : W := mkw 0x0e49959200000024 0x0039265648000000 0xefffffff00000003 0xffbffffffc000000

def z891 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xebfff9ff00000001 0xefafffe7fc000000

def z892 : W := mkw 0x0090c09ba38d22c4 0x840243026e8e348b 0x83f1c1ff87fd27f7 0xfa0fc707fe1ff49f

def z893 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8bf1c1ff871d27f7 0xfe2fc707fe1c749f

def z894 : W := mkw 0x00924009abff6bc0 0xfc02490026affdaf 0x10000000fffffffc 0x0040000003ffffff

def z895 : W := mkw 0x1e5b00007cd00001 0xc0796c0001f34000 0xdfffc00079fc001c 0x7f7fff0001e7f000

def z896 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xdbffc000e7fc001c 0x7f6fff00039ff000

def z897 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0x7bffd9ffe601c601 0x69efff67ff980718

def z898 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff9e033e3f 0xffbffffffe780cf8

def z899 : W := mkw 0x00b00828a1a34180 0xb002c020a2868d06 0xb8f01878e1e3c1ed 0xaae3c061e3878f07

def z900 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xff0e3fc7ffffffff 0xfffc38ff1fffffff

def z901 : W := mkw 0x0edb0000a9d00000 0xc03b6c0002a74000 0xdfffc000f9fc001c 0x7f7fff0003e7f000

def z902 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff871d07e5 0xea0a0707fe1c741f

def z903 : W := mkw 0x0130286820a34190 0xb004c0a1a0828d06 0xb9f0387860e3c1e9 0xaee7c0e1e1838f07

def z904 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xfdfe3878e1e3c1ed 0xfff7f8e1e3878f07

def z905 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0x7dfffe7f7802d808 0x65f7fff9fde00b60

def z906 : W := mkw 0x2f6f3f645c729d3b 0x68bdbcfd9171ca74 0x7d7e3e0078e2d808 0x05f5f8f801e38b60

def z907 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffd980fffffe3d 0x7fffff6603fffff8

def z908 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0x41ffc7ff00000002 0x6107ff1ffc000000

def z909 : W := mkw 0x0e49150054009421 0x0039245401500250 0xfe0fff80fe03fe3f 0xdff83ffe03f80ff8

def z910 : W := mkw 0x10924009abdd22c0 0xc442490026af748b 0x0000000001fc01c0 0x000000000007f007

def z911 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xfffffffffe03c03f 0xfffffffffff80f00

def z912 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdbffc000e7fc000c 0x6f6fff00039ff000

def z913 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0xe9ffffff00000003 0xefa7fffffc000000

def z914 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff18003813 0xffbffffffc6000e0

def z915 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0x4bffc07f00000000 0x692fff01fc000000

def z916 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x9a81c1ffe71d27ff 0xfe6a0707ff9c749f

def z917 : W := mkw 0x0090c09ba38d22c4 0x840243026e8e348b 0x9281c1ffe7fd27ff 0xfa4a0707ff9ff49f

def z918 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc180fffc001f 0xff7fff0603fff000

def z919 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xfffffe00ffffd83d 0xfffffff803ffff60

def z920 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6dffffff00000003 0xe5b7fffffc000000

def z921 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878e7e3e7fd 0xaee7c0e1e39f8f9f

def z922 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8681c1ff9f1d27ff 0xfe1a0707fe7c749f

def z923 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264719fe39fc 0x651438991c67f8e7

def z924 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff871d27f6 0x700a0707fe1c749f

def z925 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x41ffc00019fc001c 0x6107ff000067f000

def z926 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0xdfffc000e1fc000c 0x7f7fff000387f000

def z927 : W := mkw 0x1edb4008ffd94081 0xd07b6d0023ff6502 0xdfffc000fffdc01c 0x7f7fff0003fff700

def z928 : W := mkw 0x1e5b55007ed89421 0xc0796d5401fb6250 0xff7fff80fefffe3f 0xdffdfffe03fbfff8

def z929 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5fffc000fefc0018 0x5d7fff0003fbf000

def z930 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff80010027 0xffbffffffe000400

def z931 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x69ffd87f00000000 0x61a7ff61fc000000

def z932 : W := mkw 0x0e49809200000004 0x0039260248000000 0xcfffc07f00000000 0x7f3fff01fc000000

def z933 : W := mkw 0x206d8ab60000000e 0x0081b62ad8000000 0x40ffc03f00000000 0x4103ff00fc000000

def z934 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc040fffc01fc 0xff7fff0103fff007

def z935 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xdfffc180fffc061c 0x7f7fff0603fff018

def z936 : W := mkw 0x1edb4008ffd90081 0xc07b6d0023ff6402 0xdfffc1f8fffd27ff 0xff7fff07e3fff49f

def z937 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xdfffc000fffc3e1c 0x7f7fff0003fff0f8

def z938 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffd800fffcc01c 0x7fffff6003fff300

def z939 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xfffff800fffec01c 0x7fffffe003fffb00

def z940 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6fffffff00000003 0x8dbffffffc000000

def z941 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x59ffc00061fc0000 0x6167ff000187f000

def z942 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff1802180b 0xffbffffffc600860

def z943 : W := mkw 0x0006020508542848 0x48001808142150a1 0xc50e064719fc39fe 0xf71438191c67f0e7

def z944 : W := mkw 0x0000809300042044 0x000002024c001081 0x8281c1ff871d27f7 0xfa0a0707fe1c749f

def z945 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xeffffe7f00000000 0x7fbffff9fc000000

def z946 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff871d27f5 0x680a0707fe1c749f

def z947 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xdfffc000fffdc61c 0x7f7fff0003fff718

def z948 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xffffffffe001c003 0xffffffffff800700

def z949 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x43ffc1ff00000001 0x690fff07fc000000

def z950 : W := mkw 0x0e49150054009421 0x0039245401500250 0xff7e3f80fe03fe3f 0x9ffdf8fe03f80ff8

def z951 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xddffc00079fc001c 0x7777ff0001e7f000

def z952 : W := mkw 0x004b000008500000 0x40012c0000214000 0xc5ffc00019fc001c 0x7717ff000067f000

def z953 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x45ffc67f00000000 0x6117ff19fc000000

def z954 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xffffffff7800000b 0xfffffffffde00000

def z955 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0xcfffc1ff00000003 0xff3fff07fc000000

def z956 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xdfffc000fffed81c 0x7f7fff0003fffb60

def z957 : W := mkw 0x2e6d9fb65400942f 0x00b9b67ed9500250 0xfeffffbffe03fe3f 0xdffbfffefff80ff8

def z958 : W := mkw 0x0000150054009421 0x0000005401500250 0xb8003f80fe03fe3f 0x8ee000fe03f80ff8

def z959 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc1ffc00001fc0014 0x7307ff000007f000

def z960 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xedfffe7f00000001 0xefb7fff9fc000000

def z961 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc70e27c719fe39ff 0xff1c389f1c67f8e7

def z962 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878e1ffc1fd 0xfee7c0e1e387ff07

def z963 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbbf1f878e1e3c1ed 0xfeefc7e1e3878f07

def z964 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff06002613 0xffbffffffc180098

def z965 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264719fe39fe 0x851438991c67f8e7

def z966 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0x61ffd9ff00000001 0x6187ff67fc000000

def z967 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0x47ffc7ff1e003e12 0x711fff1ffc7800f8

def z968 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003fc0ff03ffff 0xbef800ff03fc0fff

def z969 : W := mkw 0x01b06868a3ab4390 0xb406c1a1a28ead0e 0xb9f03878e7e3c7ed 0xaee7c0e1e39f8f1f

def z970 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264799ff39ff 0xff1438991e67fce7

def z971 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffff80fffefe1e 0x7ffffffe03fffbf8

def z972 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xefffffff18001803 0xffbffffffc600060

def z973 : W := mkw 0x01b06868a3ab4190 0xb006c1a1a28ead06 0xb9f03878e7ffc1fd 0xaee7c0e1e39fff07

def z974 : W := mkw 0x0e49809254000005 0x0039260249500000 0xdfffc1fffe01263f 0xff7fff07fff80498

def z975 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffffe03de0b 0xfffffffffff80f78

def z976 : W := mkw 0x10924009ffff63c1 0xf442490027fffd8f 0x10000000ffffe7fc 0x0040000003ffff9f

def z977 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39703878e1e3c1ed 0x84e5c0e1e3878f07

def z978 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff0003c023 0xffbffffffc000f00

def z979 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffd980fffde63f 0xffffff6603fff798

def z980 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc1ffc00081fc0004 0x6b07ff000207f000

def z981 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xffffffffe6000003 0xffffffffff980000

def z982 : W := mkw 0x1e5b40007ed80001 0xc0796d0001fb6000 0xdf7fc000fefc001c 0x5f7dff0003fbf000

def z983 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xfffff980ffffe63f 0xffffffe603ffff98

def z984 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xfffffe00fffc001c 0x7ffffff803fff000

def z985 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0xcfffc00087fc0014 0x7f3fff00021ff000

def z986 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264719fe39da 0x751438991c67f8e7

def z987 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff01e0000f 0xffbffffffc078000

def z988 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xfffffffff803f83f 0xffffffffffe00fe0

def z989 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f0387861e2c1c9 0xaee7c0e1e1878b07

def z990 : W := mkw 0x2e4f97975c54bc6f 0x48b93e5e5d7152f1 0x460fc7871e1c3e12 0x51183f1e1c7870f8

def z991 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff1800001f 0xffbffffffc600000

def z992 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f01878e1e1c1cd 0x2ee7c061e3878707

def z993 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878e1e1c1c1 0xaee7c0e1e3878707

def z994 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264719fc39d2 0xf71438991c67f0e7

def z995 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x69ffd87f00000001 0x69a7ff61fc000000

def z996 : W := mkw 0x0090c09ba38d22c4 0x840243026e8e348b 0x9af1c1ffe71d27f7 0xfa6bc707ff9c749f

def z997 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264719fe19ec 0xe71438991c67f867

def z998 : W := mkw 0x2e4d97960000002e 0x00b9365e58000000 0xcfffc7ff00000003 0xff3fff1ffc000000

def z999 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f80fe03fe1b 0x1cf800fe03f80ff8

def z1000 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xc7ffe7ff00000002 0xf71fff9ffc000000

def z1001 : W := mkw 0x0f4da2d60000001c 0x003d368b58000000 0xcfffe7ff00000003 0xff3fff9ffc000000

def z1002 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffff7803fe2b 0xfffffffffde00ff8

def z1003 : W := mkw 0x10db4008abd90080 0xc0436d0022af6402 0x41ffc07801fc01c0 0x6107ff01e007f007

def z1004 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xdfffc600fffc181c 0x7f7fff1803fff060

def z1005 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbbf039f8e1e3c1ef 0xbeefc0e7e3878f07

def z1006 : W := mkw 0x1edb4000ffd89401 0xc07b6d0003ff6250 0xdfffc180fffffe3f 0xff7fff0603fffff8

def z1007 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffe600fffe181c 0x7f7fff9803fff860

def z1008 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f80fe03fe2b 0x8cf800fe03f80ff8

def z1009 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff86000017 0xffbffffffe180000

def z1010 : W := mkw 0x10924009ffdd22c1 0xc442490027ff748b 0x10000000fffc01dc 0x0040000003fff007

def z1011 : W := mkw 0x01262a6508762958 0x680498a99421d8a5 0xc5fe267f19fe39fe 0xf717f899fc67f8e7

def z1012 : W := mkw 0x01b42a6ca1a34198 0xb006d0a9b2868d06 0xf9fe387fe1e3c1ed 0xefe7f8e1ff878f07

def z1013 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc000fffd003d 0xff7fff0003fff400

def z1014 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc78fe64719fe39fe 0xff1e3f991c67f8e7

def z1015 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e064719fe39fe 0x711438191c67f8e7

def z1016 : W := mkw 0x0130286020a24110 0xb004c0a180828904 0xb9f0387861e2c1ed 0xaee7c0e1e1878b07

def z1017 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x45ffc00019fc0008 0x6517ff000067f000

def z1018 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc3ffc18087fd2637 0xfb0fff06021ff498

def z1019 : W := mkw 0x2f6dbff65400003f 0x00bdb6ffd9500000 0xfffffffffe02383f 0xfffffffffff808e0

def z1020 : W := mkw 0x2f6dbff60022413e 0x30bdb6ffd8008904 0xefffffff0002c003 0xffbffffffc000b00

def z1021 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e064719fc39f6 0xf31438191c67f0e7

def z1022 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc5ffe60019fe383e 0xf717ff980067f8e0

def z1023 : W := mkw 0x0000c09b020d22c4 0x040003026c08348b 0x8201c1ff861d27f7 0xda080707fe18749f

def z1024 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x43ffc1ff00000002 0x710fff07fc000000

def z1025 : W := mkw 0x2f24bff70026297e 0x28bc92ffdc0098a5 0xae003fff180239ff 0x9eb800fffc6008e7

def z1026 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xffffff80fffd263f 0xfffffffe03fff498

def z1027 : W := mkw 0x2f6dbff60022013e 0x20bdb6ffd8008804 0xefffffff01e001c3 0xffbffffffc078007

def z1028 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffffe01c61f 0xfffffffffff80718

def z1029 : W := mkw 0x216dbff60000003e 0x0085b6ffd8000000 0x61fffe7f00000000 0x6187fff9fc000000

def z1030 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff071c07c0 0x600a0707fc1c701f

def z1031 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xebfff9ff00000003 0xffafffe7fc000000

def z1032 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xefffffff06000603 0xffbffffffc180018

def z1033 : W := mkw 0x01b06868a3ab4190 0xb006c1a1a28ead06 0xbbf1f9f8e7ffe7ff 0xfeefc7e7e39fff9f

def z1034 : W := mkw 0x2124aaf70026295e 0x288492abdc0098a5 0x0000007f000001c0 0x00000001fc000007

def z1035 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xefffffff1803fe3f 0xffbffffffc600ff8

def z1036 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x51ffc000e1fc000c 0x6147ff000387f000

def z1037 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc1ffc00001fc000c 0x6707ff000007f000

def z1038 : W := mkw 0x0002000108542040 0x4000080004215081 0xc50e264719fe39fe 0xf71438991c67f8e7

def z1039 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff00002037 0xffbffffffc000080

def z1040 : W := mkw 0x0000c09b020d22c4 0x040003026c08348b 0x8201c1ff071d27f7 0xf2080707fc1c749f

def z1041 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xed0e3e4719fe39ff 0xffb438f91c67f8e7

def z1042 : W := mkw 0x01b6eaffabff6bdc 0xfc06dbabfeaffdaf 0x41ffc07f01fc01c0 0x6107ff01fc07f007

def z1043 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff9f1f3fff 0xfa0a0707fe7c7cff

def z1044 : W := mkw 0x0130286820a34190 0xb004c0a1a0828d06 0xb970387861e3c1ed 0xa6e5c0e1e1878f07

def z1045 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6fffdfff00000003 0x79bfff7ffc000000

def z1046 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff861d27f3 0xd80a0707fe18749f

def z1047 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc5ffc07f00000000 0x7717ff01fc000000

def z1048 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xffffff80fffe383f 0xfffffffe03fff8e0

def z1049 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbff03ff8ffe3ffff 0xbeffc0ffe3ff8fff

def z1050 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0x41ffc1ff00000003 0xe107ff07fc000000

def z1051 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xdfffc780fffd3e3f 0xff7fff1e03fff4f8

def z1052 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffe780ffff3e3f 0xff7fff9e03fffcf8

def z1053 : W := mkw 0x01b42a6ca1a34998 0xb806d0a9b2868d26 0xb9f03e78e1e3d9ed 0xaee7c0f9e3878f67

def z1054 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffff803d82f 0xffffffffffe00f60

def z1055 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xc7ffc0009ffc0014 0x7b1fff00027ff000

def z1056 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0x51ffc000e7fc0000 0x6147ff00039ff000

def z1057 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xffffff80ffffc03f 0xfffffffe03ffff00

def z1058 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc1ffe07f00000000 0xe707ff81fc000000

def z1059 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xfffffe00fffff83f 0xfffffff803ffffe0

def z1060 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x59ffc000e1fc0000 0x6967ff000387f000

def z1061 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6bffffff00000003 0xe9affffffc000000

def z1062 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f01878e1e1c1e5 0xaae7c061e3878707

def z1063 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc3ffc1ff86012637 0xfb0fff07fe180498

def z1064 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff071d27f3 0xf00a0707fc1c749f

def z1065 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0xd9ffc000fffc001c 0x6f67ff0003fff000

def z1066 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc9ffc00001fc0000 0x6f27ff000007f000

def z1067 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff871d27f7 0x880a0707fe1c749f

def z1068 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc7ffe7ff00000003 0xff1fff9ffc000000

def z1069 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xefffffff8603fe37 0xffbffffffe180ff8

def z1070 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff871d07c3 0xfa0a0707fe1c741f

def z1071 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xdd0e2647f9fe39fe 0xff7438991fe7f8e7

def z1072 : W := mkw 0x0ed94000a3880000 0x803b6500028e2000 0xdfffc000e7fc001c 0x7f7fff00039ff000

def z1073 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e264719fe19ca 0xf71438991c67f867

def z1074 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc00079fc0008 0x7f7fff0001e7f000

def z1075 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0xa281f9ff871fe7f7 0xfa8a07e7fe1c7f9f

def z1076 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbdf03e78f9e3d9ed 0xaef7c0f9e3e78f67

def z1077 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5f7fc000fffc001c 0x557dff0003fff000

def z1078 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8681e7ff871d27f7 0xfe1a079ffe1c749f

def z1079 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0xd5ffc000fffc001c 0x7757ff0003fff000

def z1080 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc5ffc00001fc0000 0x7717ff000007f000

def z1081 : W := mkw 0x0f69a8f200000014 0x003da6a3c8000000 0xeffff9ff00000003 0xffbfffe7fc000000

def z1082 : W := mkw 0x00b00828a1a34180 0xb002c020a2868d06 0xb9f01838e1e3c1ed 0x2ee7c060e3878f07

def z1083 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff010001e7 0xffbffffffc040007

def z1084 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xddffc000f9fc001c 0x7f77ff0003e7f000

def z1085 : W := mkw 0x2f6dbff60022013e 0x20bdb6ffd8008804 0xefffffff19e239ff 0xffbffffffc6788e7

def z1086 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc078fffc001d 0xff7fff01e3fff000

def z1087 : W := mkw 0x10db4000ffd80001 0xc0436d0003ff6000 0xd3ffc000fffc001c 0x7b4fff0003fff000

def z1088 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0xc3ffc00001fc0000 0x7b0fff000007f000

def z1089 : W := mkw 0x0124aaff00276bdc 0x3c0492abfc009daf 0x20003fff0003ffe3 0x808000fffc000fff

def z1090 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xefffffff1e023e3f 0xffbffffffc7808f8

def z1091 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f03878e1e3c1c9 0x2ce7c0e1e3878f07

def z1092 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc180fffc261e 0x7f7fff0603fff098

def z1093 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xc3ffc07f00000000 0x7b0fff01fc000000

def z1094 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff071c27f6 0xf20a0707fc1c709f

def z1095 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xfffffe00fffffe3c 0x7ffffff803fffff8

def z1096 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffffe601e637 0xffffffffff980798

def z1097 : W := mkw 0x2124bfff002763fe 0x348492fffc009d8f 0x20003fff0003e7e3 0x808000fffc000f9f

def z1098 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0x7bffd980e7fdc601 0x69efff66039ff718

def z1099 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc70e26479ffe39fe 0xff1c38991e7ff8e7

def z1100 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0x7dfffe0079fed808 0x65f7fff801e7fb60

def z1101 : W := mkw 0x216daaf60022011e 0x2085b6abd8008804 0x41ffc07f01e001c0 0x6107ff01fc078007

def z1102 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0x47ffc07f00000000 0x711fff01fc000000

def z1103 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xddffc000f9fc000c 0x6f77ff0003e7f000

def z1104 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xe50e3e4719fff9ff 0xf79438f91c67ffe7

def z1105 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffe600fffc001e 0xff7fff9803fff000

def z1106 : W := mkw 0x2e699db200000026 0x00b9a676c8000000 0xefffd9ff00000003 0xffbfff67fc000000

def z1107 : W := mkw 0x0e4b150008500020 0x40392c5400214000 0xefffff8019fe383f 0xffbffffe0067f8e0

def z1108 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0xeffff87f00000001 0xffbfffe1fc000000

def z1109 : W := mkw 0x00b00828a1814080 0x9002c020a2860502 0xb9f01878e1e1c1ed 0xaee7c061e3878707

def z1110 : W := mkw 0x1e5b55007ed89421 0xc0796d5401fb6250 0x7f7fff807efefe1a 0x55fdfffe01fbfbf8

def z1111 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffff7e02fe1b 0xfffffffffdf80bf8

def z1112 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x440e264719fe39fe 0xd11038991c67f8e7

def z1113 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xb9f03878e1e2c1cc 0x2ee7c0e1e3878b07

def z1114 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5dffc000fffc001c 0x6577ff0003fff000

def z1115 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0x4dffc00001fc0000 0x6537ff000007f000

def z1116 : W := mkw 0x1e5b40007ed80001 0xc0796d0001fb6000 0x5d7fc00078fc0008 0x4575ff0001e3f000

def z1117 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x43ffc00007fc0000 0x610fff00001ff000

def z1118 : W := mkw 0x0000150054009421 0x0000005401500250 0xb2003f80fe03fe3f 0x9ac800fe03f80ff8

def z1119 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0xba81d9ffe71de7f7 0xfaea0767ff9c779f

def z1120 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5bffc000fffc001c 0x696fff0003fff000

def z1121 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0x4bffc00001fc0000 0x692fff000007f000

def z1122 : W := mkw 0x2f6dbff60022093e 0x28bdb6ffd8008824 0xefffffff00021803 0xffbffffffc000860

def z1123 : W := mkw 0x1e5b40007ed80001 0xc0796d0001fb6000 0xdfffc0007efc0018 0x7f7fff0001fbf000

def z1124 : W := mkw 0x0106224508762958 0x680418891421d8a5 0x450e264719fe39ea 0xe51438991c67f8e7

def z1125 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xefffffff00023823 0xffbffffffc0008e0

def z1126 : W := mkw 0x105b40002ad80000 0xc0416d0000ab6000 0x417fc00000fc0000 0x4105ff000003f000

def z1127 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x41ffc00087fc0014 0x6107ff00021ff000

def z1128 : W := mkw 0x216daaf60000001e 0x0085b6abd8000000 0xf9fff87fe003c02d 0xefe7ffe1ff800f00

def z1129 : W := mkw 0x0000c09b020d22c4 0x040003026c08348b 0x0201c1ff061c27d2 0x50080707fc18709f

def z1130 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbe003f80ff1ffe3f 0xfef800fe03fc7ff8

def z1131 : W := mkw 0x2f6dbff60022013e 0x20bdb6ffd8008804 0xffffffffe1e3c1ef 0xffffffffff878f07

def z1132 : W := mkw 0x2f6dbff60000943e 0x00bdb6ffd8000250 0xefffffff0001c603 0xffbffffffc000718

def z1133 : W := mkw 0x0006020508762948 0x680018081421d8a5 0x440e060719fc39d2 0x511038181c67f0e7

def z1134 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e27c719ff3fff 0xf714389f1c67fcff

def z1135 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x57ffc000fffc001c 0x715fff0003fff000

def z1136 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xd50e2647f9fff9fe 0xf75438991fe7ffe7

def z1137 : W := mkw 0x1edb4000abd80000 0xc07b6d0002af6000 0x47ffc00001fc0000 0x711fff000007f000

def z1138 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x0281c1ff871d27d3 0x780a0707fe1c749f

def z1139 : W := mkw 0x2f6dbff65422953f 0x20bdb6ffd9508a54 0xffffffffffe3ffff 0xffffffffffff8fff

def z1140 : W := mkw 0x10db4000abd80000 0xc0436d0002af6000 0x59ffc00061fc0008 0x6567ff000187f000

def z1141 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe003f80fe03fe3f 0x9ef800fe03f80ff8

def z1142 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbdf03878f9e3c1fd 0xbef7c0e1e3e78f07

def z1143 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8381c1ff87fd27ff 0xfe0e0707fe1ff49f

def z1144 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6effffff00000003 0xd9bbfffffc000000

def z1145 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xebffd9ff00000003 0xfbafff67fc000000

def z1146 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6fffffff00000001 0x6dbffffffc000000

def z1147 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5fffc000fffc0010 0x797fff0003fff000

def z1148 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0x8281c1ff871c27d6 0x7a0a0707fe1c709f

def z1149 : W := mkw 0x1e5b40007ed80001 0xc0796d0001fb6000 0xdf7fc0007ffc001c 0x777dff0001fff000

def z1150 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xcfffc0001ffc0010 0x7f3fff00007ff000

def z1151 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xffffff80ffffde1d 0x7ffffffe03ffff78

def z1152 : W := mkw 0x2e6d9fb65400942f 0x00b9b67ed9500250 0x7effdfbffe01fe13 0x59fbff7efff807f8

def z1153 : W := mkw 0x2f6daaf60000001e 0x00bdb6abd8000000 0xcfffe67f00000002 0xff3fff99fc000000

def z1154 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffe000fffe003c 0xff7fff8003fff800

def z1155 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3a003f80fe03fe3f 0x88e800fe03f80ff8

def z1156 : W := mkw 0x2f6dbff60022013e 0x20bdb6ffd8008804 0xefffffff00e2000b 0xffbffffffc038800

def z1157 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffffe603fe23 0xffffffffff980ff8

def z1158 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffffe02d81f 0xfffffffffff80b60

def z1159 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdbffc000e7fc0014 0x7b6fff00039ff000

def z1160 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbbf03878e7e3c1fd 0xbeefc0e1e39f8f07

def z1161 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0x39f01878e1e3c1ed 0x28e7c061e3878f07

def z1162 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0x5fffc000fffc001c 0x0d7fff0003fff000

def z1163 : W := mkw 0x1edb4008ffd90081 0xc07b6d0023ff6402 0xdfffc000fffd01fc 0x7f7fff0003fff407

def z1164 : W := mkw 0x0e00150054009421 0x0038005401500250 0xbf003f80ffe3fe3f 0xbefc00fe03ff8ff8

def z1165 : W := mkw 0x1edb5500ffd80021 0xc07b6d5403ff6000 0xdfffc780fffc001e 0x7f7fff1e03fff000

def z1166 : W := mkw 0x10924009ffff2bc1 0xec42490027fffcaf 0x10000000ffff3ffc 0x0040000003fffcff

def z1167 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xc7ffc7ff00000003 0xfb1fff1ffc000000

def z1168 : W := mkw 0x0006020508762948 0x680018081421d8a5 0xc40e064719fe39fe 0xf31038191c67f8e7

def z1169 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xdfffc600fffc381e 0x7f7fff1803fff0e0

def z1170 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xfffffffffe003e1f 0xfffffffffff800f8

def z1171 : W := mkw 0x1e925509ffddb6e1 0xc47a495427ff76db 0xbe003f80ffffffff 0x9ef800fe03ffffff

def z1172 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xffffffffe603e63f 0xffffffffff980f98

def z1173 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0xedfffe7f00000002 0xf7b7fff9fc000000

def z1174 : W := mkw 0x2f6dbff60000003e 0x00bdb6ffd8000000 0x6fffffbf00000003 0x5dbffffefc000000

def z1175 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0xbe81ffffff1fffff 0xfefa07fffffc7fff

def z1176 : W := mkw 0x01b02868a1a34190 0xb006c0a1a2868d06 0xbdf03e78e1e3c1ef 0xbef7c0f9e3878f07

def z1177 : W := mkw 0x0106224508762958 0x680418891421d8a5 0xc50e064719fc39de 0x771438191c67f0e7

def z1178 : W := mkw 0x2f6dbff65400943f 0x00bdb6ffd9500250 0xffffffff7802f83f 0xfffffffffde00be0

def z1179 : W := mkw 0x10924009ffff69c1 0xf842490027fffda7 0x10000000fffff9fc 0x0040000003ffffe7

def z1180 : W := mkw 0x0080c09b830d22c4 0x040203026e0c348b 0xaa81f9ff871d27f7 0xfeaa07e7fe1c749f

def z1181 : W := mkw 0x0e00150054009421 0x0038005401500250 0x3e003f80fe03fe3d 0x0cf800fe03f80ff8

def z1182 : W := mkw 0x1edb5500ffd89421 0xc07b6d5403ff6250 0xdfffe780fffe3e3e 0xff7fff9e03fff8f8

def z1183 : W := mkw 0x2f24bff75426bd7f 0x28bc92ffdd509af5 0xbe003ffffe03ffff 0x9ef800fffff80fff

def z1184 : W := mkw 0x1edb4000ffd80001 0xc07b6d0003ff6000 0xfffff800fffc001d 0xffffffe003fff000

def z1185 : W := mkw 0x1e5b40007ed80001 0xc0796d0001fb6000 0x477fc0001efc0010 0x511dff00007bf000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z0,z1,z8,z2,z3,z9,z6]),(0,[z0,z10,z1,z2,z3,z11,z6]),(0,[z0,z1,z12,z2,z3,z5,z6])],[(0,[z0,z13,z1,z2,z3,z5,z6]),(0,[z14,z1,z2,z3,z5,z6,z15]),(0,[z0,z1,z16,z2,z3,z5,z6])],[(0,[z1,z2,z3,z17,z5,z18,z6]),(1,[z0,z1,z2,z3,z5,z19]),(1,[z0,z1,z2,z11,z6,z20]),(0,[z0,z1,z21,z2,z3,z5,z6])],[(0,[z22,z0,z1,z2,z3,z5,z6])],[(0,[z0,z23,z1,z2,z3,z9,z6]),(0,[z24,z0,z1,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z9,z6]),(0,[z0,z1,z2,z3,z26,z9,z6])],[(0,[z0,z27,z1,z2,z3,z5,z6]),(0,[z28,z0,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z3,z5,z30,z6]),(0,[z31,z0,z1,z2,z3,z5,z32])],[(0,[z33,z1,z2,z3,z34,z5,z6]),(0,[z14,z0,z1,z2,z3,z26,z5]),(1,[z0,z1,z2,z3,z5,z35]),(0,[z36,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z37,z32]),(0,[z0,z1,z2,z3,z5,z38,z6])],[(0,[z0,z39,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z41,z3,z5,z20]),(0,[z0,z42,z1,z2,z3,z5,z6]),(0,[z0,z43,z1,z2,z3,z5,z6]),(0,[z0,z42,z2,z44,z3,z5,z6]),(0,[z0,z43,z2,z44,z3,z5,z6]),(0,[z45,z0,z1,z2,z3,z5,z6]),(0,[z46,z0,z1,z2,z3,z11,z6]),(0,[z47,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z48]),(0,[z0,z1,z2,z3,z49,z5,z6]),(1,[z36,z0,z1,z2,z9,z6]),(0,[z36,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z50,z6])]],
   [[(0,[z51,z0,z1,z2,z3,z9,z6]),(0,[z46,z0,z1,z2,z3,z5,z32]),(0,[z0,z10,z43,z1,z3,z5,z6]),(0,[z24,z52,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z2,z53,z5,z6]),(0,[z54,z55,z1,z2,z3,z5,z6])],[(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z0,z58,z1,z2,z3,z59,z6]),(0,[z0,z1,z2,z60,z3,z5,z6])],[(0,[z0,z61,z1,z2,z3,z5,z32])],[(0,[z1,z2,z3,z5,z62,z6,z15]),(0,[z0,z1,z2,z3,z5,z63,z6]),(0,[z0,z1,z2,z64,z3,z5,z6]),(0,[z0,z1,z2,z65,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z66,z6]),(0,[z0,z67,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z6,z68])],[(0,[z69,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z70,z2,z3,z5,z6]),(0,[z71,z0,z1,z2,z3,z5,z6]),(0,[z72,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z73,z9,z6])],[(0,[z74,z0,z1,z2,z3,z11,z6]),(0,[z0,z58,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z75,z3,z5,z6])],[(0,[z74,z0,z1,z2,z3,z5,z32]),(0,[z76,z0,z1,z2,z3,z5,z6]),(0,[z0,z58,z1,z2,z3,z5,z32]),(0,[z77,z0,z1,z2,z3,z9,z6]),(1,[z0,z1,z2,z5,z32,z20])],[(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z79,z1,z2,z3,z5,z6]),(0,[z14,z0,z1,z2,z3,z5,z62]),(0,[z46,z0,z43,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z80]),(0,[z0,z1,z2,z81,z3,z5,z82]),(0,[z0,z1,z83,z2,z3,z5,z6])]],
   [[(0,[z84,z0,z1,z2,z3,z5,z6]),(0,[z85,z0,z1,z2,z3,z5,z6]),(1,[z86,z0,z2,z3,z5,z6]),(0,[z0,z87,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z88,z3,z5,z6])],[(0,[z51,z0,z61,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z17,z5,z6]),(1,[z0,z1,z2,z3,z89,z6])],[(1,[z33,z1,z2,z34,z5,z6]),(0,[z0,z1,z2,z3,z90,z5,z6]),(0,[z0,z1,z2,z3,z91,z9,z6]),(0,[z0,z1,z2,z3,z5,z92,z6]),(0,[z0,z1,z2,z3,z26,z6,z68])],[(0,[z93,z74,z1,z2,z3,z5,z6]),(0,[z0,z94,z1,z2,z3,z5,z6]),(0,[z0,z95,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z96,z3,z5,z6])],[(1,[z97,z1,z41,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z2,z3,z5,z18,z32])],[(0,[z0,z1,z2,z3,z5,z6,z99]),(0,[z0,z1,z25,z2,z53,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z82]),(0,[z0,z1,z3,z100,z5,z101,z6]),(0,[z0,z1,z2,z3,z5,z102,z20]),(0,[z0,z1,z2,z103,z3,z9,z6]),(0,[z0,z1,z2,z103,z3,z104,z6]),(0,[z0,z1,z2,z3,z5,z32,z105])],[(0,[z106,z1,z2,z41,z3,z5,z6]),(0,[z0,z1,z2,z107,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z29]),(1,[z0,z23,z2,z3,z5,z108]),(0,[z0,z1,z2,z3,z5,z32,z68])]],
   [[(0,[z109,z1,z2,z3,z5,z18,z6]),(0,[z46,z0,z110,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z20]),(1,[z0,z1,z2,z3,z9,z20]),(0,[z0,z1,z2,z3,z111,z5,z6])],[(0,[z33,z0,z1,z2,z3,z5,z32]),(0,[z46,z0,z1,z2,z3,z5,z20]),(0,[z112,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z113,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z114,z5,z6])],[(0,[z0,z61,z110,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z6,z15]),(0,[z0,z1,z2,z3,z5,z32,z62]),(0,[z115,z0,z1,z2,z3,z5,z6]),(0,[z112,z0,z2,z3,z5,z59,z6]),(0,[z0,z58,z1,z2,z3,z38,z6]),(0,[z0,z1,z116,z2,z3,z5,z6]),(0,[z117,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z118])],[(0,[z0,z61,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z119,z3,z5,z6]),(0,[z0,z1,z2,z120,z3,z5,z6])],[(0,[z0,z1,z121,z3,z53,z5,z6]),(0,[z0,z1,z2,z3,z5,z122,z6]),(1,[z74,z1,z2,z123,z5,z6]),(0,[z0,z1,z2,z3,z124,z5,z6]),(0,[z125,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z9,z100,z6]),(0,[z0,z1,z2,z3,z5,z126,z6]),(0,[z0,z1,z2,z3,z127,z5,z6])],[(0,[z0,z1,z2,z3,z128,z5,z6]),(0,[z129,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z41,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z125,z0,z1,z2,z3,z5,z32])],[(0,[z0,z1,z2,z3,z5,z130,z6]),(0,[z131,z0,z1,z2,z3,z5,z6]),(0,[z97,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z132,z2,z3,z5,z6]),(0,[z0,z110,z2,z133,z3,z5,z6]),(0,[z0,z134,z1,z2,z3,z5,z6])],[(0,[z74,z0,z1,z2,z3,z5,z20]),(0,[z0,z58,z1,z2,z3,z5,z20]),(0,[z135,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z6,z20]),(0,[z0,z1,z2,z3,z5,z136,z20])]],
   [[(0,[z1,z2,z41,z3,z5,z18,z6]),(0,[z93,z1,z121,z2,z3,z5,z6]),(0,[z109,z0,z1,z137,z3,z5,z6]),(0,[z28,z0,z1,z138,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z139,z6]),(0,[z0,z1,z2,z3,z9,z140,z6]),(0,[z0,z1,z2,z3,z5,z141,z6])],[(0,[z142,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z17,z101,z6]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z144]),(1,[z24,z0,z1,z53,z5,z6]),(0,[z0,z1,z2,z3,z5,z145,z6]),(0,[z0,z1,z2,z3,z146,z5,z6])],[(0,[z0,z1,z2,z147,z3,z5,z6]),(0,[z0,z1,z2,z3,z148,z5,z6])],[(1,[z0,z1,z2,z3,z149,z5]),(0,[z0,z1,z2,z150,z3,z5,z6])],[(0,[z0,z1,z2,z81,z3,z90,z6]),(0,[z55,z151,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z5,z6])],[(0,[z0,z1,z121,z2,z3,z9,z6]),(0,[z33,z74,z1,z2,z3,z5,z6]),(0,[z0,z1,z152,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z18,z20]),(0,[z0,z1,z153,z2,z3,z5,z6])],[(0,[z28,z0,z1,z2,z3,z11,z6]),(0,[z24,z0,z1,z2,z3,z89,z6]),(0,[z0,z1,z2,z3,z11,z6,z154])]],
   [[(0,[z0,z1,z2,z3,z5,z155,z6]),(0,[z0,z1,z2,z3,z156,z5,z6]),(0,[z125,z0,z1,z2,z3,z5,z157]),(0,[z0,z1,z2,z3,z5,z6,z158])],[(0,[z0,z159,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z37,z6])],[(0,[z33,z0,z1,z2,z3,z5,z20]),(0,[z160,z0,z1,z2,z3,z161,z5]),(0,[z0,z1,z2,z3,z11,z6,z162]),(1,[z0,z10,z1,z3,z5,z102]),(0,[z0,z1,z2,z3,z163,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z164,z6]),(0,[z0,z1,z2,z3,z165,z5,z6]),(0,[z166,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z167,z6]),(0,[z0,z1,z2,z3,z168,z5,z6]),(0,[z46,z0,z1,z2,z3,z5,z6]),(0,[z0,z169,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z170,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z11,z6]),(0,[z171,z0,z1,z2,z3,z11,z6]),(0,[z0,z172,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z32,z20]),(0,[z0,z1,z2,z3,z5,z63,z32])],[(1,[z0,z1,z2,z3,z5,z173]),(0,[z24,z0,z1,z2,z81,z5,z6]),(0,[z0,z1,z2,z81,z3,z5,z32]),(1,[z0,z1,z8,z3,z5,z162]),(0,[z31,z0,z1,z2,z3,z9,z6])],[(0,[z0,z1,z2,z3,z174,z5,z6]),(0,[z0,z23,z1,z175,z3,z5,z6]),(0,[z0,z1,z2,z3,z176,z5,z6]),(0,[z0,z1,z2,z3,z5,z177,z20])],[(0,[z125,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z161,z9,z6]),(0,[z0,z178,z1,z2,z3,z5,z6])],[(0,[z93,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z179,z5,z6]),(0,[z0,z1,z2,z3,z53,z11,z6]),(0,[z0,z1,z2,z81,z3,z5,z139]),(0,[z0,z1,z2,z3,z180,z5,z6])]],
   [[(0,[z181,z0,z1,z2,z3,z5,z6]),(0,[z14,z160,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z182]),(1,[z0,z1,z2,z3,z183,z6]),(0,[z0,z1,z2,z3,z5,z20,z108]),(0,[z0,z1,z2,z3,z5,z184,z6]),(0,[z0,z1,z2,z3,z53,z5,z32]),(0,[z0,z1,z2,z3,z185,z5,z6]),(0,[z0,z1,z2,z3,z38,z6,z68])],[(0,[z0,z1,z186,z2,z3,z5,z6]),(0,[z74,z0,z1,z2,z3,z5,z6]),(0,[z0,z58,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z187,z6]),(0,[z188,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z136,z6])],[(0,[z0,z1,z189,z2,z3,z11,z6]),(0,[z190,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z132,z3,z5,z6]),(0,[z0,z1,z2,z3,z17,z5,z32]),(0,[z191,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z138,z3,z5,z6])],[(0,[z192,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z193,z6]),(0,[z0,z194,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z195,z6]),(0,[z196,z0,z1,z2,z3,z9,z6]),(0,[z197,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z198,z5,z6])],[(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z200,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z201,z6,z108]),(0,[z0,z1,z202,z2,z3,z9,z6]),(0,[z203,z0,z1,z2,z3,z11,z6])],[(0,[z0,z1,z204,z2,z3,z5,z6]),(0,[z0,z1,z2,z123,z3,z11,z6]),(0,[z0,z1,z2,z3,z205,z5,z6]),(0,[z14,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z8,z3,z5,z6,z162]),(0,[z0,z1,z2,z3,z5,z32,z162])],[(0,[z0,z1,z2,z3,z206,z5,z6]),(0,[z0,z207,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z3,z5,z102,z6]),(0,[z0,z1,z2,z3,z208,z11,z6]),(0,[z0,z1,z2,z3,z209,z5,z20])]],
   [[(0,[z0,z1,z2,z3,z168,z5,z18])],[(0,[z0,z1,z2,z3,z5,z98,z6]),(0,[z0,z1,z2,z210,z3,z5,z6])],[(0,[z211,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z137,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z212,z6]),(0,[z0,z213,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z214,z6]),(0,[z0,z1,z25,z2,z81,z5,z6])],[(0,[z0,z1,z2,z3,z215,z5,z6]),(0,[z0,z1,z2,z133,z3,z11,z6]),(0,[z0,z58,z1,z2,z3,z124,z6]),(0,[z216,z0,z1,z2,z3,z5,z6])],[(0,[z33,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z32]),(0,[z0,z1,z2,z3,z124,z5,z32]),(0,[z0,z217,z1,z2,z3,z5,z6])],[(0,[z218,z0,z1,z2,z3,z5,z6]),(1,[z46,z0,z43,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z5,z20]),(0,[z219,z0,z1,z2,z3,z5,z6]),(0,[z220,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z20,z221])],[(0,[z0,z1,z2,z3,z5,z6,z222]),(0,[z0,z1,z2,z3,z223,z5,z6]),(0,[z0,z224,z1,z2,z3,z5,z6]),(0,[z0,z55,z1,z2,z3,z100,z6]),(0,[z225,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z9,z11,z6])],[(0,[z0,z1,z2,z3,z226,z9,z6]),(0,[z0,z1,z2,z3,z227,z6,z108])]],
   [[(0,[z0,z1,z228,z2,z3,z5,z6]),(0,[z125,z0,z2,z44,z3,z5,z6]),(0,[z125,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z229,z6]),(0,[z0,z1,z2,z3,z230,z5,z6]),(0,[z0,z1,z2,z3,z5,z231,z32])],[(0,[z51,z232,z1,z2,z3,z5,z6]),(0,[z233,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z123,z3,z34,z5,z6]),(0,[z0,z1,z137,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z234,z6]),(0,[z0,z1,z2,z3,z53,z5,z20])],[(0,[z97,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z235]),(0,[z28,z0,z1,z2,z3,z236,z6]),(0,[z0,z1,z2,z175,z3,z5,z6]),(1,[z0,z1,z202,z3,z100,z6]),(0,[z0,z237,z1,z2,z3,z9,z6])],[(0,[z0,z1,z2,z3,z5,z238,z6]),(0,[z0,z1,z2,z3,z17,z5,z20]),(0,[z239,z0,z1,z2,z3,z5,z6]),(0,[z240,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z241,z6])],[(0,[z0,z1,z242,z2,z3,z5,z6]),(0,[z0,z243,z1,z2,z3,z5,z6]),(0,[z0,z244,z1,z2,z3,z5,z6]),(0,[z245,z0,z1,z2,z3,z5,z6]),(0,[z125,z0,z2,z3,z5,z157,z6]),(0,[z0,z1,z2,z3,z5,z246,z6]),(0,[z0,z10,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z247,z6]),(0,[z0,z1,z2,z3,z5,z32,z102]),(0,[z0,z1,z2,z3,z5,z6,z20]),(0,[z0,z1,z2,z3,z5,z32,z248])],[(0,[z232,z0,z1,z2,z3,z11,z6]),(0,[z109,z0,z1,z249,z3,z5,z6]),(0,[z0,z1,z2,z3,z250,z5,z6]),(0,[z0,z43,z1,z3,z53,z5,z6]),(0,[z24,z251,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z252,z5,z6])],[(0,[z97,z0,z1,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z253,z6]),(0,[z0,z1,z2,z3,z5,z254,z6]),(0,[z36,z0,z1,z2,z3,z5,z255])],[(0,[z0,z1,z2,z3,z256,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z221]),(0,[z0,z1,z2,z3,z9,z102,z6]),(1,[z0,z1,z2,z3,z5,z257])]],
   [[(0,[z0,z1,z258,z2,z3,z5,z6]),(0,[z0,z259,z1,z2,z3,z5,z6]),(0,[z0,z110,z1,z2,z3,z11,z6]),(0,[z260,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z20,z80])],[(0,[z0,z110,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z261,z5,z6]),(0,[z0,z1,z2,z3,z11,z157,z6]),(0,[z0,z1,z2,z3,z209,z5,z6]),(0,[z0,z1,z2,z3,z111,z5,z20]),(0,[z0,z262,z1,z2,z3,z5,z6])],[(0,[z0,z1,z263,z2,z3,z5,z6]),(0,[z0,z23,z2,z3,z5,z6,z108]),(0,[z264,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z265,z5,z6])],[(0,[z28,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z101,z6]),(0,[z0,z1,z2,z3,z266,z5,z6])],[(0,[z267,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z34,z11,z6]),(0,[z0,z1,z2,z3,z268,z5,z6]),(0,[z0,z58,z1,z2,z3,z26,z6])],[(1,[z93,z1,z121,z3,z5,z6]),(1,[z28,z0,z2,z226,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z20]),(0,[z0,z1,z2,z3,z124,z5,z20]),(0,[z0,z1,z2,z3,z269,z5,z6])],[(0,[z270,z0,z1,z2,z3,z5,z6]),(0,[z33,z0,z271,z2,z3,z5,z6]),(0,[z272,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z273,z2,z3,z5,z6]),(0,[z0,z42,z1,z2,z3,z9,z6]),(0,[z0,z43,z1,z2,z3,z9,z6]),(0,[z24,z0,z1,z2,z3,z11,z6]),(0,[z0,z274,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z275,z3,z5,z6]),(0,[z276,z0,z1,z2,z3,z5,z6]),(0,[z0,z172,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z5,z6]),(0,[z171,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z54,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z277]),(0,[z0,z1,z2,z3,z5,z278,z6])],[(0,[z279,z0,z1,z2,z3,z5,z6]),(0,[z14,z0,z1,z2,z3,z5,z15])],[(0,[z0,z1,z2,z3,z5,z6,z280]),(0,[z0,z1,z2,z3,z281,z5,z6]),(0,[z0,z1,z8,z2,z3,z11,z6])],[(0,[z0,z1,z2,z3,z282,z5,z6]),(0,[z0,z1,z2,z3,z5,z283,z6]),(0,[z0,z284,z1,z2,z3,z5,z6]),(0,[z106,z1,z2,z3,z17,z5,z6]),(0,[z0,z285,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z286,z5,z6]),(0,[z0,z1,z2,z3,z53,z5,z6]),(0,[z287,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z288,z6]),(1,[z0,z1,z2,z3,z5,z289]),(0,[z0,z1,z290,z2,z3,z5,z6])],[(0,[z232,z0,z189,z2,z3,z5,z6]),(0,[z0,z1,z2,z291,z3,z5,z6]),(0,[z0,z1,z292,z2,z3,z5,z6]),(0,[z293,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z62,z6]),(0,[z0,z1,z2,z3,z5,z294,z6]),(0,[z0,z1,z295,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z5,z20])],[(0,[z0,z1,z189,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z103,z5,z6,z20])],[(0,[z296,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z18,z6]),(0,[z0,z297,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z59,z6]),(0,[z0,z1,z2,z3,z5,z6,z298]),(0,[z0,z299,z1,z2,z3,z11,z6])]],
   [[(0,[z0,z110,z189,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z300,z5,z6])],[(0,[z93,z97,z1,z2,z3,z5,z6]),(0,[z0,z301,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z302,z6]),(0,[z0,z1,z2,z3,z9,z6,z108]),(1,[z0,z1,z2,z3,z11,z32]),(0,[z203,z0,z1,z2,z3,z5,z6]),(0,[z203,z0,z1,z2,z3,z303,z6]),(0,[z304,z0,z1,z2,z3,z5,z32])],[(0,[z0,z1,z2,z305,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z306,z6]),(0,[z160,z0,z1,z2,z3,z11,z6]),(0,[z307,z0,z1,z2,z3,z5,z6]),(0,[z0,z110,z1,z2,z3,z5,z20]),(0,[z0,z1,z308,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z309,z5,z6]),(1,[z0,z1,z2,z3,z161,z38])],[(0,[z310,z0,z1,z2,z3,z5,z6]),(0,[z160,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z25,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z201,z5,z6]),(0,[z0,z1,z2,z3,z9,z11,z6]),(0,[z0,z1,z2,z3,z208,z5,z6])],[(0,[z311,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z312]),(0,[z24,z0,z213,z2,z3,z5,z6]),(0,[z0,z1,z25,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z9,z180,z6]),(0,[z0,z1,z2,z3,z9,z32,z6]),(0,[z0,z1,z2,z3,z9,z5,z32])],[(0,[z93,z0,z1,z121,z3,z5,z6]),(0,[z0,z1,z2,z123,z3,z313,z6]),(0,[z0,z1,z2,z3,z5,z314,z6]),(0,[z315,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z29,z6]),(0,[z0,z1,z2,z3,z5,z316,z6]),(0,[z0,z1,z2,z317,z3,z5,z6]),(0,[z0,z318,z1,z2,z3,z5,z6])],[(0,[z319,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z320,z6]),(0,[z0,z1,z2,z3,z5,z6,z321])],[(0,[z322,z0,z1,z2,z3,z5,z6]),(0,[z323,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z123,z3,z324,z6]),(1,[z0,z1,z249,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z325,z6]),(0,[z0,z1,z2,z3,z326,z5,z6]),(0,[z0,z2,z44,z3,z226,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z6]),(0,[z0,z1,z2,z327,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z313,z6]),(0,[z0,z1,z2,z3,z9,z17,z6]),(0,[z328,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z82]),(0,[z0,z10,z1,z2,z3,z5,z162]),(0,[z77,z0,z1,z2,z3,z11,z6])],[(0,[z74,z1,z2,z41,z3,z5,z6]),(0,[z329,z0,z1,z2,z3,z5,z6]),(0,[z330,z0,z1,z2,z3,z5,z6]),(1,[z203,z0,z1,z2,z11,z6]),(0,[z220,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z331]),(0,[z0,z1,z2,z3,z332,z5,z6]),(0,[z97,z0,z1,z2,z3,z5,z32]),(0,[z109,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z333,z5,z6]),(0,[z0,z1,z2,z3,z334,z5,z6])],[(0,[z335,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z121,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z336,z5,z6]),(0,[z0,z1,z2,z81,z3,z187,z6]),(0,[z0,z55,z1,z202,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z337,z6]),(0,[z0,z1,z2,z3,z5,z231,z6])],[(0,[z0,z1,z2,z338,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z339,z6]),(0,[z28,z0,z1,z2,z3,z5,z340]),(0,[z0,z1,z2,z3,z5,z6,z341])],[(0,[z0,z1,z2,z3,z5,z342,z6])],[(0,[z343,z0,z1,z2,z3,z5,z6]),(0,[z344,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z345,z2,z3,z5,z6]),(1,[z125,z0,z2,z3,z5,z157]),(0,[z0,z1,z346,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z347,z5,z6])],[(0,[z0,z1,z2,z3,z5,z348,z6]),(0,[z0,z1,z2,z3,z5,z349,z6])]],
   [[(1,[z0,z1,z2,z3,z214,z6]),(0,[z0,z1,z2,z3,z9,z38,z6])],[(0,[z232,z0,z1,z2,z3,z5,z6]),(0,[z0,z42,z1,z2,z3,z5,z19]),(0,[z28,z0,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z3,z5,z350,z6]),(0,[z0,z1,z2,z351,z3,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z352,z5,z6]),(1,[z14,z1,z2,z3,z5,z15]),(0,[z0,z1,z2,z353,z3,z5,z6]),(1,[z0,z1,z2,z3,z11,z20]),(0,[z354,z0,z1,z2,z3,z5,z20])],[(0,[z28,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z355,z5,z6]),(0,[z0,z1,z356,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z9,z5,z11,z6])],[(0,[z160,z0,z1,z2,z3,z5,z20]),(0,[z0,z110,z2,z44,z3,z5,z6]),(0,[z0,z110,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z357,z5,z6])],[(0,[z0,z55,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z9,z5,z20]),(0,[z0,z217,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z26,z161,z6])],[(0,[z0,z1,z2,z3,z5,z6,z358]),(0,[z0,z1,z2,z3,z5,z157,z6]),(0,[z0,z1,z359,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z5,z102]),(0,[z360,z0,z1,z2,z3,z5,z6])],[(0,[z361,z0,z1,z2,z3,z5,z6]),(0,[z362,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z363,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z340]),(0,[z24,z0,z1,z2,z3,z5,z184]),(0,[z0,z1,z364,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z121,z25,z3,z5,z6]),(0,[z0,z1,z365,z2,z3,z5,z6])],[(1,[z232,z61,z2,z3,z5,z6]),(0,[z0,z1,z2,z366,z3,z5,z6]),(0,[z28,z367,z1,z2,z3,z5,z6]),(0,[z0,z368,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z369,z5,z6]),(0,[z370,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z371,z11,z6]),(0,[z36,z0,z1,z2,z3,z9,z6])],[(0,[z372,z0,z1,z2,z3,z5,z6]),(0,[z46,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z373,z2,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z158]),(0,[z0,z1,z2,z3,z5,z6,z255]),(0,[z0,z1,z2,z103,z3,z241,z6])],[(0,[z97,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z374,z3,z5,z6]),(0,[z0,z1,z2,z3,z375,z5,z6]),(0,[z28,z376,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z157,z6,z108]),(1,[z251,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z68]),(0,[z377,z0,z1,z2,z3,z5,z6])],[(0,[z0,z61,z1,z2,z3,z9,z6]),(0,[z109,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z6,z378]),(0,[z379,z0,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z8,z3,z5,z6])],[(0,[z0,z380,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z90,z6]),(0,[z0,z55,z1,z3,z5,z101,z6])],[(0,[z0,z1,z189,z2,z3,z5,z32]),(0,[z232,z1,z2,z3,z34,z5,z6]),(0,[z381,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z382,z6]),(0,[z0,z1,z2,z3,z383,z5,z6]),(0,[z0,z1,z2,z3,z384,z5,z6]),(0,[z385,z0,z1,z2,z3,z5,z6])],[(1,[z0,z386,z2,z3,z5,z6]),(0,[z0,z1,z387,z2,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z358]),(0,[z0,z1,z2,z3,z388,z5,z6]),(1,[z0,z55,z1,z3,z101,z6]),(0,[z0,z1,z2,z3,z389,z5,z6])]],
   [[(0,[z390,z0,z1,z2,z3,z5,z6]),(0,[z0,z61,z2,z3,z226,z5,z6]),(0,[z74,z0,z1,z2,z3,z9,z6]),(0,[z0,z58,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z108,z162]),(0,[z0,z1,z2,z3,z5,z6,z391])],[(0,[z0,z1,z392,z2,z3,z5,z6]),(0,[z376,z0,z1,z2,z3,z5,z6]),(0,[z0,z251,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z393]),(0,[z203,z36,z0,z1,z2,z5,z6]),(0,[z203,z0,z1,z2,z3,z5,z32])],[(0,[z0,z1,z2,z394,z3,z5,z6]),(0,[z93,z1,z2,z3,z5,z18,z6]),(0,[z0,z1,z2,z123,z3,z5,z32]),(1,[z106,z1,z2,z3,z17,z6])],[(0,[z0,z1,z2,z3,z5,z395,z6]),(0,[z28,z0,z110,z2,z3,z5,z6]),(0,[z0,z1,z2,z396,z3,z5,z6]),(0,[z0,z299,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z397,z6]),(0,[z0,z1,z2,z3,z5,z398,z6]),(0,[z304,z0,z1,z2,z3,z5,z6]),(0,[z354,z0,z1,z2,z3,z5,z6]),(0,[z399,z0,z1,z2,z3,z5,z6]),(0,[z28,z0,z1,z2,z3,z5,z20]),(0,[z400,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z401]),(1,[z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z5,z32,z6,z20]),(0,[z0,z1,z402,z2,z3,z5,z6]),(0,[z0,z1,z2,z403,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z404,z6]),(0,[z0,z55,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z405,z3,z5,z158]),(1,[z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z20,z20])],[(0,[z33,z0,z1,z2,z3,z406,z6]),(0,[z160,z0,z1,z2,z3,z5,z6]),(0,[z0,z55,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z407,z6]),(0,[z0,z1,z2,z3,z5,z6,z408])],[(0,[z409,z0,z1,z2,z3,z5,z6]),(0,[z0,z410,z1,z2,z3,z5,z6]),(0,[z0,z1,z411,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z412,z5,z6]),(0,[z0,z1,z2,z3,z9,z5,z6]),(0,[z0,z1,z2,z3,z303,z5,z6]),(0,[z0,z1,z2,z3,z413,z5,z6]),(0,[z0,z1,z2,z3,z5,z414,z6])]],
   [[(0,[z106,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z415,z3,z5,z6]),(0,[z0,z1,z25,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z139]),(0,[z86,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z161,z11,z6])],[(0,[z74,z0,z1,z2,z123,z5,z6]),(0,[z0,z416,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z101,z6]),(0,[z417,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z418]),(0,[z0,z1,z2,z3,z5,z419,z6])],[(0,[z33,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z420,z3,z5,z6]),(0,[z0,z1,z2,z3,z193,z5,z6]),(0,[z0,z1,z2,z421,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z40,z6]),(0,[z0,z1,z25,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z422,z5,z6]),(0,[z0,z1,z2,z3,z18,z101,z6]),(0,[z0,z43,z1,z3,z5,z6,z162]),(0,[z0,z1,z2,z3,z5,z6,z423]),(0,[z424,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z425,z6]),(1,[z376,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z426,z6])],[(0,[z109,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z427,z3,z5,z6])],[(0,[z0,z1,z189,z2,z3,z5,z20]),(0,[z0,z428,z1,z2,z3,z5,z6]),(0,[z125,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z429,z6]),(0,[z0,z1,z2,z405,z3,z11,z6]),(0,[z430,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z431,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z432,z5,z6]),(0,[z0,z1,z2,z405,z3,z5,z32])],[(0,[z232,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z433,z6]),(0,[z0,z1,z2,z3,z5,z434,z6]),(0,[z435,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z436,z6]),(0,[z0,z1,z2,z44,z3,z11,z6]),(0,[z0,z437,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z124,z6]),(0,[z0,z1,z2,z3,z89,z5,z6]),(0,[z0,z1,z81,z3,z53,z5,z6])],[(0,[z438,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z439,z2,z3,z5,z6]),(0,[z97,z0,z1,z2,z3,z165,z6]),(0,[z0,z1,z2,z3,z440,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z32]),(0,[z0,z110,z1,z2,z133,z5,z6]),(1,[z0,z213,z2,z3,z5,z6]),(0,[z441,z0,z1,z2,z3,z5,z6]),(0,[z203,z0,z1,z2,z3,z5,z20])],[(0,[z0,z1,z2,z123,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z6,z442]),(0,[z0,z1,z2,z3,z11,z62,z6]),(0,[z443,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z2,z3,z100,z6]),(0,[z0,z1,z2,z3,z5,z20,z280]),(0,[z0,z1,z444,z2,z3,z5,z6]),(0,[z0,z1,z356,z2,z3,z5,z32])],[(0,[z0,z1,z2,z3,z445,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z446]),(0,[z33,z0,z1,z2,z123,z5,z6]),(0,[z0,z1,z2,z3,z5,z447,z6]),(0,[z86,z0,z8,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z448])],[(0,[z0,z1,z2,z3,z449,z5,z6]),(0,[z0,z1,z450,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z59,z6]),(0,[z0,z1,z2,z3,z451,z5,z6]),(0,[z0,z1,z2,z3,z161,z38,z6])],[(0,[z0,z1,z2,z3,z452,z5,z6]),(0,[z0,z1,z2,z3,z5,z453,z6]),(0,[z0,z1,z2,z3,z454,z5,z6]),(0,[z0,z1,z2,z3,z455,z5,z6]),(1,[z0,z1,z2,z3,z5,z20])],[(0,[z0,z456,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z457]),(0,[z0,z1,z2,z3,z458,z5,z6]),(0,[z0,z1,z459,z2,z3,z5,z6]),(0,[z0,z55,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z6,z154])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z460]),(0,[z0,z1,z41,z3,z5,z101,z6]),(0,[z0,z1,z2,z3,z34,z5,z32]),(0,[z0,z1,z2,z3,z461,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z462]),(0,[z0,z1,z2,z3,z11,z463,z6]),(0,[z0,z1,z2,z3,z209,z9,z6]),(0,[z0,z464,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z140,z5,z6])],[(0,[z0,z1,z2,z249,z3,z5,z6]),(0,[z0,z1,z2,z3,z465,z5,z6]),(0,[z0,z1,z2,z3,z466,z5,z6]),(0,[z0,z1,z2,z3,z11,z11,z6]),(0,[z0,z368,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z467,z6])],[(0,[z1,z121,z2,z41,z3,z5,z6]),(0,[z0,z386,z1,z2,z3,z5,z6]),(0,[z0,z1,z468,z2,z3,z5,z6]),(0,[z46,z0,z43,z2,z3,z5,z6]),(0,[z28,z0,z1,z2,z3,z9,z6]),(0,[z469,z0,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z6,z162]),(0,[z36,z0,z1,z2,z405,z5,z6]),(0,[z203,z0,z1,z2,z3,z92,z6])],[(0,[z470,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z6,z15]),(0,[z0,z1,z471,z2,z3,z5,z6])],[(0,[z472,z0,z1,z2,z3,z5,z6]),(0,[z0,z473,z1,z2,z3,z5,z6]),(0,[z474,z0,z1,z2,z3,z5,z32])],[(0,[z232,z74,z1,z2,z3,z5,z6]),(1,[z0,z1,z475,z3,z5,z6]),(0,[z0,z1,z2,z3,z476,z5,z6]),(0,[z160,z0,z1,z2,z3,z26,z5]),(0,[z0,z1,z2,z3,z5,z6,z477]),(0,[z0,z1,z2,z3,z11,z478,z6]),(0,[z0,z1,z2,z3,z371,z5,z6]),(0,[z203,z0,z1,z2,z5,z11,z6]),(0,[z0,z479,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z480,z6]),(0,[z0,z1,z2,z3,z100,z18,z6]),(0,[z481,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z482,z2,z3,z5,z6]),(0,[z0,z483,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z9,z6]),(0,[z0,z1,z8,z2,z3,z5,z32])],[(0,[z484,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z236,z6]),(0,[z0,z1,z202,z3,z100,z5,z6]),(0,[z0,z1,z2,z3,z26,z5,z68])]],
   [[(0,[z0,z1,z2,z3,z485,z5,z6]),(0,[z0,z486,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z487])],[(0,[z0,z1,z488,z2,z3,z5,z6]),(0,[z489,z0,z1,z2,z3,z5,z6]),(0,[z0,z43,z1,z25,z3,z5,z6]),(0,[z0,z23,z1,z2,z3,z11,z6]),(0,[z0,z490,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z405,z3,z5,z20]),(0,[z0,z1,z2,z3,z3,z11,z6]),(0,[z0,z1,z2,z3,z26,z11,z6])],[(0,[z232,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z491,z6]),(0,[z0,z1,z2,z3,z492,z5,z6]),(0,[z0,z1,z2,z3,z53,z9,z6]),(0,[z0,z1,z2,z3,z100,z11,z6]),(0,[z0,z1,z2,z3,z3,z5,z32]),(0,[z0,z1,z2,z3,z26,z5,z32])],[(0,[z1,z2,z41,z3,z34,z5,z6]),(0,[z14,z0,z1,z2,z3,z161,z5]),(0,[z0,z1,z493,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z20]),(0,[z0,z1,z2,z494,z3,z5,z6]),(0,[z0,z1,z2,z3,z100,z5,z32]),(0,[z0,z1,z2,z495,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z289,z6]),(0,[z0,z496,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z497,z5,z6]),(0,[z0,z498,z1,z2,z3,z5,z6]),(0,[z499,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z500,z2,z3,z5,z6])],[(0,[z51,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z123,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z184]),(0,[z0,z1,z2,z3,z5,z501,z6])],[(0,[z51,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z502,z5,z6]),(0,[z0,z1,z2,z3,z503,z5,z6]),(0,[z160,z0,z1,z2,z3,z5,z62]),(0,[z0,z1,z2,z3,z11,z38,z6]),(0,[z0,z1,z2,z3,z504,z5,z6])],[(0,[z505,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z32,z15]),(0,[z0,z42,z1,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z506,z6]),(0,[z0,z1,z2,z3,z5,z157,z20]),(0,[z0,z1,z2,z3,z507,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z508]),(0,[z0,z43,z1,z2,z3,z11,z6]),(0,[z0,z509,z1,z2,z3,z5,z6]),(0,[z510,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z511,z6]),(0,[z0,z1,z25,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z512,z6]),(0,[z0,z513,z1,z2,z3,z5,z20]),(1,[z0,z1,z2,z3,z303,z6])],[(0,[z514,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z515,z5,z6]),(0,[z0,z1,z2,z3,z516,z5,z6]),(0,[z0,z1,z2,z3,z34,z5,z20]),(0,[z109,z0,z1,z2,z3,z18,z6]),(0,[z0,z2,z44,z3,z5,z6,z108]),(0,[z0,z517,z1,z2,z3,z5,z6]),(0,[z112,z0,z58,z2,z3,z5,z6]),(0,[z0,z23,z1,z2,z3,z5,z108]),(0,[z0,z55,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z405,z11,z6]),(0,[z0,z1,z2,z3,z5,z6,z518])],[(0,[z0,z1,z2,z3,z5,z6,z519])],[(0,[z0,z1,z2,z520,z3,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z20])],[(0,[z106,z0,z1,z2,z3,z5,z6]),(1,[z0,z359,z2,z3,z5,z6]),(0,[z521,z0,z1,z2,z3,z5,z6]),(0,[z77,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z161,z5,z6])],[(1,[z0,z1,z2,z3,z324,z6]),(0,[z0,z1,z2,z3,z5,z522,z6]),(0,[z0,z23,z1,z2,z3,z5,z157]),(0,[z523,z0,z1,z2,z3,z11,z6]),(1,[z203,z0,z1,z2,z5,z32])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z524,z6]),(0,[z0,z1,z2,z525,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z9,z6]),(0,[z0,z1,z2,z3,z9,z6,z20])],[(0,[z0,z1,z2,z138,z3,z5,z6]),(0,[z0,z110,z1,z2,z226,z5,z6]),(0,[z526,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z9,z527,z6])]],
   [[(0,[z0,z1,z44,z3,z53,z5,z6]),(0,[z0,z1,z3,z5,z102,z6,z162])],[(0,[z0,z43,z42,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z528,z6])],[(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z17,z6]),(0,[z112,z0,z1,z2,z3,z59,z6]),(0,[z0,z1,z2,z3,z5,z157,z162]),(0,[z530,z0,z1,z2,z3,z5,z6])],[(1,[z0,z110,z2,z133,z5,z6]),(0,[z0,z1,z2,z133,z3,z350,z6]),(0,[z0,z8,z359,z2,z3,z5,z6]),(0,[z0,z1,z2,z405,z3,z5,z6]),(0,[z0,z1,z2,z103,z3,z11,z6]),(0,[z0,z1,z2,z3,z3,z5,z20]),(0,[z0,z1,z2,z3,z26,z5,z20])],[(0,[z531,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z532]),(0,[z0,z1,z2,z3,z100,z5,z20]),(0,[z0,z1,z2,z103,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z20,z68])],[(0,[z51,z0,z189,z2,z3,z5,z6]),(0,[z0,z533,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z6]),(0,[z0,z1,z2,z534,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z183,z6]),(0,[z535,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z536,z5,z6]),(0,[z0,z1,z2,z537,z3,z5,z6])],[(1,[z109,z1,z2,z3,z18,z6]),(0,[z0,z538,z1,z2,z3,z5,z6]),(0,[z112,z0,z1,z2,z3,z11,z6]),(0,[z24,z0,z539,z2,z3,z5,z6]),(1,[z36,z0,z1,z2,z5,z20]),(0,[z0,z1,z2,z3,z161,z5,z38])],[(0,[z0,z1,z540,z2,z3,z5,z6]),(0,[z112,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z541,z6]),(0,[z0,z1,z542,z2,z3,z5,z6]),(0,[z543,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z232,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z544,z5,z6]),(0,[z0,z509,z23,z1,z3,z5,z6])],[(0,[z0,z1,z2,z3,z545,z5,z6]),(0,[z0,z1,z25,z2,z3,z5,z20]),(0,[z0,z1,z546,z2,z3,z5,z6])],[(0,[z0,z1,z2,z41,z3,z11,z6]),(0,[z0,z1,z121,z3,z5,z101,z6]),(0,[z0,z1,z2,z3,z547,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z162]),(2,[z0,z1,z2,z11,z20]),(0,[z0,z513,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z548,z3,z5,z6]),(0,[z0,z1,z2,z41,z3,z5,z32]),(0,[z0,z1,z2,z3,z34,z5,z6]),(0,[z0,z110,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z549,z3,z5,z6]),(0,[z0,z1,z2,z3,z550,z5,z6]),(0,[z0,z1,z2,z3,z5,z257,z6])],[(0,[z51,z1,z189,z2,z3,z5,z6]),(0,[z0,z1,z551,z2,z3,z5,z6]),(0,[z552,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z227,z6]),(0,[z0,z1,z2,z3,z553,z5,z6]),(1,[z0,z1,z2,z3,z187,z6])],[(1,[z51,z189,z2,z3,z5,z6]),(0,[z97,z1,z2,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z463,z6]),(0,[z0,z1,z2,z3,z5,z554,z6]),(0,[z0,z1,z555,z2,z3,z5,z6]),(0,[z556,z0,z1,z2,z3,z5,z6]),(0,[z0,z557,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z558]),(0,[z77,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z559,z6])],[(1,[z54,z1,z2,z3,z5,z6])],[(0,[z0,z1,z41,z3,z53,z5,z6]),(0,[z560,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z561,z2,z3,z11,z6]),(0,[z0,z1,z365,z2,z3,z9,z6]),(0,[z474,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z562,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z19]),(0,[z46,z0,z2,z3,z5,z6,z108]),(1,[z0,z1,z2,z3,z5,z358]),(0,[z0,z563,z1,z2,z3,z5,z6])],[(0,[z1,z189,z2,z3,z34,z5,z6]),(0,[z0,z1,z2,z564,z3,z5,z6]),(0,[z46,z0,z2,z3,z226,z5,z6]),(1,[z0,z1,z2,z3,z5,z340]),(0,[z0,z565,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z201,z6]),(0,[z24,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z8,z2,z3,z5,z6])],[(0,[z232,z0,z61,z2,z3,z5,z6]),(0,[z0,z1,z121,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z566,z5,z6]),(0,[z0,z1,z2,z3,z567,z5,z6]),(0,[z0,z1,z202,z2,z3,z101,z6])],[(0,[z0,z1,z568,z2,z3,z5,z6]),(0,[z0,z1,z121,z2,z3,z5,z32]),(0,[z0,z42,z1,z2,z3,z5,z289]),(0,[z112,z0,z1,z2,z3,z38,z6])],[(1,[z0,z1,z2,z3,z98,z6]),(0,[z569,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z570,z2,z3,z5,z6]),(1,[z0,z58,z2,z3,z124,z6]),(1,[z0,z1,z2,z3,z5,z255]),(0,[z0,z571,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z572]),(0,[z0,z1,z2,z573,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z3,z574,z5,z6]),(0,[z0,z1,z2,z575,z3,z5,z6]),(0,[z0,z23,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z576,z11,z6]),(0,[z0,z1,z2,z103,z3,z5,z20]),(0,[z0,z1,z2,z3,z26,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z577]),(0,[z0,z1,z2,z3,z100,z5,z6]),(0,[z0,z1,z2,z3,z5,z32,z118])],[(0,[z0,z1,z271,z2,z3,z5,z6]),(0,[z106,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z5,z578,z6]),(0,[z0,z1,z2,z5,z11,z6,z20]),(0,[z0,z1,z2,z3,z5,z579,z6])]],
   [[(0,[z112,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z8,z2,z3,z5,z102]),(0,[z0,z1,z2,z3,z11,z102,z6]),(0,[z0,z1,z2,z3,z9,z6,z518]),(0,[z0,z1,z2,z3,z5,z241,z6])],[(0,[z51,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z580]),(0,[z0,z1,z581,z2,z3,z5,z6]),(0,[z203,z0,z1,z2,z103,z5,z6]),(0,[z0,z1,z2,z3,z161,z5,z68])],[(0,[z0,z582,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z583,z5,z6]),(0,[z28,z0,z1,z570,z3,z5,z6]),(0,[z0,z2,z133,z3,z226,z5,z6]),(0,[z0,z1,z2,z3,z584,z5,z6])],[(0,[z0,z1,z585,z2,z3,z5,z6]),(0,[z46,z0,z1,z44,z3,z5,z6]),(0,[z586,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z587,z11,z6]),(0,[z0,z1,z2,z3,z5,z6,z588])],[(0,[z0,z589,z1,z2,z3,z5,z6]),(0,[z0,z590,z1,z2,z3,z5,z6]),(0,[z93,z0,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z173,z6]),(0,[z106,z0,z1,z2,z3,z5,z32]),(0,[z591,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z9,z32]),(0,[z0,z1,z2,z3,z592,z5,z32]),(0,[z0,z1,z2,z3,z161,z5,z32])],[(0,[z93,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z406,z5,z6]),(0,[z0,z1,z2,z3,z5,z593,z6]),(0,[z160,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z73,z5,z6]),(0,[z594,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z595,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z35]),(1,[z151,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z596,z3,z5,z6]),(0,[z0,z61,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z6,z597]),(1,[z367,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z598]),(0,[z0,z1,z2,z3,z5,z101,z32]),(0,[z0,z1,z2,z3,z9,z9,z6])],[(0,[z77,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z475,z3,z5,z6]),(0,[z0,z1,z2,z3,z599,z5,z6]),(0,[z600,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z2,z3,z9,z6]),(0,[z0,z1,z601,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z5,z38])]],
   [[(0,[z0,z1,z2,z3,z5,z602,z6]),(0,[z0,z1,z2,z603,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z5,z173]),(0,[z106,z0,z1,z2,z3,z17,z6]),(0,[z0,z1,z604,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z605,z6]),(0,[z417,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z20,z154])],[(0,[z606,z0,z1,z2,z3,z5,z6]),(0,[z523,z0,z1,z2,z3,z5,z6]),(0,[z28,z0,z1,z2,z226,z5,z6]),(0,[z0,z1,z2,z3,z5,z102,z108]),(0,[z0,z1,z2,z607,z3,z5,z6])],[(0,[z608,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z609,z6]),(0,[z0,z1,z202,z2,z3,z11,z6]),(1,[z0,z1,z2,z5,z11,z20])],[(0,[z14,z0,z1,z2,z3,z11,z6]),(0,[z160,z1,z2,z3,z5,z62,z6]),(0,[z52,z0,z1,z2,z3,z5,z6]),(0,[z0,z151,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z20,z162]),(0,[z0,z1,z2,z3,z5,z610,z6]),(0,[z611,z0,z1,z2,z3,z5,z6]),(0,[z0,z612,z1,z2,z3,z5,z6])],[(0,[z97,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z121,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z91,z5,z6]),(0,[z0,z1,z2,z613,z3,z5,z6]),(0,[z14,z0,z1,z2,z3,z5,z32]),(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z0,z367,z1,z2,z3,z5,z6]),(0,[z615,z0,z1,z2,z3,z5,z6])],[(0,[z109,z0,z1,z2,z3,z9,z6]),(1,[z0,z1,z175,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z102,z157]),(0,[z0,z1,z2,z616,z3,z5,z6])],[(0,[z61,z1,z189,z2,z3,z5,z6]),(0,[z0,z617,z1,z2,z3,z5,z6]),(0,[z33,z0,z1,z132,z3,z5,z6]),(0,[z618,z0,z1,z2,z3,z5,z6]),(0,[z619,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z620,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z423]),(0,[z0,z1,z2,z621,z3,z5,z6]),(0,[z622,z0,z1,z2,z3,z5,z32])],[(0,[z0,z189,z2,z3,z226,z5,z6]),(0,[z431,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z103,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z541,z32])]],
   [[(0,[z33,z0,z386,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z18,z6]),(0,[z0,z1,z2,z3,z623,z5,z6]),(0,[z0,z1,z2,z3,z9,z157,z6]),(0,[z624,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z149,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z625]),(0,[z0,z626,z1,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z257])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z112,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z59,z32]),(0,[z0,z1,z2,z3,z11,z6,z108]),(0,[z0,z1,z2,z3,z5,z627,z20])],[(0,[z0,z628,z1,z2,z3,z5,z6]),(0,[z125,z0,z23,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z629,z6])],[(0,[z630,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z631,z2,z3,z5,z6]),(0,[z125,z46,z0,z2,z3,z5,z6]),(1,[z0,z1,z570,z3,z5,z6]),(0,[z632,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z226,z11,z6]),(0,[z0,z1,z2,z3,z633,z5,z6]),(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z634,z0,z1,z2,z26,z5,z6])],[(0,[z33,z0,z1,z2,z3,z11,z6]),(0,[z106,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z226,z5,z32]),(0,[z0,z635,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z32,z6]),(0,[z0,z1,z2,z3,z9,z6,z68]),(0,[z0,z1,z2,z3,z161,z5,z20]),(0,[z0,z636,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z41,z3,z5,z6]),(0,[z93,z0,z1,z2,z3,z5,z20]),(0,[z46,z0,z42,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z236,z5,z6]),(0,[z0,z1,z2,z637,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z501]),(0,[z0,z1,z2,z3,z5,z11,z32]),(1,[z0,z1,z2,z638,z5,z6])],[(0,[z0,z639,z1,z2,z3,z5,z6]),(0,[z640,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z324,z5,z6]),(0,[z0,z1,z2,z3,z5,z101,z20]),(0,[z0,z464,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z32,z32])]],
   [[(0,[z0,z641,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z26,z68])],[(0,[z642,z0,z1,z2,z3,z5,z6]),(0,[z28,z0,z2,z3,z226,z5,z6]),(0,[z0,z1,z2,z3,z11,z234,z6]),(0,[z0,z1,z643,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z92,z6]),(0,[z203,z0,z1,z2,z5,z32,z6]),(0,[z0,z1,z2,z3,z5,z248,z6])],[(0,[z106,z109,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z104,z5,z6])],[(0,[z0,z1,z2,z3,z644,z5,z6]),(0,[z0,z645,z1,z2,z3,z5,z6]),(0,[z28,z0,z1,z2,z3,z183,z6]),(0,[z0,z1,z561,z2,z3,z5,z6])],[(0,[z106,z93,z1,z2,z3,z5,z6]),(0,[z646,z0,z1,z2,z3,z5,z6]),(0,[z112,z0,z1,z2,z3,z124,z6]),(1,[z0,z539,z2,z3,z5,z6]),(0,[z0,z1,z202,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z647,z5,z6]),(0,[z0,z571,z1,z2,z3,z5,z32]),(0,[z648,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z313,z6]),(0,[z14,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z6,z649]),(0,[z0,z23,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z6,z650])],[(0,[z0,z1,z121,z2,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z5,z235]),(0,[z0,z1,z2,z651,z3,z5,z6]),(0,[z0,z1,z2,z3,z149,z5,z18]),(0,[z0,z1,z2,z3,z5,z32,z108]),(0,[z0,z1,z2,z3,z5,z652,z6]),(0,[z0,z1,z2,z3,z9,z579,z6]),(0,[z653,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z105,z6])],[(0,[z654,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z655,z5,z6]),(0,[z656,z0,z1,z2,z3,z5,z20])]],
   [[(0,[z0,z1,z189,z2,z3,z9,z6]),(0,[z160,z0,z1,z2,z3,z5,z15])],[(0,[z74,z1,z189,z2,z3,z5,z6]),(0,[z0,z1,z2,z657,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z62,z20]),(0,[z125,z0,z1,z2,z3,z5,z108]),(0,[z0,z1,z2,z405,z3,z5,z501]),(0,[z0,z1,z2,z3,z576,z5,z6])],[(0,[z0,z1,z2,z658,z3,z5,z6]),(1,[z0,z1,z2,z3,z406,z6]),(0,[z0,z1,z2,z3,z100,z17,z6]),(1,[z112,z0,z2,z3,z59,z6]),(0,[z0,z1,z2,z3,z5,z32,z157]),(0,[z0,z1,z2,z3,z527,z5,z6])],[(1,[z0,z42,z44,z3,z5,z6]),(0,[z0,z42,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z59,z20]),(0,[z0,z58,z2,z3,z124,z5,z6]),(0,[z24,z0,z1,z2,z3,z5,z423]),(0,[z203,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z38,z32])],[(0,[z0,z659,z1,z2,z3,z5,z6]),(0,[z74,z0,z1,z2,z34,z5,z6]),(0,[z0,z1,z2,z123,z3,z9,z6]),(0,[z660,z0,z1,z2,z3,z5,z6]),(0,[z0,z42,z1,z2,z3,z5,z32]),(0,[z0,z43,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z661,z5,z6]),(1,[z0,z509,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z627,z6]),(0,[z0,z1,z2,z3,z5,z662,z6])],[(0,[z74,z1,z2,z123,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z214,z6]),(0,[z0,z1,z2,z3,z5,z102,z6]),(0,[z31,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z226,z5,z20])],[(0,[z663,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z44,z3,z5,z6,z162]),(1,[z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z405,z5,z11,z6]),(0,[z0,z1,z2,z3,z587,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z20]),(1,[z0,z1,z2,z3,z104,z6]),(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z0,z1,z2,z26,z638,z5,z6])]],
   [[(0,[z93,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z165,z6]),(0,[z0,z1,z2,z3,z664,z5,z6]),(0,[z0,z55,z1,z2,z3,z9,z6]),(0,[z0,z665,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z666,z5,z6]),(0,[z0,z1,z2,z123,z3,z5,z519]),(0,[z0,z1,z539,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z101,z6]),(0,[z667,z0,z1,z2,z3,z5,z6])],[(0,[z0,z61,z1,z2,z3,z5,z6]),(0,[z0,z668,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z669,z6])],[(0,[z106,z0,z1,z2,z3,z9,z6]),(0,[z670,z0,z1,z2,z3,z5,z6])],[(0,[z97,z0,z1,z2,z3,z40,z6]),(0,[z671,z0,z1,z2,z3,z5,z6]),(0,[z93,z0,z1,z41,z3,z5,z6]),(0,[z196,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z519]),(0,[z0,z1,z2,z672,z3,z5,z6]),(1,[z0,z1,z2,z3,z350,z6]),(0,[z36,z0,z1,z2,z9,z5,z6])],[(0,[z0,z1,z673,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z674,z5,z6]),(0,[z112,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z675,z5,z6])],[(0,[z33,z0,z1,z475,z3,z5,z6]),(0,[z0,z1,z2,z123,z3,z5,z447]),(0,[z0,z1,z2,z3,z17,z11,z6]),(0,[z0,z23,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z227,z6]),(0,[z0,z1,z202,z2,z3,z5,z6]),(0,[z676,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z12,z2,z3,z5,z20]),(1,[z634,z0,z1,z2,z5,z6])],[(0,[z0,z677,z1,z2,z3,z5,z6]),(0,[z33,z0,z1,z2,z34,z5,z6]),(0,[z14,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z232,z61,z1,z2,z3,z5,z6]),(0,[z653,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z678,z5,z6]),(0,[z0,z1,z2,z3,z5,z32,z141])],[(1,[z0,z1,z2,z3,z5,z447]),(0,[z0,z1,z2,z3,z5,z20,z15]),(0,[z0,z1,z2,z679,z3,z5,z6]),(0,[z0,z2,z3,z124,z5,z59,z6]),(0,[z656,z0,z1,z2,z3,z5,z6]),(0,[z622,z0,z1,z2,z3,z5,z6])],[(0,[z51,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z202,z41,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z193,z6]),(0,[z0,z1,z2,z3,z680,z5,z6]),(0,[z0,z1,z2,z405,z3,z9,z6])],[(0,[z0,z1,z2,z3,z5,z62,z6]),(0,[z0,z1,z2,z3,z5,z35,z6]),(1,[z52,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z3,z53,z5,z6]),(0,[z0,z1,z2,z3,z638,z5,z6])],[(0,[z681,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z9,z6]),(0,[z0,z1,z2,z3,z9,z6,z162]),(0,[z36,z0,z1,z2,z5,z6,z20]),(0,[z0,z1,z2,z3,z5,z38,z20])],[(0,[z0,z1,z682,z2,z3,z5,z6]),(0,[z93,z1,z2,z3,z34,z5,z6]),(1,[z0,z271,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z6]),(0,[z683,z0,z1,z2,z3,z5,z6]),(0,[z0,z42,z1,z2,z3,z5,z20]),(0,[z0,z684,z1,z2,z3,z5,z6]),(0,[z0,z43,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z685,z5,z6]),(0,[z0,z1,z2,z3,z5,z59,z6]),(0,[z686,z0,z1,z2,z3,z5,z6]),(0,[z687,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z114,z11,z6]),(0,[z0,z1,z2,z3,z5,z50,z20])],[(0,[z0,z1,z2,z3,z5,z688,z6]),(0,[z0,z1,z2,z3,z5,z6,z689]),(1,[z0,z1,z2,z103,z5,z20])],[(0,[z0,z1,z2,z3,z5,z6,z108])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z235]),(0,[z0,z1,z2,z3,z690,z5,z6]),(0,[z0,z1,z2,z3,z226,z5,z6]),(0,[z0,z1,z2,z3,z124,z11,z6])],[(0,[z0,z1,z2,z3,z5,z11,z6])],[(0,[z97,z0,z1,z121,z3,z5,z6]),(0,[z0,z1,z2,z3,z34,z9,z6]),(0,[z0,z1,z2,z3,z5,z691,z6]),(0,[z0,z692,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z32,z6])],[(1,[z0,z1,z2,z3,z168,z5]),(0,[z0,z1,z2,z3,z5,z6,z15]),(0,[z693,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z694,z5,z6]),(0,[z0,z237,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z695,z3,z5,z6]),(0,[z0,z1,z2,z3,z696,z5,z6]),(0,[z0,z1,z2,z3,z11,z231,z6]),(0,[z0,z1,z2,z3,z553,z9,z6])],[(0,[z0,z1,z2,z697,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z177,z6])],[(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z699,z6]),(0,[z0,z1,z2,z3,z5,z478,z6]),(0,[z0,z1,z25,z81,z3,z5,z6]),(0,[z0,z1,z2,z3,z700,z5,z6])],[(0,[z0,z1,z2,z3,z5,z701,z6])],[(0,[z0,z1,z2,z3,z702,z5,z6]),(0,[z0,z703,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z44,z3,z5,z6]),(0,[z0,z1,z2,z704,z3,z5,z6]),(0,[z705,z0,z1,z2,z3,z5,z6]),(0,[z706,z0,z1,z2,z3,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z6]),(0,[z0,z1,z708,z3,z5,z6]),(0,[z0,z539,z2,z3,z5,z184])],[(1,[z1,z2,z709,z5,z6]),(0,[z0,z410,z1,z3,z101,z6]),(0,[z0,z1,z2,z3,z350,z20])],[(0,[z310,z189,z2,z3,z5,z6]),(0,[z0,z710,z1,z3,z5,z6]),(0,[z24,z0,z1,z53,z5,z184]),(0,[z0,z1,z2,z3,z5,z711])],[(0,[z0,z1,z2,z712,z5,z6]),(0,[z74,z1,z2,z123,z313,z6]),(0,[z14,z1,z2,z3,z334,z5]),(0,[z0,z539,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z713]),(0,[z151,z1,z3,z5,z101,z6]),(0,[z0,z1,z2,z714,z11,z6]),(0,[z634,z0,z1,z2,z5,z20])],[(0,[z0,z1,z2,z3,z5,z715]),(0,[z716,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z717,z6]),(0,[z52,z213,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z718,z6])],[(0,[z74,z271,z2,z3,z5,z6]),(0,[z0,z1,z475,z3,z5,z173]),(0,[z46,z0,z1,z2,z11,z20]),(0,[z24,z0,z1,z53,z5,z6]),(0,[z523,z0,z1,z2,z11,z20])],[(0,[z0,z1,z2,z3,z719,z6]),(0,[z0,z1,z2,z3,z720,z6]),(0,[z0,z721,z1,z3,z5,z20]),(0,[z0,z1,z2,z495,z5,z32])],[(0,[z0,z1,z2,z3,z5,z722]),(0,[z0,z635,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z723]),(0,[z36,z0,z1,z2,z9,z255])]],
   [[(0,[z189,z2,z3,z282,z5,z6]),(0,[z0,z1,z2,z724,z5,z6]),(0,[z28,z376,z2,z226,z5,z6]),(0,[z112,z0,z1,z2,z638,z6]),(0,[z52,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z209,z579]),(0,[z31,z0,z1,z2,z3,z68]),(0,[z0,z1,z2,z3,z161,z579])],[(0,[z1,z41,z3,z18,z101,z6]),(0,[z0,z1,z2,z3,z406,z6]),(0,[z112,z0,z2,z3,z59,z6]),(0,[z0,z1,z2,z3,z725,z9])],[(0,[z0,z1,z2,z726,z5,z6]),(0,[z0,z271,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z727]),(0,[z1,z2,z3,z5,z728,z15]),(0,[z0,z42,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z729]),(0,[z634,z0,z1,z2,z26,z68]),(0,[z0,z1,z2,z3,z26,z408])],[(0,[z0,z1,z2,z3,z40,z32]),(0,[z0,z1,z2,z3,z730,z6]),(0,[z0,z509,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z731]),(0,[z0,z1,z2,z3,z9,z184]),(0,[z0,z1,z2,z3,z732,z11]),(0,[z0,z1,z365,z3,z553,z6]),(0,[z0,z733,z1,z3,z5,z32])],[(0,[z0,z1,z2,z3,z5,z734]),(0,[z125,z0,z1,z2,z11,z20]),(0,[z251,z1,z2,z3,z89,z6])],[(0,[z69,z1,z2,z34,z5,z6]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z735,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z736,z6]),(0,[z0,z1,z138,z3,z236,z6]),(0,[z28,z0,z2,z226,z11,z6]),(0,[z0,z110,z2,z737,z5,z6]),(0,[z0,z738,z2,z3,z5,z20])],[(0,[z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z739]),(0,[z0,z1,z740,z3,z5,z6]),(0,[z0,z113,z44,z3,z5,z6]),(0,[z741,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z156,z11,z6]),(0,[z0,z10,z1,z3,z5,z102]),(0,[z0,z1,z2,z3,z104,z6])],[(0,[z0,z1,z2,z3,z742,z6]),(0,[z293,z1,z41,z3,z5,z6]),(1,[z1,z249,z3,z18,z6]),(0,[z0,z138,z3,z226,z5,z6]),(0,[z0,z1,z2,z156,z5,z32]),(0,[z0,z23,z2,z3,z227,z108]),(0,[z0,z1,z2,z405,z743,z6]),(0,[z0,z2,z3,z744,z11,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z173]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z8,z3,z5,z162]),(0,[z220,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z638,z6,z68])],[(0,[z1,z41,z3,z445,z5,z6]),(0,[z614,z0,z1,z2,z5,z32])],[(0,[z0,z1,z2,z3,z746,z6]),(0,[z0,z1,z747,z2,z3,z5]),(0,[z0,z110,z2,z170,z5,z6]),(0,[z0,z359,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z748,z6]),(0,[z0,z1,z2,z5,z32,z749])],[(0,[z0,z1,z2,z3,z5,z519]),(0,[z1,z249,z3,z5,z18,z6]),(0,[z0,z1,z2,z3,z350,z6]),(0,[z112,z0,z2,z3,z750,z6])],[(0,[z0,z1,z2,z3,z5,z751]),(0,[z0,z1,z2,z3,z5,z752]),(0,[z0,z1,z2,z3,z11,z289]),(0,[z0,z1,z2,z3,z183,z6]),(0,[z0,z1,z753,z3,z5,z6]),(0,[z0,z23,z2,z3,z201,z108]),(0,[z86,z0,z2,z3,z5,z32])],[(0,[z0,z1,z2,z3,z754,z6])],[(0,[z106,z1,z2,z3,z256,z6]),(0,[z33,z1,z2,z34,z11,z6]),(0,[z0,z1,z2,z3,z89,z32])],[(0,[z0,z1,z2,z3,z755,z6]),(0,[z33,z1,z2,z34,z5,z32]),(0,[z0,z1,z2,z3,z193,z6]),(0,[z0,z1,z2,z3,z756,z6]),(0,[z52,z1,z2,z3,z5,z184]),(0,[z0,z1,z2,z757,z5,z6]),(0,[z653,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z403,z5,z20])]],
   [[(0,[z0,z1,z758,z3,z5,z6]),(0,[z97,z1,z41,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z447]),(0,[z0,z1,z2,z3,z5,z759]),(0,[z0,z2,z3,z124,z750,z6])],[(0,[z97,z1,z41,z3,z5,z32]),(0,[z0,z110,z2,z133,z9,z6]),(0,[z0,z2,z3,z5,z750,z6]),(0,[z0,z1,z2,z3,z90,z82]),(0,[z0,z571,z1,z3,z5,z102]),(0,[z0,z1,z2,z3,z5,z760]),(0,[z634,z0,z1,z2,z9,z6]),(0,[z0,z1,z2,z3,z761,z32])],[(0,[z0,z1,z2,z3,z762,z6]),(0,[z52,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z763]),(0,[z0,z1,z2,z3,z11,z29])],[(0,[z0,z764,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z765,z6]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z1,z2,z3,z5,z767]),(0,[z28,z367,z2,z226,z5,z6]),(0,[z0,z110,z1,z2,z11,z20]),(0,[z0,z1,z2,z198,z5,z32]),(0,[z0,z1,z2,z3,z26,z154]),(0,[z0,z1,z2,z3,z111,z154])],[(0,[z0,z1,z2,z3,z40,z20]),(0,[z0,z768,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z2,z3,z770,z6]),(0,[z771,z0,z1,z2,z3,z6]),(0,[z0,z1,z3,z100,z772,z6])],[(0,[z0,z773,z2,z3,z5,z6]),(0,[z0,z1,z774,z3,z5,z6]),(0,[z0,z1,z2,z3,z324,z447]),(0,[z0,z1,z775,z3,z5,z6]),(0,[z0,z776,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z102,z729]),(0,[z0,z1,z2,z209,z11,z20]),(0,[z0,z1,z2,z103,z5,z20])],[(0,[z0,z1,z777,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z778]),(0,[z106,z1,z2,z3,z371,z6]),(0,[z0,z110,z2,z133,z350,z6]),(0,[z0,z1,z2,z3,z779,z6]),(0,[z0,z1,z2,z3,z576,z231]),(0,[z0,z1,z780,z3,z9,z6])],[(0,[z74,z1,z2,z123,z11,z6]),(0,[z0,z1,z249,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z781]),(0,[z0,z1,z2,z782,z5,z6]),(0,[z0,z1,z2,z3,z5,z783]),(0,[z784,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z785]),(0,[z0,z1,z2,z3,z5,z786]),(0,[z0,z1,z2,z11,z20,z20])]],
   [[(0,[z0,z1,z2,z3,z787,z6]),(0,[z0,z271,z2,z3,z9,z6]),(0,[z0,z788,z2,z3,z5,z6]),(0,[z74,z1,z2,z123,z5,z32]),(0,[z0,z1,z249,z3,z5,z32]),(0,[z0,z1,z2,z672,z11,z6]),(0,[z656,z1,z2,z3,z5,z15]),(0,[z160,z0,z1,z2,z638,z5]),(0,[z0,z1,z2,z679,z11,z6]),(0,[z0,z1,z2,z737,z5,z6]),(0,[z441,z0,z1,z2,z11,z6]),(0,[z0,z1,z2,z11,z6,z408])],[(0,[z0,z1,z202,z3,z544,z6]),(0,[z586,z1,z121,z3,z5,z6]),(0,[z0,z1,z2,z3,z789,z6]),(0,[z0,z1,z2,z525,z5,z20]),(0,[z46,z0,z43,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z790]),(0,[z367,z1,z570,z3,z5,z6]),(0,[z0,z1,z2,z3,z791,z6]),(0,[z0,z1,z2,z537,z5,z20]),(0,[z441,z0,z1,z2,z5,z32]),(0,[z0,z1,z2,z743,z5,z6])],[(0,[z0,z1,z792,z3,z5,z6]),(0,[z0,z110,z2,z133,z193,z6]),(0,[z0,z1,z2,z3,z793,z6]),(0,[z0,z1,z2,z3,z5,z794]),(0,[z795,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z9,z11,z6]),(0,[z0,z1,z2,z11,z20,z221])],[(0,[z51,z189,z2,z3,z9,z6]),(0,[z344,z0,z1,z3,z101,z6]),(0,[z376,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z3,z796,z6]),(0,[z0,z213,z2,z3,z89,z6])],[(0,[z1,z2,z3,z709,z5,z6]),(0,[z0,z43,z626,z3,z5,z6]),(0,[z0,z641,z2,z3,z5,z157]),(0,[z54,z1,z2,z3,z9,z6]),(0,[z797,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z798])],[(0,[z0,z1,z2,z3,z5,z799]),(0,[z0,z800,z42,z3,z5,z6]),(0,[z801,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z53,z5,z32]),(0,[z0,z1,z2,z802,z5,z6]),(0,[z0,z1,z2,z176,z5,z20]),(0,[z86,z0,z2,z3,z5,z20])],[(1,[z1,z41,z3,z40,z6]),(0,[z109,z1,z2,z3,z168,z18]),(0,[z125,z0,z2,z3,z11,z157]),(0,[z0,z1,z2,z3,z5,z803]),(0,[z0,z1,z202,z3,z100,z6]),(0,[z804,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z805,z6]),(0,[z0,z1,z2,z3,z806,z6]),(0,[z97,z0,z1,z2,z11,z20]),(0,[z0,z1,z807,z3,z5,z6]),(0,[z0,z1,z2,z3,z89,z20]),(0,[z0,z1,z2,z53,z11,z20])]],
   [[(0,[z33,z1,z2,z34,z5,z20]),(0,[z28,z0,z2,z226,z236,z6]),(0,[z0,z1,z808,z3,z5,z6]),(0,[z0,z2,z737,z226,z5,z6]),(0,[z0,z23,z175,z3,z5,z108]),(0,[z0,z1,z2,z3,z161,z231])],[(0,[z0,z1,z809,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z19]),(0,[z0,z2,z44,z3,z5,z19]),(0,[z0,z1,z2,z3,z810,z6]),(0,[z0,z1,z2,z3,z811,z6]),(0,[z0,z1,z2,z11,z6,z20])],[(0,[z97,z1,z41,z3,z5,z20]),(0,[z0,z44,z3,z5,z108,z162]),(0,[z0,z1,z2,z812,z5,z6]),(0,[z0,z1,z2,z3,z9,z255]),(0,[z196,z1,z2,z3,z180,z6])],[(0,[z0,z1,z2,z3,z5,z813]),(0,[z45,z0,z2,z3,z5,z108]),(0,[z0,z1,z2,z5,z749,z20])],[(0,[z0,z1,z2,z3,z98,z173]),(0,[z0,z44,z3,z574,z5,z6]),(0,[z814,z1,z2,z3,z5,z6]),(0,[z251,z1,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z815,z6])],[(0,[z51,z816,z2,z3,z5,z6]),(0,[z470,z0,z2,z226,z5,z6]),(0,[z0,z1,z2,z3,z5,z35]),(0,[z0,z1,z2,z3,z183,z340]),(0,[z0,z1,z2,z3,z817,z6]),(0,[z0,z1,z2,z11,z20,z280])],[(0,[z0,z1,z2,z3,z818,z6]),(0,[z0,z1,z2,z3,z40,z6]),(0,[z125,z0,z2,z3,z5,z819])],[(0,[z0,z1,z2,z3,z820,z6]),(0,[z1,z2,z3,z17,z821,z6]),(0,[z0,z1,z138,z3,z5,z340]),(0,[z0,z1,z2,z3,z193,z358]),(0,[z0,z1,z2,z3,z5,z822]),(0,[z0,z1,z359,z3,z5,z162]),(0,[z0,z1,z2,z208,z11,z20])]],
   [[(0,[z823,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z737,z5,z6]),(0,[z0,z1,z2,z3,z772,z6]),(0,[z0,z55,z1,z3,z140,z6]),(0,[z0,z1,z2,z265,z11,z6])],[(0,[z232,z61,z2,z3,z11,z6]),(0,[z74,z1,z2,z123,z5,z20]),(0,[z28,z0,z2,z226,z5,z6]),(0,[z0,z1,z824,z3,z5,z6]),(0,[z0,z464,z2,z3,z124,z6]),(0,[z0,z539,z2,z3,z5,z423]),(0,[z0,z1,z2,z3,z5,z825])],[(0,[z0,z1,z41,z3,z40,z6]),(0,[z0,z826,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z827,z5]),(0,[z0,z828,z2,z3,z5,z6])],[(0,[z0,z1,z829,z3,z5,z6]),(0,[z33,z0,z1,z2,z11,z20]),(0,[z0,z2,z3,z744,z5,z6]),(0,[z0,z1,z2,z150,z5,z20]),(0,[z251,z1,z2,z3,z11,z6]),(0,[z151,z1,z2,z3,z9,z6]),(0,[z0,z1,z8,z3,z5,z105]),(0,[z0,z1,z12,z2,z11,z20])],[(0,[z0,z1,z2,z3,z830,z6]),(0,[z367,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z183,z32]),(0,[z0,z1,z2,z831,z5,z6]),(0,[z0,z10,z1,z2,z11,z20])],[(0,[z1,z121,z832,z3,z5,z6]),(0,[z0,z1,z132,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z833]),(0,[z0,z1,z138,z3,z11,z6])],[(0,[z232,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z1,z132,z3,z5,z32]),(0,[z0,z1,z2,z3,z835,z6]),(0,[z0,z1,z138,z3,z5,z32]),(0,[z0,z213,z2,z3,z214,z6]),(0,[z0,z1,z2,z3,z89,z184]),(0,[z24,z0,z1,z53,z5,z20]),(0,[z0,z1,z365,z3,z100,z6]),(0,[z31,z0,z1,z2,z3,z518])],[(0,[z0,z1,z2,z3,z5,z836]),(0,[z0,z386,z2,z3,z11,z6]),(0,[z86,z0,z2,z3,z5,z6]),(0,[z837,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z537,z9,z6]),(0,[z0,z1,z2,z60,z11,z6]),(0,[z0,z1,z2,z3,z838,z6])]],
   [[(0,[z0,z839,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z289]),(0,[z0,z1,z2,z3,z840,z6]),(0,[z367,z2,z3,z226,z5,z6]),(0,[z0,z110,z2,z133,z5,z35]),(0,[z0,z1,z2,z5,z229,z20]),(0,[z0,z1,z3,z5,z772,z6]),(0,[z687,z0,z1,z2,z5,z20])],[(0,[z74,z1,z2,z709,z5,z6]),(0,[z0,z1,z2,z3,z89,z6]),(0,[z841,z0,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z161,z559])],[(0,[z33,z1,z2,z34,z5,z6]),(0,[z367,z1,z2,z3,z183,z6]),(0,[z842,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z3,z587,z6])],[(0,[z0,z843,z2,z3,z5,z6]),(0,[z106,z1,z2,z3,z17,z32]),(0,[z0,z1,z175,z3,z9,z6]),(0,[z0,z844,z2,z3,z5,z6]),(0,[z0,z55,z1,z3,z772,z6]),(0,[z0,z8,z359,z3,z5,z162])],[(0,[z97,z1,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z845,z6]),(0,[z376,z1,z2,z3,z183,z6]),(0,[z0,z1,z2,z3,z9,z423]),(0,[z0,z571,z1,z3,z5,z541])],[(0,[z0,z1,z137,z3,z11,z6]),(0,[z0,z1,z2,z250,z5,z20]),(0,[z0,z1,z2,z3,z846,z6]),(0,[z847,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z749,z6])],[(0,[z0,z1,z2,z3,z5,z848]),(0,[z0,z1,z137,z3,z5,z32]),(0,[z0,z1,z2,z5,z253,z20]),(0,[z143,z0,z2,z226,z5,z6]),(0,[z376,z1,z138,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z3,z209,z38]),(0,[z0,z1,z2,z3,z161,z38])],[(0,[z0,z1,z2,z5,z32,z247])]],
   [[(0,[z0,z1,z2,z3,z849,z6]),(0,[z0,z1,z832,z3,z5,z6]),(0,[z0,z386,z2,z3,z5,z235]),(0,[z0,z58,z1,z2,z11,z20]),(0,[z0,z1,z2,z3,z5,z850])],[(0,[z232,z816,z2,z3,z5,z6]),(0,[z97,z1,z41,z3,z165,z6]),(0,[z46,z0,z43,z3,z5,z32]),(0,[z0,z1,z2,z11,z157,z20]),(0,[z251,z213,z2,z3,z5,z6]),(0,[z0,z539,z3,z53,z5,z6])],[(0,[z0,z1,z2,z41,z11,z20]),(0,[z591,z0,z1,z2,z5,z20]),(0,[z0,z1,z570,z3,z9,z6]),(0,[z0,z23,z2,z3,z9,z108]),(0,[z0,z1,z2,z11,z511,z6]),(0,[z0,z1,z2,z9,z11,z32])],[(0,[z0,z1,z249,z3,z5,z6]),(0,[z74,z1,z2,z123,z5,z6]),(0,[z0,z1,z2,z3,z168,z9]),(0,[z0,z1,z2,z11,z6,z518]),(0,[z0,z1,z851,z3,z5,z20]),(0,[z0,z368,z2,z3,z5,z248])],[(0,[z0,z1,z2,z3,z852,z6]),(0,[z0,z1,z8,z2,z11,z20]),(0,[z0,z1,z2,z3,z9,z501]),(0,[z0,z1,z2,z638,z9,z6])],[(0,[z0,z853,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z235]),(0,[z0,z1,z2,z3,z183,z20]),(0,[z0,z1,z2,z3,z854,z6]),(0,[z0,z1,z855,z3,z11,z6]),(0,[z0,z1,z753,z3,z5,z20])],[(0,[z0,z1,z2,z3,z5,z856]),(0,[z0,z857,z1,z2,z3,z6]),(0,[z0,z1,z858,z3,z5,z6]),(0,[z0,z94,z44,z3,z5,z6]),(0,[z0,z110,z138,z3,z5,z6]),(0,[z0,z1,z2,z3,z859,z6]),(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z202,z3,z100,z32])],[(0,[z0,z1,z132,z3,z5,z20]),(0,[z14,z0,z1,z2,z638,z5]),(0,[z0,z1,z138,z3,z5,z20]),(0,[z0,z1,z2,z3,z241,z32])]],
   [[(0,[z61,z816,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z861]),(0,[z74,z1,z2,z123,z324,z6]),(0,[z219,z1,z2,z3,z17,z6]),(0,[z0,z1,z2,z3,z862,z6]),(0,[z0,z1,z2,z3,z193,z20]),(0,[z52,z1,z2,z3,z5,z423]),(0,[z0,z359,z3,z5,z6,z162])],[(0,[z0,z1,z2,z3,z863,z5]),(0,[z0,z1,z2,z3,z5,z728]),(0,[z0,z1,z2,z3,z214,z184]),(0,[z0,z1,z2,z3,z5,z864])],[(0,[z0,z1,z3,z865,z5,z6]),(0,[z0,z1,z2,z866,z5,z6]),(0,[z0,z1,z2,z3,z149,z5]),(0,[z28,z0,z2,z226,z5,z340]),(0,[z0,z1,z2,z3,z5,z867]),(0,[z379,z0,z1,z2,z9,z6]),(0,[z868,z0,z1,z2,z5,z6]),(0,[z125,z0,z2,z3,z5,z157]),(0,[z0,z539,z2,z3,z9,z6]),(0,[z0,z213,z2,z3,z11,z6]),(0,[z0,z10,z1,z3,z5,z729]),(0,[z0,z1,z2,z3,z11,z257])],[(0,[z0,z1,z2,z282,z5,z20]),(0,[z0,z1,z2,z869,z5,z6]),(0,[z0,z1,z2,z210,z11,z6]),(0,[z0,z1,z2,z3,z870,z5]),(0,[z0,z1,z2,z81,z11,z20]),(0,[z0,z1,z2,z3,z5,z871]),(1,[z0,z1,z2,z11,z158])],[(0,[z0,z1,z872,z3,z5,z6]),(0,[z1,z41,z3,z5,z40,z6]),(0,[z106,z1,z2,z3,z17,z20]),(0,[z873,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z874]),(0,[z0,z1,z2,z3,z214,z6]),(0,[z24,z0,z1,z53,z9,z6])],[(0,[z0,z1,z2,z338,z11,z6]),(0,[z0,z1,z2,z3,z5,z875]),(0,[z0,z1,z2,z3,z5,z876]),(0,[z0,z1,z2,z877,z5,z6]),(0,[z0,z1,z2,z3,z878,z6]),(0,[z879,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z9,z176,z6]),(0,[z0,z1,z2,z3,z5,z880])],[(0,[z0,z1,z881,z3,z5,z6]),(0,[z0,z1,z882,z3,z5,z6]),(0,[z0,z1,z2,z11,z20,z68])],[(0,[z0,z1,z883,z3,z5,z6]),(0,[z0,z884,z2,z3,z5,z6]),(0,[z0,z1,z137,z3,z5,z20]),(0,[z28,z0,z2,z737,z5,z6]),(0,[z0,z1,z2,z3,z885,z6]),(0,[z0,z1,z2,z396,z5,z20]),(0,[z203,z0,z1,z2,z714,z6]),(0,[z203,z0,z1,z2,z241,z6])]],
   [[(0,[z93,z1,z121,z3,z11,z6]),(0,[z0,z386,z475,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z886]),(0,[z0,z1,z2,z3,z5,z819])],[(0,[z93,z1,z121,z3,z5,z32]),(0,[z109,z1,z249,z3,z18,z6]),(0,[z0,z42,z44,z3,z9,z6]),(0,[z28,z0,z2,z226,z5,z32]),(0,[z24,z52,z1,z53,z5,z6])],[(0,[z671,z1,z41,z3,z5,z6]),(0,[z46,z0,z43,z3,z5,z20]),(0,[z0,z509,z1,z3,z9,z6]),(0,[z0,z2,z3,z5,z819,z108]),(0,[z887,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z888,z6]),(0,[z0,z1,z889,z3,z5,z6]),(0,[z0,z1,z2,z3,z890,z5]),(0,[z0,z1,z2,z3,z5,z891]),(0,[z892,z1,z2,z3,z5,z6]),(0,[z893,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z9,z11,z20]),(0,[z0,z1,z2,z208,z5,z20]),(0,[z203,z0,z1,z2,z5,z257])],[(0,[z0,z894,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z168,z11]),(0,[z0,z2,z3,z5,z157,z819]),(0,[z251,z1,z2,z3,z5,z184]),(0,[z0,z1,z2,z9,z32,z20])],[(0,[z232,z61,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z1,z475,z3,z11,z6]),(0,[z0,z10,z1,z3,z9,z102]),(0,[z0,z1,z851,z3,z5,z6])],[(0,[z74,z1,z2,z548,z5,z6]),(0,[z0,z1,z2,z3,z896,z6]),(0,[z33,z1,z2,z34,z98,z6]),(0,[z0,z1,z2,z3,z5,z897]),(0,[z52,z539,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z899,z1,z3,z5,z6]),(0,[z0,z900,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z901,z6]),(0,[z902,z1,z2,z3,z5,z6]),(0,[z0,z1,z202,z3,z100,z20]),(0,[z0,z1,z8,z3,z9,z162])]],
   [[(0,[z0,z1,z2,z3,z236,z32]),(0,[z0,z1,z2,z3,z241,z20])],[(0,[z0,z1,z132,z3,z5,z6]),(0,[z0,z1,z2,z375,z11,z6]),(0,[z0,z1,z138,z3,z5,z6]),(1,[z0,z2,z737,z5,z6]),(0,[z112,z0,z2,z3,z527,z6]),(0,[z0,z1,z2,z3,z90,z6]),(1,[z151,z1,z3,z101,z6])],[(0,[z0,z1,z2,z3,z9,z519]),(0,[z0,z1,z903,z3,z5,z6]),(0,[z0,z1,z2,z375,z5,z32]),(0,[z0,z10,z1,z3,z5,z506]),(0,[z0,z1,z8,z3,z5,z729]),(0,[z0,z1,z2,z3,z209,z177])],[(0,[z0,z386,z2,z3,z5,z6]),(0,[z1,z475,z3,z34,z5,z6]),(0,[z0,z1,z904,z3,z5,z6]),(0,[z0,z1,z2,z5,z231,z20]),(0,[z0,z1,z2,z3,z161,z798])],[(0,[z0,z1,z2,z3,z5,z905]),(0,[z1,z2,z3,z5,z6,z906]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z0,z1,z2,z351,z5,z20]),(0,[z841,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z908]),(0,[z0,z1,z2,z909,z5,z6])],[(0,[z0,z1,z2,z651,z5,z20]),(0,[z0,z1,z2,z3,z910,z5]),(0,[z0,z1,z2,z3,z11,z184]),(0,[z0,z1,z2,z3,z5,z911]),(0,[z0,z1,z2,z5,z20,z118])],[(0,[z1,z2,z41,z3,z40,z6]),(0,[z225,z1,z121,z3,z5,z6]),(0,[z0,z271,z2,z3,z406,z6]),(0,[z0,z1,z475,z3,z5,z235]),(0,[z106,z1,z2,z3,z17,z6]),(0,[z0,z1,z249,z3,z18,z6]),(0,[z0,z800,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z912,z6])],[(0,[z0,z1,z2,z3,z9,z447]),(0,[z0,z1,z2,z3,z5,z913]),(0,[z77,z0,z1,z2,z11,z20])]],
   [[(0,[z0,z1,z2,z3,z11,z6]),(0,[z470,z1,z2,z34,z5,z6]),(0,[z0,z1,z2,z11,z395,z6]),(0,[z0,z1,z2,z574,z11,z6]),(0,[z0,z1,z2,z3,z5,z914]),(0,[z376,z1,z2,z3,z236,z6]),(0,[z0,z1,z2,z3,z5,z915]),(0,[z916,z1,z2,z3,z5,z6]),(0,[z55,z151,z1,z3,z101,z6]),(0,[z917,z1,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z5,z850])],[(0,[z0,z1,z137,z3,z5,z6]),(0,[z410,z1,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z23,z2,z3,z5,z248]),(0,[z52,z1,z2,z3,z9,z6])],[(0,[z0,z1,z2,z3,z919,z6]),(0,[z93,z1,z121,z3,z5,z20]),(0,[z28,z0,z2,z226,z5,z20]),(0,[z125,z0,z2,z3,z5,z50]),(0,[z251,z1,z2,z3,z214,z6])],[(0,[z1,z832,z2,z3,z5,z6]),(0,[z135,z1,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z920]),(0,[z0,z1,z921,z3,z5,z6]),(0,[z922,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z317,z11,z6]),(0,[z0,z1,z2,z5,z32,z511]),(0,[z0,z1,z2,z3,z11,z82])],[(0,[z0,z923,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z313,z32]),(0,[z367,z1,z2,z3,z5,z29]),(0,[z924,z1,z2,z3,z5,z6]),(0,[z0,z359,z2,z3,z11,z6]),(0,[z0,z1,z774,z3,z9,z6]),(0,[z0,z1,z2,z103,z9,z20]),(0,[z0,z1,z2,z103,z104,z20])],[(0,[z0,z271,z2,z3,z5,z173]),(0,[z0,z1,z2,z583,z11,z6]),(0,[z0,z1,z2,z3,z925,z6]),(0,[z0,z151,z1,z3,z101,z6]),(0,[z203,z0,z1,z2,z11,z32]),(0,[z0,z1,z2,z303,z11,z6])],[(0,[z93,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z926,z6]),(0,[z0,z1,z2,z616,z11,z6])],[(0,[z1,z832,z41,z3,z5,z6]),(0,[z0,z1,z249,z3,z17,z6]),(0,[z0,z1,z2,z3,z927,z6]),(0,[z0,z1,z2,z3,z89,z423]),(1,[z0,z1,z2,z11,z20])]],
   [[(0,[z0,z1,z2,z174,z5,z20]),(1,[z0,z359,z3,z5,z162]),(0,[z354,z0,z1,z2,z11,z20])],[(0,[z0,z1,z2,z3,z928,z6]),(0,[z0,z1,z121,z2,z11,z20]),(0,[z0,z1,z2,z3,z5,z235]),(0,[z0,z1,z2,z3,z236,z20]),(0,[z0,z1,z2,z371,z11,z20]),(0,[z0,z1,z855,z3,z5,z6]),(0,[z0,z1,z2,z9,z743,z6])],[(0,[z0,z44,z3,z5,z6,z19]),(0,[z0,z172,z2,z3,z114,z6]),(0,[z656,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z11,z20,z154]),(0,[z0,z1,z2,z3,z714,z6]),(0,[z0,z1,z2,z3,z241,z6]),(0,[z0,z1,z2,z638,z209,z6]),(0,[z0,z1,z2,z638,z161,z6])],[(0,[z0,z1,z2,z3,z929,z6]),(0,[z0,z1,z2,z3,z5,z930]),(0,[z0,z213,z2,z3,z5,z184])],[(0,[z0,z1,z2,z3,z5,z931]),(0,[z106,z0,z1,z2,z11,z20]),(0,[z0,z42,z44,z3,z5,z19]),(0,[z642,z0,z44,z3,z5,z6]),(0,[z0,z1,z2,z3,z214,z32]),(0,[z656,z1,z2,z3,z5,z221])],[(0,[z0,z1,z2,z3,z932,z5]),(0,[z14,z1,z2,z3,z11,z15]),(0,[z0,z1,z2,z3,z5,z933]),(0,[z0,z2,z3,z750,z59,z6]),(0,[z0,z58,z1,z2,z638,z6]),(0,[z0,z1,z2,z11,z20,z162]),(0,[z653,z0,z2,z3,z5,z50])],[(0,[z0,z1,z2,z3,z934,z6]),(0,[z0,z213,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z1,z2,z88,z5,z20]),(0,[z0,z299,z1,z3,z101,z6]),(0,[z0,z1,z2,z432,z11,z6]),(0,[z0,z1,z2,z3,z5,z257]),(0,[z36,z0,z1,z2,z11,z20])],[(0,[z0,z1,z2,z275,z5,z20]),(0,[z69,z0,z1,z53,z5,z6]),(0,[z109,z1,z137,z3,z18,z6]),(0,[z0,z1,z2,z388,z5,z20]),(0,[z0,z1,z2,z3,z936,z6]),(0,[z0,z1,z2,z3,z937,z6]),(0,[z0,z1,z2,z3,z798,z68])]],
   [[(0,[z0,z1,z2,z3,z938,z6]),(0,[z481,z61,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z19]),(0,[z0,z1,z2,z403,z9,z6])],[(0,[z0,z1,z2,z3,z939,z6]),(1,[z0,z1,z2,z241,z20]),(0,[z0,z1,z356,z3,z5,z105])],[(0,[z0,z1,z2,z3,z5,z940]),(0,[z0,z1,z2,z3,z941,z6]),(0,[z0,z1,z2,z3,z5,z942]),(0,[z943,z0,z2,z3,z5,z6]),(0,[z0,z1,z570,z3,z5,z29])],[(0,[z944,z1,z2,z3,z5,z20])],[(0,[z93,z1,z121,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z945]),(0,[z0,z1,z249,z3,z5,z20]),(1,[z1,z2,z3,z821,z6]),(0,[z946,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z0,z1,z2,z3,z9,z35])],[(0,[z232,z61,z2,z3,z5,z32]),(0,[z0,z1,z132,z3,z98,z6]),(0,[z0,z1,z2,z3,z313,z20]),(0,[z0,z1,z2,z3,z5,z948]),(0,[z0,z1,z2,z3,z227,z32]),(0,[z0,z539,z2,z3,z89,z6]),(0,[z0,z1,z2,z3,z11,z158])],[(0,[z0,z1,z2,z3,z5,z949]),(0,[z24,z0,z1,z53,z5,z423]),(0,[z54,z1,z2,z3,z11,z6]),(0,[z36,z0,z1,z2,z5,z158]),(0,[z203,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z3,z854,z20])],[(0,[z0,z386,z2,z3,z98,z6]),(0,[z251,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z576,z38]),(0,[z0,z1,z2,z3,z859,z20]),(0,[z0,z1,z2,z413,z5,z20])]],
   [[(0,[z93,z1,z832,z3,z5,z6]),(0,[z28,z0,z2,z226,z9,z6]),(0,[z0,z1,z2,z3,z11,z358]),(0,[z0,z58,z2,z3,z750,z6]),(0,[z0,z1,z2,z9,z694,z6]),(0,[z0,z1,z2,z161,z11,z20]),(0,[z0,z1,z2,z616,z5,z20])],[(0,[z0,z1,z475,z3,z5,z6]),(0,[z106,z1,z2,z3,z821,z6]),(0,[z0,z1,z2,z950,z5,z6]),(0,[z0,z1,z2,z3,z11,z340]),(0,[z0,z1,z2,z3,z350,z35]),(0,[z0,z1,z2,z3,z90,z32])],[(0,[z171,z0,z1,z2,z11,z20])],[(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z386,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z236,z6]),(0,[z0,z55,z1,z3,z101,z32]),(0,[z0,z172,z1,z2,z11,z20]),(0,[z952,z0,z1,z2,z3,z6])],[(0,[z33,z1,z2,z34,z406,z6]),(0,[z24,z0,z213,z53,z5,z6]),(0,[z0,z1,z2,z3,z90,z139])],[(0,[z0,z1,z2,z3,z5,z953]),(0,[z0,z1,z2,z3,z5,z954]),(0,[z0,z1,z2,z3,z193,z35]),(0,[z0,z1,z2,z3,z214,z20]),(1,[z0,z1,z3,z5,z729])],[(0,[z0,z1,z2,z3,z5,z955]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z0,z1,z2,z174,z9,z6]),(0,[z0,z1,z2,z3,z5,z957]),(0,[z86,z0,z2,z3,z9,z6]),(0,[z0,z1,z2,z5,z20,z408])],[(0,[z0,z61,z1,z2,z11,z20]),(0,[z0,z1,z2,z3,z26,z433]),(0,[z367,z1,z138,z3,z5,z6]),(0,[z958,z0,z1,z2,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z959,z6]),(0,[z0,z1,z2,z3,z5,z960]),(0,[z0,z961,z2,z3,z5,z6]),(0,[z0,z1,z16,z3,z5,z162]),(0,[z0,z1,z2,z252,z5,z20]),(0,[z86,z0,z8,z3,z5,z162]),(0,[z0,z1,z2,z3,z11,z32])],[(0,[z0,z1,z962,z3,z5,z6]),(0,[z33,z1,z2,z34,z9,z6]),(0,[z0,z1,z963,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z184]),(0,[z0,z464,z2,z3,z73,z6])],[(0,[z0,z1,z2,z3,z5,z964]),(0,[z0,z965,z2,z3,z5,z6]),(0,[z376,z1,z2,z3,z5,z340]),(0,[z0,z1,z2,z3,z26,z689]),(0,[z0,z1,z2,z3,z5,z966]),(0,[z0,z299,z1,z3,z478,z6])],[(0,[z97,z1,z41,z3,z9,z6]),(0,[z0,z1,z2,z11,z62,z20]),(0,[z0,z800,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z139]),(0,[z0,z1,z2,z621,z5,z20])],[(0,[z0,z1,z2,z445,z5,z20]),(0,[z0,z1,z2,z3,z5,z967]),(0,[z0,z1,z2,z3,z303,z6])],[(0,[z0,z1,z2,z968,z5,z6]),(0,[z0,z1,z969,z3,z5,z6]),(0,[z0,z970,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z971,z6]),(0,[z0,z1,z2,z3,z98,z235]),(0,[z0,z1,z2,z3,z9,z29]),(0,[z944,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z59,z20]),(0,[z0,z1,z2,z451,z5,z20]),(0,[z0,z1,z2,z3,z890,z11])],[(0,[z232,z61,z2,z3,z5,z20]),(0,[z0,z1,z2,z5,z32,z395]),(0,[z367,z1,z2,z3,z11,z6]),(0,[z0,z1,z25,z2,z11,z20])],[(0,[z0,z1,z2,z3,z313,z6]),(0,[z0,z1,z2,z34,z11,z20]),(0,[z0,z1,z2,z366,z11,z6]),(0,[z0,z1,z2,z3,z5,z82]),(0,[z0,z217,z1,z3,z5,z136])]],
   [[(0,[z0,z1,z2,z366,z5,z32]),(0,[z376,z1,z2,z3,z11,z6]),(0,[z251,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z11,z463,z20]),(0,[z203,z0,z1,z2,z11,z6])],[(0,[z0,z1,z2,z3,z5,z972]),(0,[z74,z1,z2,z603,z5,z6]),(0,[z0,z1,z2,z3,z324,z6]),(0,[z0,z1,z973,z3,z5,z6]),(0,[z0,z1,z2,z3,z974,z5]),(0,[z376,z1,z2,z3,z5,z32]),(1,[z0,z2,z3,z5,z819]),(0,[z151,z1,z2,z3,z100,z6]),(0,[z0,z1,z2,z11,z11,z20]),(0,[z203,z0,z1,z2,z5,z32]),(0,[z203,z0,z1,z2,z303,z32])],[(0,[z0,z1,z2,z3,z5,z975]),(0,[z0,z1,z2,z3,z976,z5]),(0,[z33,z1,z2,z709,z5,z6]),(0,[z74,z1,z2,z123,z9,z6]),(0,[z0,z1,z249,z3,z9,z6]),(0,[z1,z2,z249,z3,z18,z6]),(0,[z0,z1,z2,z3,z90,z20])],[(0,[z0,z1,z977,z3,z5,z6]),(0,[z0,z1,z570,z3,z183,z6]),(0,[z0,z1,z2,z3,z5,z978]),(0,[z0,z1,z2,z9,z413,z6])],[(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z386,z2,z3,z5,z20]),(0,[z0,z1,z411,z3,z100,z6]),(0,[z0,z1,z2,z3,z5,z981]),(0,[z52,z1,z2,z3,z89,z6]),(0,[z0,z55,z1,z3,z101,z20])],[(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z1,z2,z3,z983,z6]),(0,[z271,z2,z3,z34,z5,z6]),(0,[z0,z1,z2,z3,z984,z6]),(0,[z0,z1,z2,z3,z985,z6]),(0,[z0,z1,z2,z11,z478,z20])],[(0,[z0,z986,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z987]),(0,[z0,z1,z2,z3,z5,z988]),(0,[z0,z213,z2,z3,z5,z32])],[(0,[z529,z1,z41,z3,z5,z6]),(0,[z33,z271,z2,z34,z5,z6]),(0,[z0,z1,z989,z3,z5,z6]),(0,[z74,z1,z2,z123,z5,z519]),(0,[z0,z1,z3,z5,z990,z6]),(0,[z0,z1,z2,z695,z11,z6])]],
   [[(0,[z0,z1,z2,z695,z5,z32])],[(0,[z109,z1,z2,z3,z149,z18]),(0,[z14,z1,z2,z3,z5,z15]),(0,[z0,z1,z2,z3,z5,z991]),(0,[z0,z1,z992,z3,z5,z6]),(0,[z0,z1,z993,z3,z5,z6]),(0,[z125,z0,z2,z3,z9,z157]),(0,[z0,z994,z2,z3,z5,z6]),(0,[z687,z0,z1,z2,z9,z6]),(0,[z0,z1,z2,z3,z11,z20]),(0,[z0,z1,z2,z26,z11,z20])],[(0,[z0,z1,z2,z3,z5,z995]),(0,[z996,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z100,z11,z20]),(0,[z36,z0,z1,z2,z5,z20]),(0,[z36,z0,z1,z2,z9,z257]),(0,[z0,z1,z2,z3,z5,z749])],[],[(0,[z0,z997,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z998]),(0,[z74,z1,z2,z123,z5,z447]),(0,[z240,z0,z43,z3,z5,z6]),(0,[z0,z1,z2,z3,z236,z340]),(0,[z0,z1,z2,z3,z38,z798])],[(0,[z56,z189,z2,z3,z5,z6]),(0,[z0,z1,z475,z3,z98,z6]),(0,[z0,z1,z2,z3,z406,z173]),(0,[z0,z490,z44,z3,z5,z6]),(0,[z0,z1,z175,z3,z5,z108]),(0,[z0,z539,z25,z3,z5,z6]),(0,[z1,z2,z3,z5,z20,z906])],[(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z1,z2,z3,z732,z5]),(0,[z125,z0,z2,z3,z5,z155]),(0,[z0,z1,z2,z3,z5,z1000]),(0,[z474,z0,z2,z3,z5,z157]),(0,[z0,z1,z2,z252,z9,z6]),(0,[z0,z1,z2,z3,z11,z501]),(0,[z0,z1,z2,z638,z11,z6]),(0,[z0,z1,z2,z11,z38,z20])],[(0,[z0,z1,z2,z3,z1001,z5]),(0,[z109,z1,z2,z3,z180,z6]),(0,[z0,z1,z113,z3,z5,z162]),(0,[z0,z1,z2,z11,z50,z20])]],
   [[(0,[z112,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z3,z227,z6]),(0,[z0,z1,z2,z3,z187,z6]),(0,[z0,z1,z3,z5,z729,z6])],[(0,[z0,z1,z475,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z1002]),(0,[z0,z1,z2,z3,z5,z158])],[(0,[z0,z1,z2,z3,z1003,z6]),(0,[z251,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1004,z6]),(0,[z0,z1,z1005,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z173]),(0,[z0,z1,z2,z3,z1006,z6]),(0,[z376,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z405,z11,z158]),(0,[z0,z1,z2,z11,z559,z6]),(0,[z892,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z92,z32])],[(0,[z0,z1,z2,z3,z1007,z6]),(0,[z0,z13,z1,z3,z101,z6]),(0,[z0,z1,z132,z3,z406,z6]),(0,[z591,z0,z1,z2,z9,z6]),(0,[z0,z1,z2,z3,z187,z82]),(0,[z0,z1,z561,z2,z11,z20]),(0,[z952,z0,z1,z2,z3,z32])],[(0,[z676,z1,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z358])],[(0,[z1,z2,z709,z34,z5,z6]),(0,[z0,z1,z2,z3,z5,z340]),(0,[z0,z1,z2,z3,z201,z6]),(0,[z0,z1,z2,z3,z161,z177]),(0,[z304,z1,z2,z3,z5,z141])],[(0,[z0,z1,z2,z1008,z5,z6]),(0,[z0,z490,z2,z3,z5,z108]),(0,[z0,z55,z1,z3,z101,z6]),(0,[z0,z1,z2,z3,z592,z231])],[(0,[z93,z1,z468,z3,z5,z6]),(0,[z0,z213,z2,z3,z5,z20]),(0,[z370,z0,z1,z2,z11,z6])]],
   [[(0,[z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z132,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z1009]),(0,[z0,z1,z2,z3,z1010,z5]),(0,[z0,z1,z2,z3,z161,z434]),(0,[z0,z1,z138,z3,z9,z6]),(0,[z28,z0,z1,z2,z11,z20]),(0,[z0,z58,z2,z3,z124,z6]),(0,[z0,z58,z2,z3,z662,z6]),(0,[z0,z1011,z2,z3,z5,z6]),(0,[z0,z1,z1012,z3,z5,z32])],[(1,[z0,z800,z3,z5,z6]),(0,[z367,z1,z2,z3,z236,z6])],[(0,[z0,z1,z2,z338,z5,z20]),(0,[z0,z1,z2,z3,z1013,z6]),(0,[z0,z386,z2,z3,z9,z6]),(0,[z0,z1014,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z208,z68])],[(0,[z0,z1,z121,z3,z40,z6]),(0,[z97,z1,z41,z3,z40,z6]),(0,[z0,z1,z2,z7,z11,z6]),(0,[z24,z251,z1,z53,z5,z6]),(1,[z0,z1,z3,z772,z6])],[(0,[z0,z1,z2,z3,z5,z32]),(0,[z0,z1015,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z303,z6]),(0,[z0,z1,z2,z3,z303,z32])],[(0,[z0,z1,z1016,z3,z5,z6]),(0,[z0,z1,z2,z3,z1017,z6]),(0,[z74,z1,z475,z3,z5,z6]),(0,[z0,z1,z2,z3,z1018,z6]),(0,[z0,z1,z2,z3,z5,z1019]),(0,[z0,z1,z2,z405,z11,z32]),(0,[z0,z1,z2,z3,z725,z5])],[(0,[z0,z1,z2,z3,z5,z1020]),(0,[z1,z2,z3,z821,z18,z6]),(0,[z0,z1,z138,z3,z183,z6]),(0,[z0,z1,z2,z3,z26,z118])],[(0,[z0,z1021,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1022,z6]),(0,[z0,z110,z2,z133,z5,z358]),(0,[z0,z1,z2,z3,z5,z139]),(0,[z1023,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1024]),(0,[z0,z1,z137,z3,z9,z6]),(0,[z28,z0,z570,z226,z5,z6]),(0,[z171,z0,z2,z3,z59,z6]),(0,[z0,z1,z2,z3,z1025,z6]),(0,[z0,z359,z2,z3,z5,z32])],[(0,[z0,z1,z2,z3,z165,z32]),(0,[z0,z1,z2,z3,z324,z32]),(0,[z109,z0,z1,z2,z11,z20]),(0,[z0,z1,z2,z3,z1026,z6]),(0,[z0,z1,z2,z3,z5,z1027]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z5,z1028])],[(0,[z0,z1,z475,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z1029]),(0,[z1030,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1031]),(0,[z0,z1,z2,z3,z406,z235]),(0,[z0,z1,z2,z3,z5,z1032]),(0,[z46,z0,z43,z3,z9,z6]),(0,[z0,z1,z1033,z3,z11,z6]),(0,[z0,z1,z2,z5,z257,z20]),(0,[z0,z1,z2,z5,z850,z20]),(1,[z0,z1,z2,z5,z749]),(0,[z0,z1,z2,z3,z92,z20]),(0,[z0,z1,z2,z3,z5,z798])],[(0,[z376,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z519]),(0,[z0,z1,z2,z3,z1034,z6])],[(0,[z0,z1,z2,z3,z5,z1035]),(0,[z0,z513,z2,z3,z5,z108]),(0,[z0,z1,z2,z3,z1036,z6])],[(0,[z0,z271,z132,z3,z5,z6]),(0,[z0,z1,z2,z3,z149,z9]),(0,[z0,z1,z2,z3,z1037,z6]),(0,[z0,z110,z2,z133,z11,z6]),(0,[z151,z1,z202,z3,z5,z6]),(0,[z1038,z0,z2,z3,z11,z6]),(0,[z634,z0,z1,z2,z11,z6]),(0,[z0,z1,z2,z638,z5,z231])],[(0,[z0,z1,z2,z3,z5,z1039]),(0,[z1040,z1,z2,z3,z5,z6]),(0,[z0,z1,z570,z3,z236,z6]),(0,[z0,z110,z2,z133,z5,z32]),(0,[z0,z1,z2,z133,z11,z20]),(0,[z0,z1041,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z9,z235])],[(0,[z0,z1,z2,z1042,z5,z6]),(0,[z97,z1,z832,z3,z5,z6]),(0,[z14,z1,z2,z3,z5,z728]),(0,[z0,z1,z2,z520,z5,z20]),(0,[z1043,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z38,z298]),(0,[z0,z2,z3,z5,z819,z6]),(1,[z0,z1,z2,z638,z68])],[(0,[z0,z1,z1044,z3,z5,z6]),(0,[z109,z1,z2,z3,z18,z32]),(0,[z0,z1,z2,z566,z5,z20]),(0,[z0,z1,z2,z3,z5,z1045]),(0,[z1046,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1047])],[(0,[z676,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z1048,z6])],[(0,[z0,z1,z1049,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1050]),(0,[z54,z55,z1,z3,z101,z6])],[(0,[z0,z1,z2,z3,z5,z20]),(1,[z816,z2,z3,z5,z6]),(0,[z0,z271,z2,z3,z11,z6]),(0,[z0,z1,z2,z576,z11,z20]),(0,[z0,z1,z2,z3,z9,z257]),(0,[z0,z1,z2,z3,z303,z20])],[(0,[z0,z1,z2,z3,z1051,z6]),(0,[z0,z1,z2,z651,z9,z6]),(0,[z109,z1,z2,z3,z821,z6]),(0,[z0,z1,z202,z2,z11,z20]),(0,[z0,z1,z2,z405,z11,z20]),(0,[z0,z513,z1,z2,z11,z20]),(0,[z887,z0,z1,z2,z3,z9])],[(0,[z0,z1,z2,z3,z1052,z6]),(0,[z0,z1,z1053,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1054]),(0,[z0,z1,z2,z3,z1055,z6]),(0,[z0,z1,z2,z3,z1056,z6]),(0,[z523,z1,z2,z3,z371,z6]),(0,[z0,z1,z2,z11,z627,z20])]],
   [[(0,[z51,z189,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z187,z32]),(0,[z151,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z1057,z6]),(0,[z0,z1,z2,z11,z102,z20]),(0,[z0,z1,z2,z5,z241,z20])],[(0,[z51,z189,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z1058]),(0,[z0,z1,z2,z3,z1059,z6]),(0,[z0,z1,z2,z3,z1060,z6]),(0,[z0,z1,z2,z3,z5,z1061]),(0,[z0,z1,z3,z772,z101,z6]),(0,[z0,z359,z2,z3,z5,z20]),(0,[z220,z1,z2,z3,z463,z6])],[(0,[z0,z1,z1062,z3,z5,z6]),(0,[z0,z1,z2,z3,z165,z20]),(0,[z0,z1,z2,z3,z5,z1063]),(0,[z0,z1,z2,z3,z324,z20]),(0,[z1064,z1,z2,z3,z5,z6]),(0,[z24,z0,z1,z53,z89,z6]),(0,[z0,z1,z2,z3,z1065,z6]),(0,[z54,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z1066,z6]),(0,[z0,z1,z2,z638,z5,z6]),(0,[z203,z0,z1,z2,z5,z749])],[(0,[z93,z1,z121,z3,z9,z6]),(0,[z1067,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z187,z139]),(0,[z0,z1,z2,z587,z11,z20])],[(0,[z0,z1,z2,z3,z5,z1068]),(0,[z0,z1,z2,z3,z5,z1069]),(0,[z1070,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z101,z20]),(0,[z634,z0,z1,z2,z5,z257]),(0,[z0,z1,z2,z3,z26,z68])],[(0,[z46,z0,z2,z3,z5,z19]),(0,[z0,z800,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z201,z32]),(0,[z0,z1071,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z214,z423]),(0,[z0,z1,z2,z3,z92,z6])],[(0,[z0,z1,z2,z3,z1072,z6]),(0,[z0,z271,z2,z3,z5,z235]),(0,[z0,z1073,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1074,z6]),(0,[z0,z42,z44,z3,z5,z289]),(0,[z1075,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z208,z154])],[(0,[z0,z1,z1076,z3,z5,z6]),(0,[z0,z1,z2,z3,z149,z11]),(0,[z24,z0,z1,z757,z5,z6]),(0,[z0,z1,z3,z757,z5,z6]),(0,[z804,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z11,z255]),(0,[z0,z1,z12,z3,z5,z280])]],
   [[(0,[z0,z1,z2,z3,z1077,z6]),(0,[z0,z1,z475,z3,z9,z6]),(0,[z0,z1,z2,z3,z98,z32]),(0,[z1078,z1,z2,z3,z5,z6]),(0,[z0,z110,z2,z133,z5,z20]),(0,[z0,z1,z2,z3,z1079,z6]),(0,[z0,z58,z2,z3,z124,z32]),(0,[z0,z1,z2,z3,z1080,z6]),(1,[z0,z1,z2,z743,z6]),(0,[z0,z1,z2,z103,z241,z20]),(0,[z0,z1,z3,z5,z990,z20]),(0,[z0,z1011,z2,z3,z5,z32])],[(0,[z472,z189,z2,z3,z5,z6]),(0,[z0,z816,z2,z3,z5,z6]),(0,[z232,z27,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1081,z5]),(0,[z1,z2,z123,z709,z5,z6]),(0,[z0,z1,z2,z9,z250,z6]),(0,[z0,z1,z44,z3,z5,z19]),(0,[z28,z0,z2,z226,z183,z6]),(0,[z0,z1082,z1,z3,z5,z6]),(0,[z0,z23,z1,z2,z11,z20]),(0,[z0,z1,z757,z53,z5,z6]),(0,[z0,z1,z2,z11,z136,z20])],[(0,[z0,z1,z2,z3,z5,z1083]),(0,[z0,z1,z2,z3,z11,z19]),(0,[z0,z1,z2,z3,z9,z289]),(0,[z0,z1,z2,z3,z1084,z6]),(0,[z0,z1,z2,z3,z5,z1085]),(0,[z0,z1,z2,z495,z11,z6]),(0,[z203,z0,z1,z2,z92,z32])],[(0,[z0,z1,z2,z3,z1086,z6]),(0,[z0,z1,z2,z3,z1087,z6]),(0,[z109,z1,z2,z3,z18,z20]),(0,[z0,z1,z2,z3,z821,z6]),(0,[z0,z1,z2,z3,z1088,z6]),(0,[z367,z1,z2,z3,z5,z340]),(0,[z28,z0,z138,z226,z5,z6]),(0,[z0,z1,z1012,z3,z5,z6]),(0,[z0,z1,z2,z5,z610,z20])],[(0,[z0,z1,z1089,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z1090]),(0,[z0,z359,z2,z3,z5,z162]),(0,[z0,z1,z2,z638,z5,z38])],[(0,[z0,z1,z1091,z3,z5,z6]),(0,[z0,z1,z2,z3,z1092,z6]),(0,[z0,z1,z2,z3,z5,z1093]),(0,[z1094,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z64,z11,z6]),(0,[z0,z513,z2,z3,z5,z80])],[(0,[z33,z1,z2,z34,z5,z173]),(0,[z0,z1,z2,z3,z1095,z6]),(0,[z0,z1,z2,z3,z11,z35]),(0,[z0,z1,z2,z5,z32,z559]),(0,[z0,z1,z2,z3,z26,z798])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1096]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z0,z1,z2,z3,z1098,z6]),(0,[z0,z1,z2,z88,z9,z6]),(0,[z0,z1,z2,z638,z11,z20]),(0,[z36,z0,z1,z2,z743,z6])]],
   [[(0,[z1,z816,z2,z3,z5,z6]),(0,[z0,z1099,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z18,z20]),(0,[z0,z1,z2,z388,z9,z6]),(0,[z251,z1,z2,z3,z5,z423]),(0,[z151,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z405,z11,z6]),(0,[z36,z0,z1,z2,z9,z32])],[(0,[z0,z1,z2,z3,z1100,z6]),(0,[z0,z1,z2,z3,z5,z1101]),(0,[z0,z1,z2,z3,z227,z20]),(0,[z0,z1,z2,z3,z187,z20]),(0,[z151,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z5,z1102])],[(0,[z51,z189,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z1103,z6]),(0,[z0,z43,z1,z3,z5,z19]),(0,[z367,z1,z2,z3,z5,z32]),(0,[z0,z1104,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z6,z158])],[(0,[z417,z1,z2,z3,z17,z6]),(0,[z0,z359,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1105,z6]),(0,[z0,z539,z2,z3,z214,z6]),(0,[z54,z1,z2,z3,z5,z20])],[(0,[z0,z1,z2,z3,z5,z1106]),(0,[z0,z1,z2,z3,z165,z6]),(0,[z33,z1,z132,z34,z5,z6]),(0,[z0,z1,z2,z226,z11,z20]),(0,[z0,z1,z2,z3,z1107,z6]),(0,[z0,z1,z2,z3,z5,z1108])],[(0,[z0,z1109,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z1110,z6]),(0,[z614,z0,z1,z2,z11,z6]),(0,[z24,z0,z1,z53,z214,z6]),(0,[z0,z1,z2,z11,z32,z20])],[(0,[z816,z189,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1111]),(0,[z0,z271,z475,z3,z5,z6]),(0,[z33,z386,z2,z34,z5,z6]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z0,z1,z2,z3,z183,z29]),(1,[z0,z175,z3,z5,z108]),(0,[z0,z1,z2,z3,z201,z20]),(0,[z0,z1,z2,z3,z9,z82]),(0,[z0,z1112,z2,z3,z5,z6]),(0,[z0,z10,z1,z3,z5,z136])],[(0,[z0,z1,z1113,z3,z5,z6]),(0,[z0,z1,z2,z3,z1114,z6]),(0,[z0,z1,z2,z3,z1115,z6]),(0,[z0,z43,z800,z3,z5,z6]),(0,[z0,z1,z2,z3,z1116,z6]),(0,[z0,z299,z1,z2,z11,z20]),(0,[z0,z1,z1033,z3,z5,z6]),(0,[z0,z1,z2,z11,z177,z20])]],
   [[(0,[z0,z1,z2,z3,z1117,z6]),(0,[z0,z1,z138,z3,z5,z29]),(0,[z0,z1,z175,z3,z11,z6]),(0,[z86,z0,z2,z3,z11,z6]),(0,[z417,z1,z2,z3,z91,z6]),(0,[z203,z0,z1,z2,z9,z32])],[(0,[z0,z1,z2,z3,z98,z20]),(0,[z1118,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z44,z11,z20]),(0,[z0,z1,z570,z3,z5,z340]),(0,[z0,z58,z2,z3,z124,z20]),(0,[z0,z1,z175,z3,z5,z32]),(0,[z0,z1,z2,z3,z11,z423]),(0,[z0,z1,z2,z11,z234,z20])],[(0,[z1038,z0,z2,z3,z5,z6]),(0,[z1119,z1,z2,z3,z5,z6]),(0,[z0,z110,z2,z133,z5,z6]),(0,[z0,z1,z2,z3,z1120,z6]),(0,[z0,z2,z133,z737,z5,z6]),(0,[z125,z0,z175,z3,z5,z6]),(0,[z0,z1,z2,z11,z20,z108]),(0,[z0,z1,z2,z3,z1121,z6]),(0,[z0,z359,z2,z3,z5,z102]),(0,[z634,z0,z1,z2,z5,z6]),(0,[z634,z0,z1,z2,z303,z6])],[(0,[z0,z1,z2,z3,z5,z1122]),(0,[z0,z1,z2,z3,z1123,z6]),(0,[z0,z1124,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z313,z519]),(0,[z143,z0,z1,z53,z5,z6]),(0,[z0,z1,z2,z3,z5,z1125]),(0,[z0,z1,z2,z3,z413,z38])],[(0,[z0,z1,z2,z3,z1126,z6]),(0,[z0,z1,z2,z3,z1127,z6]),(0,[z46,z0,z373,z3,z5,z6]),(0,[z624,z0,z1,z2,z11,z6]),(0,[z0,z1,z3,z5,z729,z162]),(0,[z0,z1,z2,z647,z5,z20])],[(0,[z0,z1,z2,z3,z324,z519]),(0,[z109,z1,z2,z3,z18,z6]),(0,[z624,z0,z1,z2,z5,z32]),(0,[z0,z1,z2,z3,z5,z1128]),(0,[z0,z1,z2,z5,z11,z158]),(0,[z0,z721,z1,z3,z5,z6])],[(0,[z0,z1,z2,z11,z20,z15]),(0,[z251,z539,z2,z3,z5,z6]),(0,[z1129,z1,z2,z3,z11,z6])],[(0,[z0,z1,z2,z1130,z5,z6]),(0,[z0,z1,z780,z3,z5,z6]),(0,[z0,z1,z570,z3,z11,z6]),(0,[z0,z1,z2,z3,z5,z1131]),(0,[z0,z1,z2,z3,z5,z1132]),(0,[z0,z1,z2,z549,z11,z6]),(0,[z0,z23,z2,z3,z11,z108]),(0,[z0,z1,z2,z198,z11,z6]),(0,[z1133,z0,z2,z3,z5,z20]),(0,[z0,z1,z2,z638,z5,z68])]],
   [[(0,[z0,z1,z189,z2,z11,z20]),(0,[z0,z1134,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z313,z447]),(0,[z14,z1,z2,z3,z9,z15]),(0,[z0,z43,z1,z2,z11,z20]),(0,[z0,z1,z570,z3,z5,z32]),(0,[z0,z1,z2,z549,z5,z32]),(0,[z251,z1,z3,z53,z5,z6]),(0,[z0,z1,z2,z3,z1135,z6]),(0,[z0,z1136,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1137,z6])],[(0,[z0,z271,z2,z3,z5,z6]),(0,[z1138,z1,z2,z3,z5,z6]),(0,[z0,z42,z1,z2,z11,z20]),(0,[z36,z0,z1,z2,z9,z20])],[(0,[z93,z1,z363,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1139]),(0,[z367,z110,z2,z3,z5,z6]),(0,[z151,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z638,z5,z32])],[(0,[z0,z1,z2,z3,z1140,z6]),(0,[z14,z0,z1,z2,z11,z20]),(0,[z367,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z638,z68]),(0,[z0,z1,z2,z26,z638,z68])],[(0,[z51,z189,z2,z3,z5,z6]),(0,[z33,z1,z2,z34,z5,z235]),(0,[z0,z1,z175,z3,z5,z157]),(0,[z0,z1,z620,z3,z5,z102]),(0,[z0,z1,z561,z3,z587,z6]),(0,[z0,z738,z2,z3,z5,z6])],[(0,[z1141,z0,z1,z2,z5,z6]),(0,[z54,z1,z2,z3,z5,z6]),(0,[z0,z1,z1142,z3,z5,z6])],[(0,[z1143,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1144]),(0,[z0,z710,z1,z3,z11,z6])],[(0,[z51,z0,z1,z2,z11,z20]),(0,[z232,z61,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z168,z5]),(0,[z112,z0,z2,z3,z389,z6]),(0,[z0,z175,z3,z5,z6,z108]),(0,[z0,z539,z2,z3,z11,z6]),(0,[z0,z213,z2,z3,z5,z423]),(0,[z24,z0,z1,z2,z11,z20])]],
   [[(0,[z0,z1,z2,z3,z5,z1145]),(0,[z0,z386,z2,z3,z406,z6]),(0,[z376,z1,z570,z3,z5,z6]),(0,[z0,z539,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z9,z158])],[(0,[z0,z1,z2,z123,z11,z20]),(0,[z0,z1,z2,z223,z11,z6]),(0,[z251,z1,z2,z3,z9,z6]),(0,[z24,z0,z1,z53,z11,z6])],[(0,[z0,z1,z2,z3,z5,z1146]),(0,[z74,z0,z1,z2,z11,z20]),(0,[z14,z1,z2,z3,z5,z141]),(1,[z0,z2,z3,z750,z6]),(0,[z0,z1,z175,z3,z5,z20]),(0,[z52,z1,z2,z3,z214,z6])],[(0,[z0,z1,z2,z3,z9,z358]),(0,[z0,z23,z2,z3,z5,z819]),(0,[z0,z1,z2,z3,z5,z255]),(0,[z0,z1,z3,z865,z11,z6])],[(0,[z0,z1,z2,z3,z1147,z6]),(0,[z0,z1,z2,z3,z9,z340]),(0,[z1148,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z798])],[(0,[z0,z1,z2,z3,z1149,z6]),(0,[z0,z110,z2,z562,z5,z6]),(0,[z0,z1,z132,z3,z5,z173]),(0,[z0,z1,z2,z3,z1150,z6])],[(0,[z0,z1,z2,z3,z406,z32]),(0,[z0,z1,z2,z4,z11,z6]),(0,[z0,z1,z2,z17,z11,z20]),(0,[z0,z42,z44,z3,z11,z6]),(0,[z112,z0,z2,z3,z59,z32]),(0,[z0,z1,z2,z11,z247,z6])],[(0,[z0,z1,z2,z3,z1151,z6]),(0,[z0,z386,z2,z3,z5,z173]),(0,[z0,z42,z44,z3,z5,z32]),(0,[z0,z509,z1,z3,z11,z6])]],
   [[(0,[z0,z1,z2,z3,z350,z358]),(0,[z0,z509,z1,z3,z5,z32])],[(0,[z0,z1,z2,z3,z5,z1152]),(0,[z0,z1,z570,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z1153]),(0,[z1133,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1154,z6]),(0,[z315,z0,z1,z3,z5,z162]),(0,[z0,z1,z2,z1155,z5,z6]),(0,[z24,z0,z539,z53,z5,z6]),(0,[z0,z10,z1,z3,z11,z102]),(0,[z0,z1,z2,z3,z743,z6]),(0,[z0,z1,z2,z11,z20,z80]),(0,[z0,z1,z2,z3,z26,z518])],[(0,[z0,z1,z2,z3,z5,z1156]),(0,[z181,z1,z2,z3,z18,z6]),(0,[z28,z0,z2,z226,z5,z29]),(0,[z0,z733,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1157]),(0,[z36,z0,z1,z2,z9,z6]),(0,[z0,z1,z2,z3,z9,z32]),(0,[z0,z1,z2,z638,z5,z20]),(0,[z0,z1,z2,z3,z104,z32])],[(0,[z151,z1,z2,z3,z5,z6]),(0,[z33,z1,z475,z34,z5,z6]),(0,[z0,z1,z2,z3,z11,z173]),(0,[z0,z1,z2,z3,z5,z1158]),(0,[z0,z58,z2,z3,z114,z6]),(0,[z0,z1,z8,z3,z11,z162]),(0,[z0,z1,z2,z209,z11,z6]),(0,[z0,z1,z2,z111,z11,z20]),(0,[z706,z0,z1,z2,z5,z20]),(0,[z0,z1,z2,z241,z6,z20])],[(0,[z367,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1159,z6]),(0,[z0,z386,z132,z3,z5,z6]),(0,[z0,z1,z1160,z3,z5,z6]),(0,[z46,z0,z207,z3,z5,z6]),(0,[z0,z1,z2,z114,z11,z20]),(0,[z0,z217,z1,z2,z11,z20])],[(0,[z93,z0,z1,z2,z11,z20]),(0,[z0,z1,z1161,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z139]),(0,[z1023,z1,z2,z3,z9,z6])],[(0,[z0,z1,z2,z3,z1162,z6]),(0,[z0,z1,z2,z3,z1163,z6])]],
   [[(0,[z0,z1,z2,z1164,z5,z6]),(0,[z0,z1,z2,z3,z350,z32]),(0,[z0,z1,z2,z124,z11,z20]),(0,[z0,z1,z2,z3,z1165,z6])],[(0,[z0,z1,z2,z3,z1166,z5]),(1,[z1,z832,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1167]),(0,[z1168,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1169,z6]),(0,[z379,z0,z1,z2,z5,z20]),(0,[z0,z539,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z1170]),(0,[z0,z1,z2,z327,z11,z6]),(0,[z0,z1,z2,z5,z11,z20]),(0,[z0,z237,z1,z3,z140,z6])],[(0,[z0,z1,z2,z3,z1171,z5]),(0,[z0,z1,z2,z3,z236,z29]),(0,[z0,z1,z202,z3,z772,z6]),(0,[z0,z1,z2,z5,z32,z20]),(0,[z31,z0,z1,z2,z3,z118]),(0,[z634,z0,z1,z2,z5,z32])],[(0,[z0,z1,z2,z3,z5,z1172]),(0,[z376,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z694,z5,z20]),(0,[z0,z1,z2,z11,z231,z20])],[(0,[z0,z1,z2,z3,z11,z447]),(0,[z0,z473,z44,z3,z5,z6]),(0,[z0,z1,z175,z3,z5,z6]),(0,[z0,z1,z2,z3,z193,z32]),(0,[z171,z0,z2,z3,z234,z6])],[(0,[z0,z1,z2,z3,z5,z1173]),(0,[z0,z271,z2,z3,z98,z6]),(0,[z0,z1,z2,z3,z5,z423])],[(0,[z0,z1,z2,z282,z11,z6]),(0,[z52,z1,z2,z3,z11,z6])],[(0,[z0,z1,z2,z3,z406,z20]),(0,[z160,z0,z1,z2,z11,z20]),(0,[z112,z0,z2,z3,z59,z20]),(0,[z52,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z592,z38])]],
   [[(0,[z0,z1,z2,z3,z5,z1174]),(0,[z0,z42,z44,z3,z5,z20]),(0,[z1175,z1,z2,z3,z5,z6]),(0,[z0,z1,z1176,z3,z5,z6]),(0,[z0,z213,z2,z3,z9,z6])],[(0,[z0,z271,z2,z3,z5,z32]),(0,[z106,z1,z249,z3,z5,z6]),(0,[z220,z1,z2,z3,z18,z6]),(0,[z1,z2,z3,z5,z6,z728]),(0,[z0,z509,z1,z3,z5,z20]),(0,[z0,z10,z359,z3,z5,z6]),(0,[z0,z1,z2,z103,z11,z20]),(0,[z0,z1,z2,z3,z761,z6])],[(0,[z13,z1,z2,z3,z18,z6]),(1,[z0,z44,z3,z5,z19]),(0,[z0,z1177,z2,z3,z5,z6]),(0,[z1129,z1,z2,z3,z5,z6]),(0,[z431,z0,z2,z3,z527,z6]),(0,[z0,z1,z2,z103,z5,z749])],[(0,[z0,z1,z2,z3,z5,z1178]),(0,[z0,z1,z132,z3,z5,z235]),(0,[z0,z1,z570,z3,z5,z6]),(0,[z0,z1,z2,z3,z1179,z5]),(0,[z0,z23,z2,z3,z5,z108])],[(0,[z46,z0,z800,z3,z5,z6]),(0,[z1180,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z20]),(0,[z0,z1,z2,z3,z104,z20]),(0,[z474,z0,z2,z3,z5,z63])],[(0,[z0,z1,z2,z1181,z5,z6]),(0,[z46,z0,z43,z3,z11,z6]),(0,[z0,z2,z175,z3,z5,z108]),(0,[z0,z509,z23,z3,z5,z108]),(0,[z0,z1,z2,z3,z5,z501]),(0,[z0,z1,z2,z743,z11,z6])],[(0,[z0,z1,z475,z3,z406,z6]),(0,[z0,z1,z2,z3,z1182,z6]),(0,[z0,z1,z2,z3,z1183,z6]),(0,[z0,z1,z2,z3,z1184,z6]),(0,[z0,z1,z2,z405,z11,z501]),(0,[z0,z1,z2,z111,z11,z6])],[(0,[z0,z1,z2,z3,z1185,z6]),(0,[z0,z16,z2,z3,z5,z108]),(0,[z0,z55,z1,z2,z11,z20]),(0,[z0,z1,z12,z3,z5,z162]),(0,[z0,z1,z2,z3,z111,z68])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 502).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1014).take 343) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1357)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [502, 512, 343] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 66).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 66).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 135).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 199).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [66, 69, 64, 57] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_46266

theorem PEqualNP.Outside.L_meta_46266 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4274585216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4274585216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46266.solve