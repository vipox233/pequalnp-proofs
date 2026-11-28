import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38933

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4276145344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0801b31c711c7664#64 ++ 0x210036638e238ecc#64 ++ 0xa827f73cf13cf667#64 ++ 0xd504fee79e279ecc#64 : BitVec 256),
   (0x004b8145014502a8#64 ++ 0x40097028a028a055#64 ++ 0xf8db89c701c71fff#64 ++ 0xbf1b7138e038e3ff#64 : BitVec 256),
   (0x03140e02b602b856#64 ++ 0x806281c056c0570a#64 ++ 0xd71c0e07fe07f87f#64 ++ 0x7ae381c0ffc0ff0f#64 : BitVec 256),
   (0x05a00ea81aa81d07#64 ++ 0x00b401d5035503a0#64 ++ 0xffe00ff81ff81f86#64 ++ 0xfffc01ff03ff03f0#64 : BitVec 256),
   (0x16fed0000df7c000#64 ++ 0x02dfda0001bef800#64 ++ 0x9ffff0001fffe005#64 ++ 0xf3fffe0003fffc00#64 : BitVec 256),
   (0x27ff6df7c0000000#64 ++ 0x04ffedbef8000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0xd01808070007187f 0x3a030100e000e30f

def z1 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8db89c701c71fff 0xbf1b7138e038e3ff

def z2 : W := mkw 0x035f8f47b747bafe 0xc06bf1e8f6e8f75f 0xffdf8fc7ffc7ffff 0xfffbf1f8fff8ffff

def z3 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe00ff81ff81f86 0xfffc01ff03ff03f0

def z4 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa827f73cf13cf667 0xd504fee79e279ecc

def z5 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9ffff0001fffe005 0xf3fffe0003fffc00

def z6 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xd71c0e07fe07f87f 0x7ae381c0ffc0ff0f

def z8 : W := mkw 0x0b5fbf5ff75ffefe 0xe16bf7ebfeebffdf 0xffffffffffffffff 0xffffffffffffffff

def z9 : W := mkw 0x0da12fbc7aa83f67 0x21b425f78f5507ec 0xffe00ffcfff81fe6 0xfffc01ff9fff03fc

def z10 : W := mkw 0x000002003602b856 0x8000004006c0570a 0x100000001e07f87c 0x0200000003c0ff0f

def z11 : W := mkw 0x24eb61f540000000 0x049d6c3ea8000000 0x20e3f1f800000000 0x841c7e3f00000000

def z12 : W := mkw 0x0da03eb87ab87d47 0x21b407d70f570fa8 0x07247638fe38e000 0x40e48ec71fc71c00

def z13 : W := mkw 0x01000ea812081d07 0x002001d5024103a0 0x60000ff800001f82 0x0c0001ff000003f0

def z14 : W := mkw 0x125ed0000557c000 0x024bda0000aaf800 0x001ff0000007e001 0x0003fe000000fc00

def z15 : W := mkw 0x0214000004028000 0x0042800000805000 0x070400001e00e000 0x40e0800003c01c00

def z16 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x073ff63fe0000001 0x40e7fec7fc000000

def z17 : W := mkw 0x02140002a402a050 0x804280005480540a 0x001c0007e007e079 0x00038000fc00fc0f

def z18 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0x28e001f801f80780 0x851c003f003f00f0

def z19 : W := mkw 0x0800221870083444 0x210004430e010688 0x00000638e0000000 0x000000c71c000000

def z20 : W := mkw 0x07b40eaabeaabd57 0x80f681d557d557aa 0xfffc0fffffffffff 0xffff81ffffffffff

def z21 : W := mkw 0x14ead00009f54000 0x029d5a00013ea800 0x08e3f00001f80000 0x811c7e00003f0000

def z22 : W := mkw 0x03152d16c0000000 0x0062a5a2d8000000 0xe73fff3fe0000003 0xfce7ffe7fc000000

def z23 : W := mkw 0x01000ea81aa81d07 0x002001d5035503a0 0x78000ff81ff81f86 0x0f0001ff03ff03f0

def z24 : W := mkw 0x05eb8fed1bed1faf 0x40bd71fda37da3f5 0xfffb8fff1fff1fff 0xffff71ffe3ffe3ff

def z25 : W := mkw 0x16ffd1450df7c2a8 0x42dffa28a1bef855 0xfffff9c71fffffff 0xffffff38e3ffffff

def z26 : W := mkw 0x0001211440000000 0x0000242288000000 0xa027f73ce0000003 0xd404fee79c000000

def z27 : W := mkw 0x121490000df7c000 0x0242920001bef800 0x9f1c00001fffe005 0x73e3800003fffc00

def z28 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xe0db89c70007007b 0xbc1b7138e000e00f

def z29 : W := mkw 0x0001211440000000 0x0000242288000000 0x2000073ce0000002 0x040000e79c000000

def z30 : W := mkw 0x225f6157c0000000 0x044bec2af8000000 0xa03ff73fe0000003 0xd407fee7fc000000

def z31 : W := mkw 0x03140c0286028812 0x8062818050c05102 0xd71c0e07ee03081b 0x7ae381c0fdc06103

def z32 : W := mkw 0x37fe4ce38ce38000 0x06ffc99c719c7000 0x57d808c30ec30000 0x2afb011861d86000

def z33 : W := mkw 0x021402003602b856 0x8042804006c0570a 0x971c00001e07f87d 0x72e3800003c0ff0f

def z34 : W := mkw 0x0800321870187444 0x210006430e030e88 0x00247638f038e000 0x40048ec71e071c00

def z35 : W := mkw 0x0801b11461146260 0x210036228c228c4c 0x0007f004e004e061 0x0000fe009c009c0c

def z36 : W := mkw 0x100090000df7c000 0x0200120001bef800 0x180000001fffe004 0x0300000003fffc00

def z37 : W := mkw 0x27b46cb2c0000000 0x04f68d9658000000 0x07247638e0000000 0x40e48ec71c000000

def z38 : W := mkw 0x03140c0286028812 0x8062818050c05102 0x571808030e030818 0x2ae3010061c06103

def z39 : W := mkw 0x0801b11c411c4620 0x21003623882388c4 0x2823f13801380600 0x85047e27002700c0

def z40 : W := mkw 0x01000e02b2003856 0x802001c05640070a 0x40000e07e000187a 0x080001c0fc00030f

def z41 : W := mkw 0x004b014500000000 0x00096028a0000000 0xf0db89c70007187f 0xbe1b7138e000e30f

def z42 : W := mkw 0x01000ca002000903 0x0020019400400120 0x400008c000000980 0x0800011800000130

def z43 : W := mkw 0x000002081aa81d07 0x00000041035503a0 0x180000001ff81f84 0x0300000003ff03f0

def z44 : W := mkw 0x05a00ca000000000 0x00b4019400000000 0xe7e00ff800000002 0xfcfc01ff00000000

def z45 : W := mkw 0x225f6157c0000000 0x044bec2af8000000 0x001ff007e0000001 0x0003fe00fc000000

def z46 : W := mkw 0x17fedea81fffdd07 0x02ffdbd503fffba0 0x9ffff6381fffe005 0xf3fffec703fffc00

def z47 : W := mkw 0x00008000014502a8 0x400010000028a055 0x1800000001c71ffc 0x030000000038e3ff

def z48 : W := mkw 0x004a004100410088 0x4009400820082011 0x50d808c300c30998 0x2a1b011860186133

def z49 : W := mkw 0x0b143e1af61afc56 0xa16287c35ec35f8a 0x07247638fe38e000 0x40e48ec71fc71c00

def z50 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x08000000113cf664 0x0100000002279ecc

def z51 : W := mkw 0x27ff6ff7f602b856 0x84ffedfefec0570a 0xf7fffffffe07f87f 0xfeffffffffc0ff0f

def z52 : W := mkw 0x36fff1f54df7c000 0x06dffe3ea9bef800 0xbffff1f81fffe005 0xf7fffe3f03fffc00

def z53 : W := mkw 0x2cebf1fd411c4620 0x259d7e3fa82388c4 0x28e3f1f801380600 0x851c7e3f002700c0

def z54 : W := mkw 0x1efed2083dfff664 0x23dfda4107bffecc 0x9ffff0001ffff665 0xf3fffe0003fffecc

def z55 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x28c381c001c00780 0x85187038003800f0

def z56 : W := mkw 0x084bb35d715d76ec 0x6109766bae2baedd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z57 : W := mkw 0x06fec00001450000 0x00dfd8000028a000 0x9ffff00001c70005 0xf3fffe000038e000

def z58 : W := mkw 0x17fedc028ff7c812 0x82ffdb8051fef902 0xdffff8031fffe81d 0xfbffff0063fffd03

def z59 : W := mkw 0x004a8041014502a8 0x400950082028a055 0x58d808c301c71ffc 0x2b1b01186038e3ff

def z60 : W := mkw 0x26ff6157c0000000 0x04dfec2af8000000 0x87fff007e0000001 0xf0fffe00fc000000

def z61 : W := mkw 0x0da09ea83bbc7f67 0x21b413d507778fec 0xffe00ff81ffcffe6 0xfffc01ff03ff9ffc

def z62 : W := mkw 0x17ffdf47bff7fafe 0xc2fffbe8f7feff5f 0xffffffc7ffffffff 0xfffffff8ffffffff

def z63 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x50db88c700c709f9 0x2a1b7118e018e13f

def z64 : W := mkw 0x05a12fbc5aa81d07 0x00b425f78b5503a0 0xffe7fffcfff81f87 0xfffcffff9fff03f0

def z65 : W := mkw 0x01000e02b602b856 0x802001c056c0570a 0x50000e07fe07f87e 0x0a0001c0ffc0ff0f

def z66 : W := mkw 0x0001810401040220 0x0000302080208044 0xa803810401041667 0x95007020802082cc

def z67 : W := mkw 0x27ff6df7c0410088 0x44ffedbef8082011 0xf7ffffffe0c3099b 0xfefffffffc186133

def z68 : W := mkw 0x0ca1b3bc79bc7765 0x219436778f378eec 0xa8e7f7fcf1fcf7e7 0xd51cfeff9e3f9efc

def z69 : W := mkw 0x025e400000000000 0x004bc80000000000 0x001ff00000000001 0x0003fe0000000000

def z70 : W := mkw 0x00008000014502a8 0x400010000028a055 0x0800000001c00780 0x01000000003800f0

def z71 : W := mkw 0x01000e0012001806 0x002001c002400300 0x070006001e000000 0x40e000c003c00000

def z72 : W := mkw 0x04ea800009e50000 0x009d5000013ca000 0x9ffb80001fff0005 0xf3ff700003ffe000

def z73 : W := mkw 0x004b014500000000 0x00096028a0000000 0xe0db89c700000003 0xbc1b7138e0000000

def z74 : W := mkw 0x27ffedf7c14502a8 0x44fffdbef828a055 0xffffffffe1c71fff 0xfffffffffc38e3ff

def z75 : W := mkw 0x27ff6df7c6028812 0x84ffedbef8c05102 0xf7ffffffee03081b 0xfefffffffdc06103

def z76 : W := mkw 0x27fe4ce386028812 0x84ffc99c70c05102 0x57d808c30e030818 0x2afb011861c06103

def z77 : W := mkw 0x0800900021146260 0x2100120004228c4c 0x000000000004e060 0x0000000000009c0c

def z78 : W := mkw 0x0001231c50081404 0x000024638a010280 0xa827f73cf1381607 0xd504fee79e2702c0

def z79 : W := mkw 0x0efff31c711c7664 0x21dffe638e238ecc 0xaffff73cf13cf667 0xf5fffee79e279ecc

def z80 : W := mkw 0x0901bf1c731c7e66 0x212037e38e638fcc 0xff27ff3cff3cfe67 0xffe4ffe79fe79fcc

def z81 : W := mkw 0x0801231c70083664 0x210024638e0106cc 0x2000073ce0001662 0x040000e79c0002cc

def z82 : W := mkw 0x0000020810081404 0x0000004102010280 0xa820073811381606 0xd50400e7022702c0

def z83 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x67d80fffe0000002 0x2cfb01fffc000000

def z84 : W := mkw 0x27ff6df7c00002a8 0x44ffedbef8000055 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z85 : W := mkw 0x0000020030003044 0x0000004006000608 0x80040604f004f067 0x500080c09e009e0c

def z86 : W := mkw 0x04a002a818a81505 0x00940055031502a0 0xa8e007f811f81786 0xd51c00ff023f02f0

def z87 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xfff80fff1fff1fff 0xffff01ffe3ffe3ff

def z88 : W := mkw 0x035e0e43b643b8de 0xc06bc1c876c8771b 0xd7dc0ec7fec7f9ff 0x7afb81d8ffd8ff3f

def z89 : W := mkw 0x27ff6dffc8a80501 0x04ffedbff91500a0 0xefffffffe1f80783 0xfdfffffffc3f00f0

def z90 : W := mkw 0x03140e0ab60abc56 0x806281c156c1578a 0xff3c0f3fff3ffe7f 0xffe781e7ffe7ffcf

def z91 : W := mkw 0x084bb31c715d7664 0x210976638e2baecc 0xb8fff73cf1fff667 0xf71ffee79e3ffecc

def z92 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x1f2006381ff81f84 0x43e400c703ff03f0

def z93 : W := mkw 0x0801331c70187444 0x210026638e030e88 0xa027f73cf038e003 0xd404fee79e071c00

def z94 : W := mkw 0x0fb5bfbeffbeff77 0xa1f6b7f7dff7dfee 0xffffffffffffffff 0xffffffffffffffff

def z95 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0xbfe001f81ff80784 0xf7fc003f03ff00f0

def z96 : W := mkw 0x2ffffffff11c7664 0x25fffffffe238ecc 0xeffffffff13cf667 0xfdfffffffe279ecc

def z97 : W := mkw 0x004b0145000002a8 0x40096028a0000055 0xe0db89c700001ffb 0xbc1b7138e00003ff

def z98 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2827f738f138e600 0xc504fee71e271cc0

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8c009c001c01f86 0xbf180138003803f0

def z100 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x072006381e380000 0x40e400c703c70000

def z101 : W := mkw 0x16b440000ca28000 0x02d6880001945000 0x070000000e000000 0x00e0000001c00000

def z102 : W := mkw 0x004a000000410000 0x0009400000082000 0x10d8000000c30000 0x221b000000186000

def z103 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0xa8200738113cf666 0xd50400e702279ecc

def z104 : W := mkw 0x17fe4e02bee3b856 0x82ffc9c057dc770a 0xd7dc0e07fec7f87f 0x7afb81c0ffd8ff0f

def z105 : W := mkw 0x0000020030003044 0x0000004006000608 0x000000001004f064 0x0000000002009e0c

def z106 : W := mkw 0x0b15bf1ef71efe76 0xa162b7e3dee3dfce 0xff3fff3fff3ffe7f 0xffe7ffe7ffe7ffcf

def z107 : W := mkw 0x0000900001144000 0x0000120000228800 0x8827f000113ce005 0xd104fe0002279c00

def z108 : W := mkw 0x1efff31c7dfff664 0x23dffe638fbffecc 0xbffff73cfffff667 0xf7fffee79ffffecc

def z109 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x07040600fe00e000 0x40e080c01fc01c00

def z110 : W := mkw 0x07b40ea81eaa9d07 0x00f681d503d553a0 0xfffc0ff81fffff87 0xffff81ff03fffff0

def z111 : W := mkw 0x27b56db6c0000000 0x04f6adb6d8000000 0xa727f73ce0000003 0xd4e4fee79c000000

def z112 : W := mkw 0x0214000004028000 0x0042800000805000 0x971c00001e07e005 0x72e3800003c0fc00

def z113 : W := mkw 0x27ff6df7c4028000 0x04ffedbef8805000 0xf7fffffffe07e007 0xfeffffffffc0fc00

def z114 : W := mkw 0x0000020812081d07 0x00000041024103a0 0x0000000000001f80 0x00000000000003f0

def z115 : W := mkw 0x225fe157c14502a8 0x444bfc2af828a055 0x001ff007e0070079 0x0003fe00fc00e00f

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z117 : W := mkw 0x07b40eaabeaabd57 0x80f681d557d557aa 0x07240638fe38e000 0x40e480c71fc71c00

def z118 : W := mkw 0x0214000284028010 0x8042800050805002 0x0018000300030018 0x0003000060006003

def z119 : W := mkw 0x06ff414500000000 0x00dfe828a0000000 0xe7fff9c700000003 0xfcffff38e0000000

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8d809c701c71fff 0xbf1b0138e038e3ff

def z121 : W := mkw 0x05a00ea01aa01907 0x00b401d403540320 0xd7c00ec01ec01986 0x7af801d803d80330

def z122 : W := mkw 0x23152df7c0000000 0x0462a5bef8000000 0xe71c0fffe0000003 0x7ce381fffc000000

def z123 : W := mkw 0x084bb155615562e8 0x6109762aac2aac5d 0xf8dff9c7e1c7ffff 0xbf1bff38fc38ffff

def z124 : W := mkw 0x100000000ce38000 0x02000000019c7000 0x100000000ec30000 0x0200000001d86000

def z125 : W := mkw 0x06fe400000000000 0x00dfc80000000000 0x87fff00000000001 0xf0fffe0000000000

def z126 : W := mkw 0x0801b11c411c4620 0x21003623882388c4 0xa823f13c013c1667 0x95047e27802782cc

def z127 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x9fe000001ff80004 0xf3fc000003ff0000

def z128 : W := mkw 0x235f6df7c0000000 0x046bedbef8000000 0x601fffffe0000003 0x0c03fffffc000000

def z129 : W := mkw 0x0801b11461146260 0x210036228c228c4c 0xa807f104e104f667 0x9500fe209c209ecc

def z130 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x401c0e07e007f87b 0x080381c0fc00ff0f

def z131 : W := mkw 0x21012df7c0000000 0x042025bef8000000 0x60000fffe0000002 0x0c0001fffc000000

def z132 : W := mkw 0x25eb6df7c0000000 0x04bd6dbef8000000 0x60e3ffffe0000002 0x8c1c7ffffc000000

def z133 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x5fc008c01ff81f84 0x2bf8011803ff03f0

def z134 : W := mkw 0x37fffdf7cdf7c2a8 0x46ffffbef9bef855 0xffffffffffffffff 0xffffffffffffffff

def z135 : W := mkw 0x214b2df7c0000000 0x042965bef8000000 0xe0db8fffe0000003 0xbc1b71fffc000000

def z136 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2823f73ce1381662 0x85047ee79c2702cc

def z137 : W := mkw 0x00010145000002a8 0x40002028a0000055 0xf8c009c701c01ffe 0xbf180138e03803ff

def z138 : W := mkw 0x27fffdf7c1144000 0x04ffffbef8228800 0xeffffffff13ce007 0xfdfffffffe279c00

def z139 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x0fe7f0001ff8e000 0xc1fcfe0003ff1c00

def z140 : W := mkw 0x01000e02b2003856 0x802001c05640070a 0xd7000e07fe00187e 0x7ae001c0ffc0030f

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0xd000080000001806 0x3a00010000000300

def z142 : W := mkw 0x000002081aa81d07 0x00000041035503a0 0x000000001e380000 0x0000000003c70000

def z143 : W := mkw 0x104ad00001554000 0x02095a00002aa800 0x0003f00000000000 0x00007e0000000000

def z144 : W := mkw 0x014b8fed134d1faf 0x402971fda269a3f5 0xf8db8fff01c71fff 0xbf1b71ffe038e3ff

def z145 : W := mkw 0x00010145000002a8 0x40002028a0000055 0x600009c700001ffa 0x0c000138e00003ff

def z146 : W := mkw 0x05a00ea83aa83d47 0x00b401d5075507a8 0xffe40ffcfffcffe7 0xfffc81ff9fff9ffc

def z147 : W := mkw 0x225e404380000000 0x044bc80870000000 0x0018000300000000 0x0003000060000000

def z148 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x0807f004f13cf665 0x0100fe009e279ecc

def z149 : W := mkw 0x27fe6cb2c0000000 0x04ffcd9658000000 0x87fff638e0000001 0xf0fffec71c000000

def z150 : W := mkw 0x16b450000cb2c000 0x02d68a0001965800 0x072470001e38e000 0x40e48e0003c71c00

def z151 : W := mkw 0x000000000aa00903 0x0000000001540120 0x100000000ec00980 0x0200000001d80130

def z152 : W := mkw 0x0800020830083664 0x21000041060106cc 0x0000000000001660 0x00000000000002cc

def z153 : W := mkw 0x37fedce38df7c000 0x06ffdb9c71bef800 0xdffff8c31fffe005 0xfbffff1863fffc00

def z154 : W := mkw 0x084bb35d711c7664 0x2109766bae238ecc 0xe8fffffff13cf667 0xfd1ffffffe279ecc

def z155 : W := mkw 0x014b8f47b3453afe 0xc02971e8f668a75f 0xf8db8fc7e1c71fff 0xbf1b71f8fc38e3ff

def z156 : W := mkw 0x0001910401144220 0x0000322080228844 0xa827f104113cf667 0xd504fe2082279ecc

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0xa020073800000002 0xd40400e700000000

def z158 : W := mkw 0x24eb61f540000000 0x049d6c3ea8000000 0xa0e7f7fce0000003 0xd41cfeff9c000000

def z159 : W := mkw 0x16fe40000ce38000 0x02dfc800019c7000 0x17d800000ec30000 0x22fb000001d86000

def z160 : W := mkw 0x03140c0286028812 0x8062818050c05102 0xd71808070e07187f 0x3ae30100e1c0e30f

def z161 : W := mkw 0x17fedea81fffdd07 0x02ffdbd503fffba0 0xfffffff81fffff87 0xffffffff03fffff0

def z162 : W := mkw 0x16ffd1450df7c000 0x02dffa28a1bef800 0xfffff9c71fffe007 0xffffff38e3fffc00

def z163 : W := mkw 0x03140eaab60abd57 0x806281d556c157aa 0xf71c0ffffe07ffff 0x7ee381ffffc0ffff

def z164 : W := mkw 0x07fe4c0280000000 0x00ffc98050000000 0xc7fffe07e0000003 0xf8ffffc0fc000000

def z165 : W := mkw 0x37fffdf7cdf7c000 0x06ffffbef9bef800 0xffffffffffffe007 0xfffffffffffffc00

def z166 : W := mkw 0x02140202b402b054 0x804280405680560a 0x801c0607f007f07f 0x500380c0fe00fe0f

def z167 : W := mkw 0x225f6157c0000000 0x044bec2af8000000 0xe0dff9c7e0000003 0xbc1bff38fc000000

def z168 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x971c0600fe07e005 0x72e380c01fc0fc00

def z169 : W := mkw 0x27ff6fffdaa81d07 0x04ffedfffb5503a0 0xfffffffffff81f87 0xffffffffffff03f0

def z170 : W := mkw 0x000000002402a050 0x800000000480540a 0x000000000007e078 0x000000000000fc0f

def z171 : W := mkw 0x100092003ff7f856 0x8200124007feff0a 0x180000001ffff87c 0x0300000003ffff0f

def z172 : W := mkw 0x27ff6ff7f602b856 0x84ffedfefec0570a 0xe7fffffffe00e003 0xfcffffffffc01c00

def z173 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xf8e7fffcf1fcffe7 0xff1cffff9e3f9ffc

def z174 : W := mkw 0x16fed0a80dffc501 0x02dfda1501bff8a0 0xbffff1f81fffe785 0xf7fffe3f03fffcf0

def z175 : W := mkw 0x05a00ca80aa80d03 0x00b40195015501a0 0x7fe009f80ff80f80 0xaffc013f01ff01f0

def z176 : W := mkw 0x17fede02bff7f856 0x82ffdbc057feff0a 0xdffffe07fffff87f 0xfbffffc0ffffff0f

def z177 : W := mkw 0x100092081fffdd07 0x0200124103fffba0 0x180000001fffff84 0x0300000003fffff0

def z178 : W := mkw 0x180092083dfff664 0x2300124107bffecc 0x180000001ffff664 0x0300000003fffecc

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x800400001004e005 0x5000800002009c00

def z180 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x47dff8c7e0000001 0x28fbff18fc000000

def z181 : W := mkw 0x16fed2081fffdd07 0x02dfda4103fffba0 0x9ffff0001fffff85 0xf3fffe0003fffff0

def z182 : W := mkw 0x000082003747bafe 0xc000104006e8f75f 0x180000001fc7fffc 0x0300000003f8ffff

def z183 : W := mkw 0x17fede001ff7d806 0x02ffdbc003fefb00 0xdffffe001ffff807 0xfbffffc003ffff00

def z184 : W := mkw 0x03140c0286028812 0x8062818050c05102 0xd71c08031e07e81d 0x7ae3810063c0fd03

def z185 : W := mkw 0x004a800001450000 0x000950000028a000 0x98db800001c70005 0xb31b70000038e000

def z186 : W := mkw 0x000000a800080501 0x00000015000100a0 0x200001f800000780 0x0400003f000000f0

def z187 : W := mkw 0x03140e02b2003856 0x806281c05640070a 0xc71c0e07e000187b 0x78e381c0fc00030f

def z188 : W := mkw 0x27ffedf7c14502a8 0x44fffdbef828a055 0xe7ffffffe007007b 0xfcfffffffc00e00f

def z189 : W := mkw 0x0000800001040220 0x0000100000208044 0x0800000001041664 0x01000000002082cc

def z190 : W := mkw 0x05a00ca00aa00903 0x00b4019401540120 0x57c008c00ec00980 0x2af8011801d80130

def z191 : W := mkw 0x05a12db440000000 0x00b425b688000000 0xe7e7fffce0000003 0xfcfcffff9c000000

def z192 : W := mkw 0x0da1bfbc7bbc7f67 0x21b437f78f778fec 0xffe7fffcfffcffe7 0xfffcffff9fff9ffc

def z193 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x98db800701c7007d 0xb31b7000e038e00f

def z194 : W := mkw 0x1cebf11c49fd4620 0x239d7e23893fa8c4 0x28e3f13801f80600 0x851c7e27003f00c0

def z195 : W := mkw 0x004ba155414502a8 0x4009742aa828a055 0xf8ffffffe1c71fff 0xff1ffffffc38e3ff

def z196 : W := mkw 0x0001b11441144000 0x0000362288228800 0xa827f73cf13ce007 0xd504fee79e279c00

def z197 : W := mkw 0x084bb35d715d76ec 0x6109766bae2baedd 0xa83ff73ff13ff67f 0xd507fee7fe27fecf

def z198 : W := mkw 0x00010145000002a8 0x40002028a0000055 0x0000000700000078 0x00000000e000000f

def z199 : W := mkw 0x104a90000df7c000 0x0209520001bef800 0x98db80001fffe005 0xb31b700003fffc00

def z200 : W := mkw 0x0001810401040220 0x0000302080208044 0x0003800400040061 0x000070008000800c

def z201 : W := mkw 0x14a090000df7c000 0x0294120001bef800 0x9fe000001fffe004 0xf3fc000003fffc00

def z202 : W := mkw 0x035e8e02b747b856 0x806bd1c056e8f70a 0xdfdf8e07ffc7f87f 0xfbfbf1c0fff8ff0f

def z203 : W := mkw 0x0801231c70083664 0x210024638e0106cc 0xa004073cf004f667 0x540080e79e009ecc

def z204 : W := mkw 0x004b0145004102a8 0x40096028a0082055 0x70d809c700c31ffa 0x2e1b0138e01863ff

def z205 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x28db81c701c707f9 0x851b7038e038e0ff

def z206 : W := mkw 0x01000e0012001806 0x002001c002400300 0xd7000e001e001806 0x7ae001c003c00300

def z207 : W := mkw 0x0000000006028812 0x8000000000c05102 0x100000000e030818 0x0200000001c06103

def z208 : W := mkw 0x03140c0280000000 0x0062818050000000 0xc71c0e07e0000003 0x78e381c0fc000000

def z209 : W := mkw 0x080092083bbc7f67 0x2100124107778fec 0x180000001ffcffe4 0x0300000003ff9ffc

def z210 : W := mkw 0x27fe4ce380000000 0x04ffc99c70000000 0xe7f80ffb00000002 0xfcff01ff60000000

def z211 : W := mkw 0x0b149e0ab71efe76 0xa16293c156e3dfce 0xdf1c0e07ff3ffe7f 0x7be381c0ffe7ffcf

def z212 : W := mkw 0x21012fffd2081d07 0x042025fffa4103a0 0x60000fffe0001f82 0x0c0001fffc0003f0

def z213 : W := mkw 0x24ebe1f5414502a8 0x449d7c3ea828a055 0x28e3f1f801c00780 0x851c7e3f003800f0

def z214 : W := mkw 0x0000020810081404 0x0000004102010280 0x0020063810380000 0x400400c702070000

def z215 : W := mkw 0x0801b31c715d76ec 0x610036638e2baedd 0xb827f73cf1ffffff 0xd704fee79e3fffff

def z216 : W := mkw 0x225fe157c14502a8 0x444bfc2af828a055 0xf8dff9c7e1c71fff 0xbf1bff38fc38e3ff

def z217 : W := mkw 0x06ff611440000000 0x00dfec2288000000 0xa7fff73ce0000003 0xf4fffee79c000000

def z218 : W := mkw 0x17fede02bff7f856 0x82ffdbc057feff0a 0x9ffff600ffffe005 0xf3fffec01ffffc00

def z219 : W := mkw 0x03140c0280000000 0x0062818050000000 0x07040600e0000000 0x40e080c01c000000

def z220 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x08e0000001f80000 0x811c0000003f0000

def z221 : W := mkw 0x27ff6ff7f2003856 0x84ffedfefe40070a 0xe7ffffffe000187b 0xfcfffffffc00030f

def z222 : W := mkw 0x27ff6fffd0081404 0x04ffedfffa010280 0xeffffffff1381607 0xfdfffffffe2702c0

def z223 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xffdc0fc7ffc7ffff 0xfffb81f8fff8ffff

def z224 : W := mkw 0x0000201040000000 0x0000040208000000 0x00247638e0000000 0x40048ec71c000000

def z225 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x67200ff81e381f82 0x4ce401ff03c703f0

def z226 : W := mkw 0x00000002a0002050 0x800000005400040a 0x00000007e0000078 0x00000000fc00000f

def z227 : W := mkw 0x2ffffffff71efe76 0xa5fffffffee3dfce 0xffffffffff3ffe7f 0xffffffffffe7ffcf

def z228 : W := mkw 0x0001010400000000 0x0000202080000000 0xa003810400000003 0x9400702080000000

def z229 : W := mkw 0x16b450000cb2c000 0x02d68a0001965800 0x9fe470001ff8e004 0xf3fc8e0003ff1c00

def z230 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x001b800700070079 0x00037000e000e00f

def z231 : W := mkw 0x06b4400000000000 0x00d6880000000000 0x0724700000000000 0x40e48e0000000000

def z232 : W := mkw 0x0801b11c411c4620 0x21003623882388c4 0xa827f138113ce605 0xd504fe2702279cc0

def z233 : W := mkw 0x0800301840184400 0x2100060308030880 0x0020703800380000 0x00040e0700070000

def z234 : W := mkw 0x0000020830083444 0x0000004106010688 0xa824073cf13cf667 0xd50480e79e279ecc

def z235 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x601b89c700071ffb 0x0c037138e000e3ff

def z236 : W := mkw 0x29012ffff0083664 0x252025fffe0106cc 0x60000fffe0001662 0x0c0001fffc0002cc

def z237 : W := mkw 0x05a00ea812081d07 0x00b401d5024103a0 0xe7e00ff800001f82 0xfcfc01ff000003f0

def z238 : W := mkw 0x04a002081aa81d07 0x00940041035503a0 0x9fe000001ff81f84 0xf3fc000003ff03f0

def z239 : W := mkw 0x0800301060106040 0x210006020c020c08 0x00047000e000e000 0x00008e001c001c00

def z240 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x47040e07fe00f87a 0x48e081c0ffc01f0f

def z241 : W := mkw 0x0000020810081404 0x0000004102010280 0x2000073800001602 0x040000e7000002c0

def z242 : W := mkw 0x27fe4ce380000000 0x04ffc99c70000000 0x47d808c300000000 0x28fb011860000000

def z243 : W := mkw 0x01000e0012001806 0x002001c002400300 0xd7180e071e07187f 0x7ae301c0e3c0e30f

def z244 : W := mkw 0x03140c02a402a050 0x806281805480540a 0xc71c0e07e007e07b 0x78e381c0fc00fc0f

def z245 : W := mkw 0x01000ea812081d07 0x002001d5024103a0 0xf8c00ff801c01f86 0xbf1801ff003803f0

def z246 : W := mkw 0x0da1bfbc5bbc5f27 0x21b437f78b778be4 0xffe3fff81ff81f86 0xfffc7fff03ff03f0

def z247 : W := mkw 0x37fffff7fff7f856 0x86fffffefffeff0a 0xfffffffffffff87f 0xffffffffffffff0f

def z248 : W := mkw 0x24eb61f540000000 0x049d6c3ea8000000 0xe0fbf9ff00000003 0xbc1f7f3fe0000000

def z249 : W := mkw 0x27fe4eeb9aa81d07 0x04ffc9dd735503a0 0xfff80ffb1ff81f86 0xffff01ff63ff03f0

def z250 : W := mkw 0x0000800001450000 0x000010000028a000 0x1800000001c70004 0x030000000038e000

def z251 : W := mkw 0x07b40eaa9eaa9d17 0x80f681d553d553a2 0xfff80ffb1ffb1f9e 0xffff01ff63ff63f3

def z252 : W := mkw 0x04a0020818a81404 0x0094004103150280 0xbfe007381ff81606 0xf7fc00e703ff02c0

def z253 : W := mkw 0x004b814501040220 0x00097028a0208044 0xe8db89c701041667 0xbd1b7138e02082cc

def z254 : W := mkw 0x325ff157c557c000 0x064bfe2af8aaf800 0x001ff007e007e001 0x0003fe00fc00fc00

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x8820000011380004 0xd104000002270000

def z256 : W := mkw 0x0ca1b1bc49bc4721 0x21943637893788e4 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z257 : W := mkw 0x20012157c0000000 0x0400242af8000000 0x00000007e0000000 0x00000000fc000000

def z258 : W := mkw 0x27ff6fffd2081d07 0x04ffedfffa4103a0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z259 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x2fe007f81ff80780 0xc5fc00ff03ff00f0

def z260 : W := mkw 0x0800321870187444 0x210006430e030e88 0xa8247738f138f606 0xd5048ee71e271ec0

def z261 : W := mkw 0x004b014500000000 0x00096028a0000000 0x20c381c000000000 0x8418703800000000

def z262 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x17c000000ec00000 0x22f8000001d80000

def z263 : W := mkw 0x0ca1b31c79bc7664 0x219436638f378ecc 0xbfe7f73cfffcf667 0xf7fcfee79fff9ecc

def z264 : W := mkw 0x2fff7ffff0187444 0x25ffeffffe030e88 0xe7fffffff038e003 0xfcfffffffe071c00

def z265 : W := mkw 0x0801b31471147264 0x210036628e228e4c 0x8007f604f004f067 0x5000fec09e009e0c

def z266 : W := mkw 0x0a15b31ef51ef674 0xa142b663dea3dece 0xa83ff73ff13ff67f 0xd507fee7fe27fecf

def z267 : W := mkw 0x15eadea81bfd5d07 0x02bd5bd5037faba0 0xffe3fff81ff81f86 0xfffc7fff03ff03f0

def z268 : W := mkw 0x225f6157e402a050 0x844bec2afc80540a 0x001ff007e007e079 0x0003fe00fc00fc0f

def z269 : W := mkw 0x04a0900009b44000 0x0094120001368800 0x9fe7f0001ffce005 0xf3fcfe0003ff9c00

def z270 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xf83fff3ff13ffe7f 0xff07ffe7fe27ffcf

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800010001001606 0x95000020002002c0

def z272 : W := mkw 0x1801b31c7dfff664 0x230036638fbffecc 0xb827f73cfffff667 0xd704fee79ffffecc

def z273 : W := mkw 0x16fed0410df7c088 0x42dfda0821bef811 0xdffff8c31fffe99d 0xfbffff1863fffd33

def z274 : W := mkw 0x14ebd14509f542a8 0x429d7a28a13ea855 0x28e3f1c001f80780 0x851c7e38003f00f0

def z275 : W := mkw 0x27fe4ce380410088 0x44ffc99c70082011 0x57d808c300c30998 0x2afb011860186133

def z276 : W := mkw 0x1000900009f54000 0x02001200013ea800 0x0800000001f80000 0x01000000003f0000

def z277 : W := mkw 0x09012fbc72083f67 0x212025f78e4107ec 0x60000ffce0001fe2 0x0c0001ff9c0003fc

def z278 : W := mkw 0x02140002a402a050 0x804280005480540a 0x971c0007fe07e07d 0x72e38000ffc0fc0f

def z279 : W := mkw 0x14ead0a809fd4501 0x029d5a15013fa8a0 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z280 : W := mkw 0x16fff1144df7c000 0x02dffe2289bef800 0xbffff73cffffe007 0xf7fffee79ffffc00

def z281 : W := mkw 0x000002081aa81d07 0x00000041035503a0 0xf8c009c01ff81f86 0xbf18013803ff03f0

def z282 : W := mkw 0x2fb5ffbef11c7664 0x25f6bff7de238ecc 0xaf27f73cf13cf667 0xd5e4fee79e279ecc

def z283 : W := mkw 0x03140e0296029816 0x806281c052c05302 0xd7180e031e03181e 0x7ae301c063c06303

def z284 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xd7200e381e381806 0x7ae401c703c70300

def z285 : W := mkw 0x004b215540000000 0x0009642aa8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z286 : W := mkw 0x27fe4ce38aa00903 0x04ffc99c71540120 0x57d808c30ec00980 0x2afb011861d80130

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000001c01f84 0x03000000003803f0

def z288 : W := mkw 0x24ebe1f5414502a8 0x449d7c3ea828a055 0xf8fbf9ff01c71fff 0xbf1f7f3fe038e3ff

def z289 : W := mkw 0x27ff6df7c8a00000 0x04ffedbef9140000 0xfffffffffff80007 0xffffffffffff0000

def z290 : W := mkw 0x000082081bed1faf 0x40001041037da3f5 0x180000001fff1ffc 0x0300000003ffe3ff

def z291 : W := mkw 0x08009208315d76ec 0x61001241062baedd 0x1800000011fffffc 0x03000000023fffff

def z292 : W := mkw 0x03148e02b747bafe 0xc06291c056e8f75f 0xdf1c0e07ffc7ffff 0x7be381c0fff8ffff

def z293 : W := mkw 0x16fed0000df7c2a8 0x42dfda0001bef855 0x9ffff0001ffffffd 0xf3fffe0003ffffff

def z294 : W := mkw 0x004b834d1bed1faf 0x40097069a37da3f5 0xf8db89c71fff1fff 0xbf1b7138e3ffe3ff

def z295 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xffffffffe1c01f87 0xfffffffffc3803f0

def z296 : W := mkw 0x04a000a008a00101 0x0094001401140020 0x00c000c000c00180 0x0018001800180030

def z297 : W := mkw 0x17fe4ea81eeb9d07 0x02ffc9d503dd73a0 0xfff80ff81ffb1f86 0xffff01ff03ff63f0

def z298 : W := mkw 0x104b91450df7c2a8 0x42097228a1bef855 0xf8db89c71fffffff 0xbf1b7138e3ffffff

def z299 : W := mkw 0x15a09ea81fffdd07 0x02b413d503fffba0 0xffe00ff81fffff86 0xfffc01ff03fffff0

def z300 : W := mkw 0x07ff8fefbfefbfff 0xc0fff1fdf7fdf7ff 0xffff8fffffffffff 0xfffff1ffffffffff

def z301 : W := mkw 0x0214000280000000 0x0042800050000000 0x001c0007e0000001 0x00038000fc000000

def z302 : W := mkw 0x03140e0016029806 0x006281c002c05300 0xd71c0e001e07f807 0x7ae381c003c0ff00

def z303 : W := mkw 0x27fe4ee3b602b856 0x84ffc9dc76c0570a 0xd7dc0ec7fe07f87f 0x7afb81d8ffc0ff0f

def z304 : W := mkw 0x004b814501450000 0x00097028a028a000 0xf8db89c701c70007 0xbf1b7138e038e000

def z305 : W := mkw 0x0001014500000000 0x00002028a0000000 0x600009c700000002 0x0c000138e0000000

def z306 : W := mkw 0x27b46eb2f602b856 0x84f68dd65ec0570a 0x07247638fe00e000 0x40e48ec71fc01c00

def z307 : W := mkw 0x17b45ea81ebadd07 0x02f68bd503d75ba0 0xffe47ff81ff8ff86 0xfffc8fff03ff1ff0

def z308 : W := mkw 0x0000000008a00000 0x0000000001140000 0x180000001ff80004 0x0300000003ff0000

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x9018000000070005 0x320300000000e000

def z310 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x9fe006381ff80004 0xf3fc00c703ff0000

def z311 : W := mkw 0x05a00ea012001806 0x00b401d402400300 0xf7e00ff81e001806 0xfefc01ff03c00300

def z312 : W := mkw 0x25a12df7c0000000 0x04b425bef8000000 0xe7e00fffe0000002 0xfcfc01fffc000000

def z313 : W := mkw 0x01000e081aa81d07 0x002001c1035503a0 0xdf000e001ff81f86 0x7be001c003ff03f0

def z314 : W := mkw 0x16b450000cb2c000 0x02d68a0001965800 0x973c70001e3fe005 0x72e78e0003c7fc00

def z315 : W := mkw 0x100010000cb2c000 0x0200020001965800 0x000000001e38e000 0x0000000003c71c00

def z316 : W := mkw 0x21012df7c00002a8 0x442025bef8000055 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z317 : W := mkw 0x025f8147a547a2f8 0xc04bf028f4a8f45f 0xf8df89c7e1c7ffff 0xbf1bf138fc38ffff

def z318 : W := mkw 0x2cebf3fd711c7664 0x259d7e7fae238ecc 0xa8e7f7fcf13cf667 0xd51cfeff9e279ecc

def z319 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x571808031e07f87c 0x2ae3010063c0ff0f

def z320 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x071c0607fe07e079 0x40e380c0ffc0fc0f

def z321 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xa8c381c401c417e7 0x95187038803882fc

def z322 : W := mkw 0x16fe40000ce38000 0x02dfc800019c7000 0x97dc00001ec7e005 0x72fb800003d8fc00

def z323 : W := mkw 0x0000020032003856 0x800000400640070a 0x0000000000001878 0x000000000000030f

def z324 : W := mkw 0x0801b31c771efe76 0xa10036638ee3dfce 0xb827f73cff3ffe7f 0xd704fee79fe7ffcf

def z325 : W := mkw 0x05a00eaabaa83d57 0x80b401d5575507aa 0xffe00ffffff81ffe 0xfffc01ffffff03ff

def z326 : W := mkw 0x0001810401040220 0x0000302080208044 0xf8c389c401c41fe7 0xbf187138803883fc

def z327 : W := mkw 0x05eb8fed1bed1faf 0x40bd71fda37da3f5 0xffe38ff81ff81f86 0xfffc71ff03ff03f0

def z328 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xe8db89c701c00783 0xbd1b7138e03800f0

def z329 : W := mkw 0x16fe40000ce38000 0x02dfc800019c7000 0x97fff0000ec30001 0xf2fffe0001d86000

def z330 : W := mkw 0x0214000004028000 0x0042800000805000 0x171800000e030000 0x22e3000001c06000

def z331 : W := mkw 0x0801b31c7bbc7f67 0x210036638f778fec 0xb827f73cfffcffe7 0xd704fee79fff9ffc

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0c009c000000002 0xbc18013800000000

def z334 : W := mkw 0x16fed2003ff7f856 0x82dfda4007feff0a 0x9ffff0001ffff87d 0xf3fffe0003ffff0f

def z335 : W := mkw 0x004b014500000000 0x00096028a0000000 0xf8db89c701c01f87 0xbf1b7138e03803f0

def z336 : W := mkw 0x27b56df7c0000000 0x04f6adbef8000000 0x67247fffe0000002 0x4ce48ffffc000000

def z337 : W := mkw 0x25a12fffdaa81d07 0x04b425fffb5503a0 0xffe00ffffff81f86 0xfffc01ffffff03f0

def z338 : W := mkw 0x04eb81ed09ed07a9 0x409d703da13da0f5 0x28e381f801f80780 0x851c703f003f00f0

def z339 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0xf8e009f801f81f86 0xbf1c013f003f03f0

def z340 : W := mkw 0x0000020810081404 0x0000004102010280 0xf8e00ff811f81f86 0xff1c01ff023f03f0

def z341 : W := mkw 0x06fed00001144000 0x00dfda0000228800 0x8ffff000113ce005 0xf1fffe0002279c00

def z342 : W := mkw 0x16fe40410ce38088 0x42dfc808219c7011 0x57d808c30ec30998 0x2afb011861d86133

def z343 : W := mkw 0x035f0f47b602b856 0x806be1e8f6c0570a 0xf7df8fc7fe07f87f 0xfefbf1f8ffc0ff0f

def z344 : W := mkw 0x27ff6ffffeaabd57 0x84ffedffffd557aa 0xffffffffffffffff 0xffffffffffffffff

def z345 : W := mkw 0x14ead00009f54000 0x029d5a00013ea800 0x9fe3f0001ff80004 0xf3fc7e0003ff0000

def z346 : W := mkw 0x27ffeff7f747bafe 0xc4fffdfefee8f75f 0xffffffffffc7ffff 0xfffffffffff8ffff

def z347 : W := mkw 0x0800b218711c7444 0x210016430e238e88 0x8827f638f13ce005 0xd104fec71e279c00

def z348 : W := mkw 0x004a004100410088 0x4009400820082011 0xd0d808c700c719ff 0x3a1b0118e018e33f

def z349 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x88040604f13cf667 0x510080c09e279ecc

def z350 : W := mkw 0x02140202b602b856 0x8042804056c0570a 0x101c0007fe07f87d 0x02038000ffc0ff0f

def z351 : W := mkw 0x17b45e02beb2f856 0x82f68bc057d65f0a 0x07247600fe38e000 0x40e48ec01fc71c00

def z352 : W := mkw 0x07b40e02bea2b856 0x80f681c057d4570a 0xdffc0e07fffff87f 0xfbff81c0ffffff0f

def z353 : W := mkw 0x07fe4ca000000000 0x00ffc99400000000 0xe7fffff800000003 0xfcffffff00000000

def z354 : W := mkw 0x1efff35d7dfff6ec 0x63dffe6bafbffedd 0xffffffffffffffff 0xffffffffffffffff

def z355 : W := mkw 0x1eb5f31c7dbef664 0x23d6be638fb7decc 0xaf27f73cff3cf667 0xd5e4fee79fe79ecc

def z356 : W := mkw 0x004b834d114d16ac 0x40097069a229a2d5 0xf8fb8fff11ff1fff 0xff1f71ffe23fe3ff

def z357 : W := mkw 0x09012f1ef2083e76 0xa12025e3de4107ce 0x60000f3fe0001e7a 0x0c0001e7fc0003cf

def z358 : W := mkw 0x21012ff7f2003856 0x842025fefe40070a 0x60000fffe000187a 0x0c0001fffc00030f

def z359 : W := mkw 0x05a08ea81bed1faf 0x40b411d5037da3f5 0xffe00ff81fff1ffe 0xfffc01ff03ffe3ff

def z360 : W := mkw 0x0000020030003044 0x0000004006000608 0x00000604e0001062 0x000000c09c00020c

def z361 : W := mkw 0x17fedca00df7c000 0x02ffdb9401bef800 0xfffffff81fffe007 0xffffffff03fffc00

def z362 : W := mkw 0x03149e02b716f856 0x806293c056e2df0a 0xdf3ffe07ff3ff87f 0xfbe7ffc0ffe7ff0f

def z363 : W := mkw 0x004a900001554000 0x00095200002aa800 0x98fff00011ffe005 0xf31ffe00023ffc00

def z364 : W := mkw 0x27b46eb2f602b856 0x84f68dd65ec0570a 0xd73c7e3ffe07f87f 0x7ae78fc7ffc0ff0f

def z365 : W := mkw 0x004a800001450000 0x000950000028a000 0xd8db880701c7187f 0xbb1b7100e038e30f

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x400008070000187a 0x08000100e000030f

def z367 : W := mkw 0x27ffedf7c1040220 0x04fffdbef8208044 0xefffffffe1041667 0xfdfffffffc2082cc

def z368 : W := mkw 0x0000100000104000 0x0000020000020800 0x002470001038e000 0x40048e0002071c00

def z369 : W := mkw 0x07fe4e02b602b856 0x80ffc9c056c0570a 0xd7fffe07fe07f87f 0xfaffffc0ffc0ff0f

def z370 : W := mkw 0x23152ff7f602b856 0x8462a5fefec0570a 0xf71c0ffffe07f87f 0x7ee381ffffc0ff0f

def z371 : W := mkw 0x0801331c70187664 0x210026638e030ecc 0x2024773cf038f662 0x44048ee79e071ecc

def z372 : W := mkw 0x125ed0000557c000 0x024bda0000aaf800 0x883ff000113fe005 0xd107fe000227fc00

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x8027f00000000001 0xd004fe0000000000

def z374 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xf7ffffffe007187f 0xfefffffffc00e30f

def z375 : W := mkw 0x0801930c311c7664 0x2100326186238ecc 0xa8038104113cf667 0x9500702082279ecc

def z376 : W := mkw 0x08009208371efe76 0xa100124106e3dfce 0x180000001f3ffe7c 0x0300000003e7ffcf

def z377 : W := mkw 0x0001231470003044 0x000024628e000608 0xa027f73cf004f067 0xd404fee79e009e0c

def z378 : W := mkw 0x37ff6df7cce38000 0x06ffedbef99c7000 0xf7ffffffeec30003 0xfefffffffdd86000

def z379 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1ffbf0000ffb0000 0xa3ff7e0001ff6000

def z380 : W := mkw 0x021402003402b044 0x0042804006805608 0x971c0604fe07f067 0x72e380c09fc0fe0c

def z381 : W := mkw 0x21012df7c0000000 0x042025bef8000000 0xe027ffffe0000003 0xdc04fffffc000000

def z382 : W := mkw 0x084bb15d415d46a8 0x6109762ba82ba8d5 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z383 : W := mkw 0x1efff11c4dffc620 0x23dffe2389bff8c4 0xbffff1381fffe605 0xf7fffe2703fffcc0

def z384 : W := mkw 0x0801235d700836ec 0x6100246bae0106dd 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z385 : W := mkw 0x0801b11461146260 0x210036228c228c4c 0x8827f004f13ce065 0xd104fe009e279c0c

def z386 : W := mkw 0x004b9145015542a8 0x40097228a02aa855 0xf8fff9c711ffffff 0xff1fff38e23fffff

def z387 : W := mkw 0x14ead00009f54000 0x029d5a00013ea800 0x98fbf00001ff0005 0xb31f7e00003fe000

def z388 : W := mkw 0x004b014500000000 0x00096028a0000000 0x001b800700000001 0x00037000e0000000

def z389 : W := mkw 0x05a18fac1bac1f27 0x00b431f5837583e4 0xffe38ffc1ffc1fe7 0xfffc71ff83ff83fc

def z390 : W := mkw 0x0214000004028000 0x0042800000805000 0xd71c08071e07f87f 0x7ae38100e3c0ff0f

def z391 : W := mkw 0x16fed0000557c000 0x02dfda0000aaf800 0x87fff0000007e001 0xf0fffe000000fc00

def z392 : W := mkw 0x0001830431043264 0x000030608620864c 0xa8078704f104f667 0xd500f0e09e209ecc

def z393 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xd01b88070007187f 0x3a037100e000e30f

def z394 : W := mkw 0x1cebf31c79fd7664 0x239d7e638f3faecc 0xa8e7f73cf1fcf667 0xd51cfee79e3f9ecc

def z395 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x38c381c001c71ffc 0x871870380038e3ff

def z396 : W := mkw 0x17b45ea81ebadd07 0x02f68bd503d75ba0 0x072476381e38e000 0x40e48ec703c71c00

def z397 : W := mkw 0x36fff157cdf7c000 0x06dffe2af9bef800 0x9ffff007ffffe005 0xf3fffe00fffffc00

def z398 : W := mkw 0x17fedc028df7c000 0x02ffdb8051bef800 0xdffffe07ffffe007 0xfbffffc0fffffc00

def z399 : W := mkw 0x05a00ea83eaabd57 0x80b401d507d557aa 0xffe00ff81ffffffe 0xfffc01ff03ffffff

def z400 : W := mkw 0x06ffc145014502a8 0x40dff828a028a055 0xfffff9c701c71fff 0xffffff38e038e3ff

def z401 : W := mkw 0x05ea8ea81bed1d07 0x00bd51d5037da3a0 0xfffb8ff81fff1f87 0xffff71ff03ffe3f0

def z402 : W := mkw 0x01000ea812081d07 0x002001d5024103a0 0x0000063800000000 0x000000c700000000

def z403 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x87040604fe04f067 0x50e080c09fc09e0c

def z404 : W := mkw 0x14ead00009f54000 0x029d5a00013ea800 0x88e7f00011fce005 0xd11cfe00023f9c00

def z405 : W := mkw 0x035f0d4780000000 0x006be1a8f0000000 0xe7df8fc7e0000003 0xfcfbf1f8fc000000

def z406 : W := mkw 0x204b615540000000 0x04096c2aa8000000 0x0003f00000000000 0x00007e0000000000

def z407 : W := mkw 0x0a15b31c751ef664 0x2142b6638ea3decc 0xbf3ff73cff3ff667 0xf7e7fee79fe7fecc

def z408 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x78db89c301c30f98 0xaf1b7138603861f3

def z409 : W := mkw 0x2ffffdf7e1146260 0x25ffffbefc228c4c 0xe7ffffffe004e063 0xfcfffffffc009c0c

def z410 : W := mkw 0x03140c02a602a852 0x8062818054c0550a 0x571c0807ee07e879 0x2ae38100fdc0fd0f

def z411 : W := mkw 0x00018104014502a8 0x400030208028a055 0xb803810401c71fff 0x970070208038e3ff

def z412 : W := mkw 0x04eb81ed09ed07a9 0x409d703da13da0f5 0xf8fb89ff01ff1fff 0xbf1f713fe03fe3ff

def z413 : W := mkw 0x06fe400008a00000 0x00dfc80001140000 0x9ffff0001ff80005 0xf3fffe0003ff0000

def z414 : W := mkw 0x01000e02b2003856 0x802001c05640070a 0x00000600e0000000 0x000000c01c000000

def z415 : W := mkw 0x100090000df7c2a8 0x4200120001bef855 0x180000001ffffffc 0x0300000003ffffff

def z416 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xe7e00ff81e380002 0xfcfc01ff03c70000

def z417 : W := mkw 0x0801211c40080620 0x21002423880100c4 0x2000013800000600 0x04000027000000c0

def z418 : W := mkw 0x17b45e02beb2f856 0x82f68bc057d65f0a 0xd73c7e07fe3ff87f 0x7ae78fc0ffc7ff0f

def z419 : W := mkw 0x0000000020002040 0x0000000004000408 0x00040004e004e061 0x000080009c009c0c

def z420 : W := mkw 0x0001211440000000 0x0000242288000000 0x0007f004e0000001 0x0000fe009c000000

def z421 : W := mkw 0x03140e02b0003044 0x006281c056000608 0xc71c0e07f004f067 0x78e381c0fe009e0c

def z422 : W := mkw 0x37b47cb2ccb2c000 0x06f68f9659965800 0x07247638fe38e000 0x40e48ec71fc71c00

def z423 : W := mkw 0x27fe6cf3c0000000 0x04ffcd9e78000000 0x47fc7efbe0000000 0x68ff8fdf7c000000

def z424 : W := mkw 0x2ffffffff15d76ec 0x65fffffffe2baedd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z425 : W := mkw 0x01000eaab2083d57 0x802001d5564107aa 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z426 : W := mkw 0x0000020030003044 0x0000004006000608 0xd01c0e07f007f87f 0x7a0381c0fe00ff0f

def z427 : W := mkw 0x01000c0282000812 0x8020018050400102 0x4000080300000818 0x0800010060000103

def z428 : W := mkw 0x03150f47b602bafe 0xc062a1e8f6c0575f 0xf71c0fc7fe07ffff 0x7ee381f8ffc0ffff

def z429 : W := mkw 0x035f8d4787478aba 0xc06bf1a8f0e8f157 0xffdb89c70fc71fff 0xbffb7138e1f8e3ff

def z430 : W := mkw 0x1fffffbc7fffff67 0x23fffff78fffffec 0xfffffffcffffffe7 0xffffffff9ffffffc

def z431 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x08fff00001ffe001 0x811ffe00003ffc00

def z432 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0x0020003800380000 0x0004000700070000

def z433 : W := mkw 0x05eb8de50be50bab 0x40bd71bca17ca175 0xffdb89c70fc71fff 0xbffb7138e1f8e3ff

def z434 : W := mkw 0x00018145014502a8 0x40003028a028a055 0x780009c701c71ffe 0x0f000138e038e3ff

def z435 : W := mkw 0x0da03eb87ab87d47 0x21b407d70f570fa8 0xffe47ff8fff8ff86 0xfffc8fff1fff1ff0

def z436 : W := mkw 0x21002cb2c0000000 0x0420059658000000 0x00000638e0000000 0x000000c71c000000

def z437 : W := mkw 0x0000000004028000 0x0000000000805000 0x100000001e07e004 0x0200000003c0fc00

def z438 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2007f73ce004f663 0x0400fee79c009ecc

def z439 : W := mkw 0x03140e0292001806 0x006281c052400300 0xd71c0e07fe001807 0x7ae381c0ffc00300

def z440 : W := mkw 0x0801b35d711c76ec 0x6100366bae238edd 0xe827fffff13cffff 0xdd04fffffe279fff

def z441 : W := mkw 0x0901bfbc731c7f67 0x212037f78e638fec 0xe827fffcf13cffe7 0xdd04ffff9e279ffc

def z442 : W := mkw 0x004a804101450088 0x400950082028a011 0xd8db88c301c7099d 0xbb1b71186038e133

def z443 : W := mkw 0x0000004100000088 0x4000000820000011 0x400008c300000998 0x0800011860000133

def z444 : W := mkw 0x37ffffffdfffdd07 0x06fffffffbfffba0 0xffffffffffffff87 0xfffffffffffffff0

def z445 : W := mkw 0x27ffcde7814502a8 0x44fff9bcf028a055 0xffdb89c701c71fff 0xbffb7138e038e3ff

def z446 : W := mkw 0x27b44ca280000000 0x04f6899450000000 0x0700000000000000 0x00e0000000000000

def z447 : W := mkw 0x16b4d0000db6c000 0x02d69a0001b6d800 0x8f27f0001f3ce005 0xd1e4fe0003e79c00

def z448 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x17040600fe07f87c 0x42e080c01fc0ff0f

def z449 : W := mkw 0x0801b11c411c4620 0x21003623882388c4 0xa827f73ce1380603 0xd504fee79c2700c0

def z450 : W := mkw 0x084ba35d714d36ec 0x6109746bae29a6dd 0xf8db8fffe1c71fff 0xbf1b71fffc38e3ff

def z451 : W := mkw 0x16ffd1450df7c2a8 0x42dffa28a1bef855 0xbffff1c01fffe785 0xf7fffe3803fffcf0

def z452 : W := mkw 0x16fe50000cb2c000 0x02dfca0001965800 0x87fff0001e38e001 0xf0fffe0003c71c00

def z453 : W := mkw 0x0000020810081404 0x0000004102010280 0x0800000011381604 0x01000000022702c0

def z454 : W := mkw 0x21000ce380000000 0x0420019c70000000 0x400008c300000000 0x0800011860000000

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000400041067 0x100000008000820c

def z456 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x073ff0001e3fe001 0x40e7fe0003c7fc00

def z457 : W := mkw 0x05a00ca000000000 0x00b4019400000000 0xffe00ff801c01f86 0xfffc01ff003803f0

def z458 : W := mkw 0x01000c0000000000 0x0020018000000000 0xc7000e0000000002 0x78e001c000000000

def z459 : W := mkw 0x04eb814509e502a8 0x409d7028a13ca055 0xfffb89c71fff1fff 0xffff7138e3ffe3ff

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x80040604e0000003 0x500080c09c000000

def z461 : W := mkw 0x25eb6df540000000 0x04bd6dbea8000000 0xe7e3fff800000002 0xfcfc7fff00000000

def z462 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xfffff9c01fffff87 0xffffff3803fffff0

def z463 : W := mkw 0x0801b11441144220 0x2100362288228844 0x0003f00000000000 0x00007e0000000000

def z464 : W := mkw 0x04a000a000000000 0x0094001400000000 0x20e001f800000000 0x841c003f00000000

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0xc018080700000003 0x38030100e0000000

def z466 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x68e00ff801f81f82 0x8d1c01ff003f03f0

def z467 : W := mkw 0x1efff1146df7e260 0x23dffe228dbefc4c 0x9ffff004ffffe065 0xf3fffe009ffffc0c

def z468 : W := mkw 0x0800120830187444 0x2100024106030e88 0x000000001038e000 0x0000000002071c00

def z469 : W := mkw 0x27fe4ce380000000 0x04ffc99c70000000 0xc7fff8c300000001 0xf8ffff1860000000

def z470 : W := mkw 0x01000e02b2003856 0x802001c05640070a 0xc0040e07f004f87f 0x580081c0fe009f0f

def z471 : W := mkw 0x07b40eaabeaabd57 0x80f681d557d557aa 0xffe40ff8fff8ff86 0xfffc81ff1fff1ff0

def z472 : W := mkw 0x000002081aa81d07 0x00000041035503a0 0xb82007381ff81f86 0xd70400e703ff03f0

def z473 : W := mkw 0x025f8147a547a2f8 0xc04bf028f4a8f45f 0x001f8007e007e079 0x0003f000fc00fc0f

def z474 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2800073cf13cf666 0x050000e79e279ecc

def z475 : W := mkw 0x0b143e1af61afc56 0xa16287c35ec35f8a 0xd73c7e3ffe3ff87f 0x7ae78fc7ffc7ff0f

def z476 : W := mkw 0x125e400004438000 0x024bc80000887000 0x0018000000030000 0x0003000000006000

def z477 : W := mkw 0x07b40eaabeaabd57 0x80f681d557d557aa 0xd73c0e3ffe3ff87f 0x7ae781c7ffc7ff0f

def z478 : W := mkw 0x1efef2187dfff444 0x23dfde430fbffe88 0x9ffff638ffffe005 0xf3fffec71ffffc00

def z479 : W := mkw 0x0801b31c511c5624 0x210036638a238ac4 0xa823f73811381606 0xd5047ee7022702c0

def z480 : W := mkw 0x14ebd14509f542a8 0x429d7a28a13ea855 0xf8fbf9c701ff1fff 0xbf1f7f38e03fe3ff

def z481 : W := mkw 0x00009208111c5404 0x0000124102238a80 0xa827f738113cf607 0xd504fee702279ec0

def z482 : W := mkw 0x2fff6ffff0083664 0x25ffedfffe0106cc 0xe7ffffffe0001663 0xfcfffffffc0002cc

def z483 : W := mkw 0x1a5ff31c755ff664 0x234bfe638eabfecc 0xa83ff73cf13ff667 0xd507fee79e27fecc

def z484 : W := mkw 0x2a5ff35ff11c7664 0x254bfe6bfe238ecc 0xa83ff73ff13cf667 0xd507fee7fe279ecc

def z485 : W := mkw 0x05a00ea810081404 0x00b401d502010280 0xefe00ff811381606 0xfdfc01ff022702c0

def z486 : W := mkw 0x03140c0284028000 0x0062818050805000 0xd71c0e07fe07e007 0x7ae381c0ffc0fc00

def z487 : W := mkw 0x01010fed12081faf 0x402021fda24103f5 0x60000fff00001ffa 0x0c0001ffe00003ff

def z488 : W := mkw 0x021490000516c000 0x0042920000a2d800 0x9f3ff0001f3fe005 0xf3e7fe0003e7fc00

def z489 : W := mkw 0x25eb6ffd5aa81d07 0x04bd6dffab5503a0 0xffe3fff81ff81f86 0xfffc7fff03ff03f0

def z490 : W := mkw 0x05a00ca000000000 0x00b4019400000000 0x47c008c000000000 0x28f8011800000000

def z491 : W := mkw 0x0b15bf16f716fa76 0xa162b7e2dee2df4e 0xd71ffe07fe07f87f 0x7ae3ffc0ffc0ff0f

def z492 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x57180e07ee03187a 0x2ae301c0fdc0630f

def z493 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x27e7f7f8e0000000 0xc4fcfeff1c000000

def z494 : W := mkw 0x07b40ca280000000 0x00f6819450000000 0xe7fc0fffe0000003 0xfcff81fffc000000

def z495 : W := mkw 0x235f6d57c0000000 0x046bedaaf8000000 0xc71ffe07e0000003 0x78e3ffc0fc000000

def z496 : W := mkw 0x125fd1450557c2a8 0x424bfa28a0aaf855 0x001ff0070007e079 0x0003fe00e000fc0f

def z497 : W := mkw 0x025f8145054782a8 0x404bf028a0a8f055 0xffdf89c71fc7ffff 0xfffbf138e3f8ffff

def z498 : W := mkw 0x00010145000002a8 0x40002028a0000055 0xf01809c700071fff 0x3e030138e000e3ff

def z499 : W := mkw 0x03152f16f602b856 0x8062a5e2dec0570a 0xf73fff3ffe07f87f 0xfee7ffe7ffc0ff0f

def z500 : W := mkw 0x14a0500008b04000 0x02940a0001160800 0x0020700000380000 0x00040e0000070000

def z501 : W := mkw 0x0da1bfbc7bbc7f67 0x21b437f78f778fec 0xaf27f73cff3cf667 0xd5e4fee79fe79ecc

def z502 : W := mkw 0x3ffffffffdfff664 0x27ffffffffbffecc 0xfffffffffffff667 0xfffffffffffffecc

def z503 : W := mkw 0x01010f47b2003afe 0xc02021e8f640075f 0x60000fc7e0001ffa 0x0c0001f8fc0003ff

def z504 : W := mkw 0x17fedeaabffffd57 0x82ffdbd557ffffaa 0xffffffffffffffff 0xffffffffffffffff

def z505 : W := mkw 0x0a15b116e516e270 0xa142b622dca2dc4e 0x001ff007e007e079 0x0003fe00fc00fc0f

def z506 : W := mkw 0x17fe4ca00ee38903 0x02ffc99401dc7120 0x57d808c00ec30980 0x2afb011801d86130

def z507 : W := mkw 0x125ed0000df7c000 0x024bda0001bef800 0x181ff0001fffe005 0x0303fe0003fffc00

def z508 : W := mkw 0x05a00ca00aa00903 0x00b4019401540120 0xffc009c00fc01f86 0xbff8013801f803f0

def z509 : W := mkw 0x16b4d0000df7c000 0x02d69a0001bef800 0x1f2470001fffe004 0x43e48e0003fffc00

def z510 : W := mkw 0x14ea400008e10000 0x029d4800011c2000 0x00c0000000c00000 0x0018000000180000

def z511 : W := mkw 0x035f8d47814502a8 0x406bf1a8f028a055 0xffdf8fc7e1c71fff 0xfffbf1f8fc38e3ff

def z512 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xa81b81070107167f 0x95037020e020e2cf

def z513 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8c389c001c01f86 0xbf187138003803f0

def z514 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x67fbf9fb00000000 0xacff7f3f60000000

def z515 : W := mkw 0x135ede02b757f856 0x826bdbc056eaff0a 0xd71ffe07fe07f87f 0x7ae3ffc0ffc0ff0f

def z516 : W := mkw 0x0b15bf1ef71efe76 0xa162b7e3dee3dfce 0xaf27f73cff3cf667 0xd5e4fee79fe79ecc

def z517 : W := mkw 0x27ff6fffdaa81d07 0x04ffedfffb5503a0 0xe7fffffffe380003 0xfcffffffffc70000

def z518 : W := mkw 0x0001810401040220 0x0000302080208044 0xf81b890701071e7f 0xbf037120e020e3cf

def z519 : W := mkw 0x2a5ff157e1146260 0x254bfe2afc228c4c 0x001ff007e004e061 0x0003fe00fc009c0c

def z520 : W := mkw 0x004a004100410088 0x4009400820082011 0x00c000c000c00180 0x0018001800180030

def z521 : W := mkw 0x1a5ff1146557e260 0x234bfe228caafc4c 0x001ff004e007e061 0x0003fe009c00fc0c

def z522 : W := mkw 0x03158f06b706ba76 0x8062b1e0d6e0d74e 0xff1f8f07ff07fe7f 0xffe3f1e0ffe0ffcf

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018000700070079 0x00030000e000e00f

def z524 : W := mkw 0x00008000014502a8 0x400010000028a055 0x0000000000070078 0x000000000000e00f

def z525 : W := mkw 0x014b8f4513451aae 0x402971e8a268a355 0xffdb8fc71fc71fff 0xfffb71f8e3f8e3ff

def z526 : W := mkw 0x125ed002a557e050 0x824bda0054aafc0a 0x001ff007e007e079 0x0003fe00fc00fc0f

def z527 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x181b800701c71ffd 0x03037000e038e3ff

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x50c008c000c00980 0x2a18011800180130

def z529 : W := mkw 0x0000000800080400 0x0000000100010080 0x2820013801380600 0x85040027002700c0

def z530 : W := mkw 0x06fe400000000000 0x00dfc80000000000 0x07d8000000000000 0x20fb000000000000

def z531 : W := mkw 0x0000000808a80501 0x00000001011500a0 0x0800000001f80780 0x01000000003f00f0

def z532 : W := mkw 0x03140c0286028812 0x8062818050c05102 0x070000000e000000 0x00e0000001c00000

def z533 : W := mkw 0x05ea0ce10ae1098b 0x40bd419c215c2131 0x57d808c30ec30998 0x2afb011861d86133

def z534 : W := mkw 0x01000e0012001806 0x002001c002400300 0x40000e0000001802 0x080001c000000300

def z535 : W := mkw 0x03140c0280000000 0x0062818050000000 0xd71c0e07e007187f 0x7ae381c0fc00e30f

def z536 : W := mkw 0x27ff6df7e402a050 0x84ffedbefc80540a 0xe7ffffffe007e07b 0xfcfffffffc00fc0f

def z537 : W := mkw 0x24a060b040000000 0x04940c1608000000 0x0020703800000000 0x00040e0700000000

def z538 : W := mkw 0x004a800001450000 0x000950000028a000 0x08c3800001c00000 0x8118700000380000

def z539 : W := mkw 0x27ffedf7c1450000 0x04fffdbef828a000 0xffffffffe1c70007 0xfffffffffc38e000

def z540 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x0027f63cf03ce061 0x4004fec79e079c0c

def z541 : W := mkw 0x16fed002adf7e050 0x82dfda0055befc0a 0x9ffff007ffffe07d 0xf3fffe00fffffc0f

def z542 : W := mkw 0x07fe4ea81aa81d07 0x00ffc9d5035503a0 0xfffffff81ff81f87 0xffffffff03ff03f0

def z543 : W := mkw 0x0b15bf1ef11c7664 0x2162b7e3de238ecc 0xef3fff3ff13cf667 0xfde7ffe7fe279ecc

def z544 : W := mkw 0x0da1bfbc711c7664 0x21b437f78e238ecc 0xefe7fffcf13cf667 0xfdfcffff9e279ecc

def z545 : W := mkw 0x05a00ca000000000 0x00b4019400000000 0x0720063800000000 0x40e400c700000000

def z546 : W := mkw 0x0000900001144000 0x0000120000228800 0x08000000113ce004 0x0100000002279c00

def z547 : W := mkw 0x0000800001040000 0x0000100000208000 0x8803800001040005 0x9100700000208000

def z548 : W := mkw 0x05ea0ee91ae91d8f 0x40bd41dd235d23b1 0xfff80ffb1ffb1f9e 0xffff01ff63ff63f3

def z549 : W := mkw 0x03140c0280000000 0x0062818050000000 0x4718080300000000 0x28e3010060000000

def z550 : W := mkw 0x0b152f1ef60abe76 0xa162a5e3dec157ce 0xf71c0f3ffe07fe7f 0x7ee381e7ffc0ffcf

def z551 : W := mkw 0x08009008011c4620 0x21001201002388c4 0x0800000001380600 0x01000000002700c0

def z552 : W := mkw 0x16fed2081dffd404 0x02dfda4103bffa80 0xbffff7381ffff607 0xf7fffee703fffec0

def z553 : W := mkw 0x000002003602b856 0x8000004006c0570a 0xd01808071e07f87f 0x3a030100e3c0ff0f

def z554 : W := mkw 0x004b8345314532ec 0x40097068a628a65d 0xf8df8fc7f1c7ffff 0xff1bf1f8fe38ffff

def z555 : W := mkw 0x05a00ca00aa00903 0x00b4019401540120 0xf7e00ff80ec00982 0xfefc01ff01d80130

def z556 : W := mkw 0x05eb0de500000000 0x00bd61bca0000000 0xe7fb8fff00000003 0xfcff71ffe0000000

def z557 : W := mkw 0x04a0000008a00000 0x0094000001140000 0xffe009c01ff81f86 0xfffc013803ff03f0

def z558 : W := mkw 0x27b46ebadaa81d07 0x04f68dd75b5503a0 0xffe47ff8fff81f86 0xfffc8fff1fff03f0

def z559 : W := mkw 0x05a00ca808a80501 0x00b40195011500a0 0xefe00ff801f80782 0xfdfc01ff003f00f0

def z560 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x0003800000000000 0x0000700000000000

def z561 : W := mkw 0x02140002a402a050 0x804280005480540a 0x00040000e000e000 0x000080001c001c00

def z562 : W := mkw 0x27ff6df7caa00903 0x04ffedbef9540120 0xf7ffffffeec00983 0xfefffffffdd80130

def z563 : W := mkw 0x0801b11c611c6660 0x210036238c238ccc 0x2827f13ce13ce661 0x8504fe279c279ccc

def z564 : W := mkw 0x0801211460002260 0x210024228c00044c 0x00000004e0000060 0x000000009c00000c

def z565 : W := mkw 0x05eb0fed1aa81d07 0x00bd61fda35503a0 0xfffb8fff1ff81f87 0xffff71ffe3ff03f0

def z566 : W := mkw 0x0800b218711c7664 0x210016430e238ecc 0x08247638f13cf664 0x41048ec71e279ecc

def z567 : W := mkw 0x37fefcb2cdf7c000 0x06ffdf9659bef800 0x9ffff638ffffe005 0xf3fffec71ffffc00

def z568 : W := mkw 0x0000020012001806 0x0000004002400300 0x100000001e001804 0x0200000003c00300

def z569 : W := mkw 0x01000ea812081d07 0x002001d5024103a0 0xf7000ff81e001f86 0x7ee001ff03c003f0

def z570 : W := mkw 0x025e800005478000 0x004bd00000a8f000 0x9fdf80001fc7e005 0xf3fbf00003f8fc00

def z571 : W := mkw 0x0801231c70083664 0x210024638e0106cc 0xa820073cf1381666 0xd50400e79e2702cc

def z572 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xaf2007381f381606 0xd5e400e703e702c0

def z573 : W := mkw 0x004b810401450220 0x000970208028a044 0xb8db810401c71667 0xb71b70208038e2cc

def z574 : W := mkw 0x000002003602b856 0x8000004006c0570a 0x90040604fe07f87f 0x520080c09fc0ff0f

def z575 : W := mkw 0x0001010400000220 0x0000202080000044 0x2000010400001662 0x04000020800002cc

def z576 : W := mkw 0x084bb15d415d46a8 0x6109762ba82ba8d5 0xf8fbf9ff01ff1fff 0xbf1f7f3fe03fe3ff

def z577 : W := mkw 0x0000020030003044 0x0000004006000608 0x00040600f000e000 0x400080c01e001c00

def z578 : W := mkw 0x125ed0000557c000 0x024bda0000aaf800 0x98dff00001c7e005 0xb31bfe000038fc00

def z579 : W := mkw 0x17fe4c028ee38812 0x82ffc98051dc7102 0x57d808030ec30818 0x2afb010061d86103

def z580 : W := mkw 0x01000ea812081d07 0x002001d5024103a0 0xe8200ff811381f86 0xdd0401ff022703f0

def z581 : W := mkw 0x05a00ca00aa00903 0x00b4019401540120 0x070000000e000000 0x00e0000001c00000

def z582 : W := mkw 0x004a000000000000 0x0009400000000000 0x80db800000000001 0xb01b700000000000

def z583 : W := mkw 0x34ebf1f549f54000 0x069d7e3ea93ea800 0x28e3f1f801f80000 0x851c7e3f003f0000

def z584 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2823f138113cf664 0x85047e2702279ecc

def z585 : W := mkw 0x00008000014502a8 0x400010000028a055 0xd818080701c71fff 0x3b030100e038e3ff

def z586 : W := mkw 0x27ffedf7c14502a8 0x44fffdbef828a055 0xefffffffe1c00783 0xfdfffffffc3800f0

def z587 : W := mkw 0x0000000000410088 0x4000000000082011 0x1000000000c30998 0x0200000000186133

def z588 : W := mkw 0x0000920031147044 0x0000124006228e08 0x8827f604f13cf067 0xd104fec09e279e0c

def z589 : W := mkw 0x1eb472187cbaf444 0x23d68e430f975e88 0x07247638fe38e000 0x40e48ec71fc71c00

def z590 : W := mkw 0x01000e0012001806 0x002001c002400300 0xffc00fc01fc01f86 0xfff801f803f803f0

def z591 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x57e00ef81ef80980 0x6afc01df03df0130

def z592 : W := mkw 0x03140e0abeaabd57 0x806281c157d557aa 0xdf1c0e07ffffffff 0x7be381c0ffffffff

def z593 : W := mkw 0x084b934d315d76ec 0x61097269a62baedd 0xf8db89c711ffffff 0xbf1b7138e23fffff

def z594 : W := mkw 0x084bb155615562e8 0x6109762aac2aac5d 0x001ff007e007e079 0x0003fe00fc00fc0f

def z595 : W := mkw 0x000002083eaabd57 0x8000004107d557aa 0x180000001ffffffc 0x0300000003ffffff

def z596 : W := mkw 0x05a00ca00aa00903 0x00b4019401540120 0xdfe008c01ff80984 0xfbfc011803ff0130

def z597 : W := mkw 0x2901bffff11c7664 0x252037fffe238ecc 0xe827fffff13cf667 0xdd04fffffe279ecc

def z598 : W := mkw 0x01000c0002000802 0x0020018000400100 0x570008000e000800 0x2ae0010001c00100

def z599 : W := mkw 0x26ff61f7c0000000 0x04dfec3ef8000000 0x20fff1ffe0000001 0x841ffe3ffc000000

def z600 : W := mkw 0x14ead0000df7c000 0x029d5a0001bef800 0x18e3f0001fffe004 0x831c7e0003fffc00

def z601 : W := mkw 0x0001211440000000 0x0000242288000000 0x2023f13800000000 0x84047e2700000000

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0x98c0000001c00004 0xb318000000380000

def z603 : W := mkw 0x004a004100000000 0x0009400820000000 0x40d808c300000000 0x281b011860000000

def z604 : W := mkw 0x27b46cb2c0000000 0x04f68d9658000000 0xc73c7e3fe0000003 0x78e78fc7fc000000

def z605 : W := mkw 0x0000020010001004 0x0000004002000200 0x8000060010001006 0x500000c002000200

def z606 : W := mkw 0x13149e02bff7f856 0x826293c057feff0a 0xdf1c0e07fffff87f 0x7be381c0ffffff0f

def z607 : W := mkw 0x17ffdfed1fffdfaf 0x42fffbfda3fffbf5 0xffffffff1fffffff 0xffffffffe3ffffff

def z608 : W := mkw 0x125ed0000557c000 0x024bda0000aaf800 0x971ff0001e07e005 0x72e3fe0003c0fc00

def z609 : W := mkw 0x27ff6ff7f0003044 0x04ffedfefe000608 0xe7fffffff004f067 0xfcfffffffe009e0c

def z610 : W := mkw 0x0901bf1ef31c7e76 0xa12037e3de638fce 0xe827ff3ff13cfe7f 0xdd04ffe7fe279fcf

def z611 : W := mkw 0x37fffdf7c557c000 0x06ffffbef8aaf800 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z612 : W := mkw 0x05a00ca008a00000 0x00b4019401140000 0xffe00ff81ff80006 0xfffc01ff03ff0000

def z613 : W := mkw 0x01000e0812081c06 0x002001c102410380 0xff200f381f381e06 0xffe401e703e703c0

def z614 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xc71c0e07fe00e003 0x78e381c0ffc01c00

def z615 : W := mkw 0x16fed2003df7f044 0x02dfda4007befe08 0x9ffff604fffff067 0xf3fffec09ffffe0c

def z616 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xdffff8071ffff87f 0xfbffff00e3ffff0f

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x28c001c001c00780 0x85180038003800f0

def z618 : W := mkw 0x24ea40e100000000 0x049d481c20000000 0x00c000c000000000 0x0018001800000000

def z619 : W := mkw 0x05eb8de5014502a8 0x40bd71bca028a055 0xfffb8fff01c71fff 0xffff71ffe038e3ff

def z620 : W := mkw 0x00008000014502a8 0x400010000028a055 0xf8c009c001c71ffe 0xbf1801380038e3ff

def z621 : W := mkw 0x22146012c0000000 0x04428c0258000000 0x00047000e0000000 0x00008e001c000000

def z622 : W := mkw 0x27ff4de780000000 0x04ffe9bcf0000000 0xe7db89c700000003 0xbcfb7138e0000000

def z623 : W := mkw 0x16fed00009f54000 0x02dfda00013ea800 0x8ffff00001f80001 0xf1fffe00003f0000

def z624 : W := mkw 0x27b46ebadaa81d07 0x04f68dd75b5503a0 0x07247638fe380000 0x40e48ec71fc70000

def z625 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x8827f000113cf665 0xd104fe0002279ecc

def z626 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x072000001e380000 0x40e4000003c70000

def z627 : W := mkw 0x0214000004028000 0x0042800000805000 0x001c00000007e001 0x000380000000fc00

def z628 : W := mkw 0x0801a31c710c3664 0x210034638e2186cc 0xa803873ce1041667 0x950070e79c2082cc

def z629 : W := mkw 0x37ff7df7ccb2c000 0x06ffefbef9965800 0xe7fffffffe38e003 0xfcffffffffc71c00

def z630 : W := mkw 0x004a004100410088 0x4009400820082011 0xf8d809c301c31f9e 0xbf1b0138603863f3

def z631 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87e0000000000000 0xf0fc000000000000

def z632 : W := mkw 0x004a800001450000 0x000950000028a000 0xf8db89c001c71f87 0xbf1b71380038e3f0

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x600009c000001f82 0x0c000138000003f0

def z634 : W := mkw 0x035f8f47b747bafe 0xc06bf1e8f6e8f75f 0xd71f8e07fe07f87f 0x7ae3f1c0ffc0ff0f

def z635 : W := mkw 0x004b014500410088 0x40096028a0082011 0xf0db89c700c3099b 0xbe1b7138e0186133

def z636 : W := mkw 0x2ffffdffc11c4620 0x25ffffbff82388c4 0xefffffffe1380603 0xfdfffffffc2700c0

def z637 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xb8db81c001c70785 0xb71b70380038e0f0

def z638 : W := mkw 0x0000900001144000 0x0000120000228800 0x0007f0000004e001 0x0000fe0000009c00

def z639 : W := mkw 0x035e0c438643889a 0xc06bc18870c87113 0x57d808c30ec30998 0x2afb011861d86133

def z640 : W := mkw 0x00010145000002a8 0x40002028a0000055 0x200001c000000780 0x04000038000000f0

def z641 : W := mkw 0x01000e0032003846 0x002001c006400708 0xd7040e04fe04f867 0x7ae081c09fc09f0c

def z642 : W := mkw 0x0801b11461146260 0x210036228c228c4c 0xa027f73ce004e063 0xd404fee79c009c0c

def z643 : W := mkw 0x16ffd1450df7c2a8 0x42dffa28a1bef855 0x9ffff0071fffe07d 0xf3fffe00e3fffc0f

def z644 : W := mkw 0x06b400000ca28000 0x00d6800001945000 0x9ffc00001fffe005 0xf3ff800003fffc00

def z645 : W := mkw 0x17fedca00ff7c903 0x02ffdb9401fef920 0xdffff8c01fffe985 0xfbffff1803fffd30

def z646 : W := mkw 0x16fe40000ce38000 0x02dfc800019c7000 0x9ff800001ffb0004 0xf3ff000003ff6000

def z647 : W := mkw 0x16ffc1450de782a8 0x42dff828a1bcf055 0xffdb89c70fc71fff 0xbffb7138e1f8e3ff

def z648 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1fd800001fffe004 0x23fb000003fffc00

def z649 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x77c00ff80ec01f82 0x2ef801ff01d803f0

def z650 : W := mkw 0x27ffefffdbed1faf 0x44fffdfffb7da3f5 0xffffffffffff1fff 0xffffffffffffe3ff

def z651 : W := mkw 0x16fec0000de78000 0x02dfd80001bcf000 0x9fdb80000fc70005 0xb3fb700001f8e000

def z652 : W := mkw 0x37fffdf7c9f54000 0x06ffffbef93ea800 0xefffffffe1f80003 0xfdfffffffc3f0000

def z653 : W := mkw 0x100090000557c000 0x0200120000aaf800 0x000000000007e000 0x000000000000fc00

def z654 : W := mkw 0x01000e003602b856 0x802001c006c0570a 0xd7000e001e07f87e 0x7ae001c003c0ff0f

def z655 : W := mkw 0x214badf7c14502a8 0x442975bef828a055 0xf8db8fffe1c71fff 0xbf1b71fffc38e3ff

def z656 : W := mkw 0x07b40eaa9aa81d07 0x00f681d5535503a0 0xfffc0ffffff81f87 0xffff81ffffff03f0

def z657 : W := mkw 0x0001810401040220 0x0000302080208044 0x2803810001000600 0x85007020002000c0

def z658 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x571c0e03fe03e818 0x6ae381c07fc07d03

def z659 : W := mkw 0x16fe50000cf3c000 0x02dfca00019e7800 0x17fc70001efbe000 0x62ff8e0003df7c00

def z660 : W := mkw 0x07b40ea2b602b856 0x80f681d456c0570a 0xf7fc0ffffe07f87f 0xfeff81ffffc0ff0f

def z661 : W := mkw 0x0001830c110c1624 0x00003061822182c4 0xa823873c113c1667 0xd50470e7822782cc

def z662 : W := mkw 0x06fe400004028000 0x00dfc80000805000 0x97fff0001e07e005 0xf2fffe0003c0fc00

def z663 : W := mkw 0x004b83453747bafe 0xc0097068a6e8f75f 0xf8db89c71fc7ffff 0xbf1b7138e3f8ffff

def z664 : W := mkw 0x125fd1450557c2a8 0x424bfa28a0aaf855 0xf8dff9c701c7ffff 0xbf1bff38e038ffff

def z665 : W := mkw 0x0001a11441040220 0x0000342288208044 0xa827f73ce1041667 0xd504fee79c2082cc

def z666 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x17dff0000ec7e001 0x22fbfe0001d8fc00

def z667 : W := mkw 0x24eb61fd48a80501 0x049d6c3fa91500a0 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z668 : W := mkw 0x2fb47ebaf0187444 0x25f68fd75e030e88 0x07247638f038e000 0x40e48ec71e071c00

def z669 : W := mkw 0x27ff6ff7d2001806 0x04ffedfefa400300 0xf7fffffffe001807 0xfeffffffffc00300

def z670 : W := mkw 0x1fffff1efffffe76 0xa3ffffe3dfffffce 0xffffff3ffffffe7f 0xffffffe7ffffffcf

def z671 : W := mkw 0x04ea400000000000 0x009d480000000000 0x00e3f00000000000 0x801c7e0000000000

def z672 : W := mkw 0x07b40ea2bea2b957 0x80f681d457d4572a 0xd7dc0ec7fec7f9ff 0x7afb81d8ffd8ff3f

def z673 : W := mkw 0x0800321870187444 0x210006430e030e88 0x8024763cf03cf067 0x50048ec79e079e0c

def z674 : W := mkw 0x02140002a402a050 0x804280005480540a 0xd01c0807e007f87f 0x3a038100fc00ff0f

def z675 : W := mkw 0x100090000df7c000 0x0200120001bef800 0x9827f0001fffe005 0xd304fe0003fffc00

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000000007187c 0x020000000000e30f

def z677 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xd7040e00fe00f806 0x7ae081c01fc01f00

def z678 : W := mkw 0x27b46cb2c0000000 0x04f68d9658000000 0xe7e47ff8e0000002 0xfcfc8fff1c000000

def z679 : W := mkw 0x0214000000000000 0x0042800000000000 0x871c000000000001 0x70e3800000000000

def z680 : W := mkw 0x121450000412c000 0x02428a0000825800 0x000470000000e000 0x00008e0000001c00

def z681 : W := mkw 0x04a002a81aa81d07 0x00940055035503a0 0x38e001f81ff81f84 0x871c003f03ff03f0

def z682 : W := mkw 0x004a004100410088 0x4009400820082011 0x0018000300030018 0x0003000060006003

def z683 : W := mkw 0x004a800001450000 0x000950000028a000 0x001b800000070001 0x000370000000e000

def z684 : W := mkw 0x16ffd1040df7c220 0x02dffa2081bef844 0xbffff1041ffff667 0xf7fffe2083fffecc

def z685 : W := mkw 0x2ffffffffbbc7f67 0x25ffffffff778fec 0xfffffffffffcffe7 0xffffffffffff9ffc

def z686 : W := mkw 0x05a10fed1aa81faf 0x40b421fda35503f5 0xffe00fff1ff81ffe 0xfffc01ffe3ff03ff

def z687 : W := mkw 0x200121f540000000 0x0400243ea8000000 0x200001f800000000 0x0400003f00000000

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x5018080300030818 0x2a03010060006103

def z689 : W := mkw 0x01000c0280000000 0x0020018050000000 0x40000e07e0000002 0x080001c0fc000000

def z690 : W := mkw 0x01000ca000000000 0x0020019400000000 0x60000ff800000002 0x0c0001ff00000000

def z691 : W := mkw 0x084bb35d715d76ec 0x6109766bae2baedd 0xa8e7f7fcf1fcf7e7 0xd51cfeff9e3f9efc

def z692 : W := mkw 0x000002003602b856 0x8000004006c0570a 0x000000001e00e000 0x0000000003c01c00

def z693 : W := mkw 0x0debbffd7bfd7fef 0x61bd77ffaf7faffd 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x01000e02b2003856 0x802001c05640070a 0xd0180e07e007187f 0x3a0301c0fc00e30f

def z695 : W := mkw 0x07b40ca28ea28913 0x80f6819451d45122 0x57d808c30ec30998 0x2afb011861d86133

def z696 : W := mkw 0x05a09ea81bbc5d07 0x00b413d503778ba0 0xffe7fff81ffcff87 0xfffcffff03ff9ff0

def z697 : W := mkw 0x0000900001144000 0x0000120000228800 0x0823f00001380000 0x81047e0000270000

def z698 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x68c389c701c01ffa 0x8d187138e03803ff

def z699 : W := mkw 0x235f6f57f602b856 0x846bedeafec0570a 0xd71ffe07fe07f87f 0x7ae3ffc0ffc0ff0f

def z700 : W := mkw 0x0801231c70083664 0x210024638e0106cc 0xa027f73ce0001663 0xd404fee79c0002cc

def z701 : W := mkw 0x26ff61f540000000 0x04dfec3ea8000000 0xa7fff1f800000001 0xf4fffe3f00000000

def z702 : W := mkw 0x004a8000014502a8 0x400950000028a055 0x98db800001c71ffd 0xb31b70000038e3ff

def z703 : W := mkw 0x00000000000002a8 0x4000000000000055 0x0000000000001ff8 0x00000000000003ff

def z704 : W := mkw 0x27fe4ce380000000 0x04ffc99c70000000 0xc7dc0ec7e0000003 0x78fb81d8fc000000

def z705 : W := mkw 0x05a00e001aa01806 0x00b401c003540300 0xdfe00e001ff81806 0xfbfc01c003ff0300

def z706 : W := mkw 0x00018145010402a8 0x40003028a0208055 0xe80389c701041fff 0x9d007138e02083ff

def z707 : W := mkw 0x0001211440000000 0x0000242288000000 0x2027f738e0000000 0xc404fee71c000000

def z708 : W := mkw 0x03140eaab60abd57 0x806281d556c157aa 0xffdc0fffffc7ffff 0xfffb81fffff8ffff

def z709 : W := mkw 0x03140e0ab60abc56 0x806281c156c1578a 0xf71c0f3ffe07fe7f 0x7ee381e7ffc0ffcf

def z710 : W := mkw 0x025f611440000000 0x004bec2288000000 0xa03ff73ce0000003 0xd407fee79c000000

def z711 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xa73ff73fe0000003 0xd4e7fee7fc000000

def z712 : W := mkw 0x204b615540000000 0x04096c2aa8000000 0xa027f73ce0000003 0xd404fee79c000000

def z713 : W := mkw 0x08009208311c7444 0x2100124106238e88 0x08000000113ce004 0x0100000002279c00

def z714 : W := mkw 0x08009208315d76ec 0x61001241062baedd 0x08000000113ff67c 0x010000000227fecf

def z715 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x0027f638f038e000 0x4004fec71e071c00

def z716 : W := mkw 0x125ed0000557c000 0x024bda0000aaf800 0x9f3ff0001f3fe005 0xf3e7fe0003e7fc00

def z717 : W := mkw 0x180092083ffffe76 0xa300124107ffffce 0x180000001ffffe7c 0x0300000003ffffcf

def z718 : W := mkw 0x1efed2083dfff664 0x23dfda4107bffecc 0x1fd800001ffff664 0x23fb000003fffecc

def z719 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x88000004113cf667 0x1100000082279ecc

def z720 : W := mkw 0x05a00eaabaa83d57 0x80b401d5575507aa 0xffe00ff8fff81f86 0xfffc01ff1fff03f0

def z721 : W := mkw 0x05a00ea83aa83d47 0x00b401d5075507a8 0xffe00ff81ffcffe6 0xfffc01ff03ff9ffc

def z722 : W := mkw 0x0801b31c731c7e66 0x210036638e638fcc 0xb827f73cff3cfe67 0xd704fee79fe79fcc

def z723 : W := mkw 0x16fe50000cb2c000 0x02dfca0001965800 0x07e7f0001e38e000 0xc0fcfe0003c71c00

def z724 : W := mkw 0x0001211440000220 0x0000242288000044 0xa027f73ce0001663 0xd404fee79c0002cc

def z725 : W := mkw 0x27b4ecb2c14502a8 0x44f69d965828a055 0x1f247638e1c71ffc 0x43e48ec71c38e3ff

def z726 : W := mkw 0x15eade02bbf57856 0x82bd5bc0577eaf0a 0x48e3fe07e1f8187a 0x891c7fc0fc3f030f

def z727 : W := mkw 0x05eb8fed1bed1faf 0x40bd71fda37da3f5 0x073b863f1e3f0079 0x40e770c7e3c7e00f

def z728 : W := mkw 0x03140e0ab60abc56 0x806281c156c1578a 0xdf1c0e07ff3ffe7f 0x7be381c0ffe7ffcf

def z729 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xf7ffffffe0001807 0xfefffffffc000300

def z730 : W := mkw 0x27ff6df7c4028000 0x04ffedbef8805000 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z731 : W := mkw 0x07ff6d16c0000000 0x00ffeda2d8000000 0xe7ffff3fe0000003 0xfcffffe7fc000000

def z732 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8fb8fff01c71fff 0xff1f71ffe038e3ff

def z733 : W := mkw 0x27ff6df7c2000812 0x84ffedbef8400102 0xe7ffffffe000081b 0xfcfffffffc000103

def z734 : W := mkw 0x06ff615540000000 0x00dfec2aa8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z735 : W := mkw 0x0801b35d715d76ec 0x6100366bae2baedd 0xf827fffff1ffffff 0xdf04fffffe3fffff

def z736 : W := mkw 0x03152d16c0000000 0x0062a5a2d8000000 0xa727f73ce0000003 0xd4e4fee79c000000

def z737 : W := mkw 0x16b551450cb2c2a8 0x42d6aa28a1965855 0x672479c71e38fffa 0x4ce48f38e3c71fff

def z738 : W := mkw 0x24eb61f540000000 0x049d6c3ea8000000 0x20e3f7fce0000002 0x841c7eff9c000000

def z739 : W := mkw 0x004b215540000000 0x0009642aa8000000 0xa0e7f7fce0000003 0xd41cfeff9c000000

def z740 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xfffff9c01fffe007 0xffffff3803fffc00

def z741 : W := mkw 0x135edea8175fdd07 0x026bdbd502ebfba0 0x601ffff80007ff83 0x0c03ffff0000fff0

def z742 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8fff9c701c71fff 0xff1fff38e038e3ff

def z743 : W := mkw 0x05a00ea83aa83d47 0x00b401d5075507a8 0xfffc0fffffffffff 0xffff81ffffffffff

def z744 : W := mkw 0x05a00eaa9aa81d07 0x00b401d5535503a0 0xffe00ffffff81f86 0xfffc01ffffff03f0

def z745 : W := mkw 0x0801b31c731c7e76 0xa10036638e638fce 0xa827f73cf13cfe7f 0xd504fee79e279fcf

def z746 : W := mkw 0x14a090000df7c000 0x0294120001bef800 0x9fe7f0001fffe005 0xf3fcfe0003fffc00

def z747 : W := mkw 0x004b9145015542a8 0x40097228a02aa855 0xf8dff9c701c7ffff 0xbf1bff38e038ffff

def z748 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa8e7f7fcf1fcf7e7 0xd51cfeff9e3f9efc

def z749 : W := mkw 0x0801b35d711c7664 0x2100366bae238ecc 0xe827fffff13cf667 0xdd04fffffe279ecc

def z750 : W := mkw 0x25eb6df7c0000000 0x04bd6dbef8000000 0xe0e7ffffe0000003 0xdc1cfffffc000000

def z751 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x971c0607fe07e07d 0x72e380c0ffc0fc0f

def z752 : W := mkw 0x0800b218711c7444 0x210016430e238e88 0xa827f738f13cf607 0xd504fee71e279ec0

def z753 : W := mkw 0x27ff6df7c0410000 0x04ffedbef8082000 0xf7ffffffe0c30003 0xfefffffffc186000

def z754 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z755 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xb83ff73cf13ff667 0xf707fee79e27fecc

def z756 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x0727f0001e38e000 0x40e4fe0003c71c00

def z757 : W := mkw 0x0001211440000000 0x0000242288000000 0xf8e7fffce1c01f87 0xff1cffff9c3803f0

def z758 : W := mkw 0x0001311440104000 0x0000262288020800 0xa027f73cf038e003 0xd404fee79e071c00

def z759 : W := mkw 0x235f6df7c0000000 0x046bedbef8000000 0xe71fffffe0000003 0x7ce3fffffc000000

def z760 : W := mkw 0x24eb63f57602b856 0x849d6c7eaec0570a 0x30e3f1f81e07f87c 0x861c7e3f03c0ff0f

def z761 : W := mkw 0x3101bdf7cdf7c000 0x062037bef9bef800 0x78000fffffffe006 0x0f0001fffffffc00

def z762 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xdffff8071fffe007 0xfbffff00e3fffc00

def z763 : W := mkw 0x04a002a818a81505 0x00940055031502a0 0xbfe007f81ff81786 0xf7fc00ff03ff02f0

def z764 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2827f73cf138f662 0xc504fee79e271ecc

def z765 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0xf8c009c011fcffe6 0xbf180138023f9ffc

def z766 : W := mkw 0x27ff6df7c8a00000 0x04ffedbef9140000 0xe7fffffffe380003 0xfcffffffffc70000

def z767 : W := mkw 0x03140eaab60abd57 0x806281d556c157aa 0xd71c0e3ffe07f87f 0x7ae381c7ffc0ff0f

def z768 : W := mkw 0x05a00ea83aa83d57 0x80b401d5075507aa 0xffe00ff81ff81ffe 0xfffc01ff03ff03ff

def z769 : W := mkw 0x27ff6df7c6028812 0x84ffedbef8c05102 0xe7ffffffee000003 0xfcfffffffdc00000

def z770 : W := mkw 0x08009208315d7664 0x21001241062baecc 0x1800000011fff664 0x03000000023ffecc

def z771 : W := mkw 0x23152df7c0000000 0x0462a5bef8000000 0xe73fffffe0000003 0xfce7fffffc000000

def z772 : W := mkw 0x27b46cb2c0000000 0x04f68d9658000000 0x8727f638e0000001 0xd0e4fec71c000000

def z773 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xdf1c0e07ffc7ffff 0x7be381c0fff8ffff

def z774 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xd73ffe07fe07f87f 0xfae7ffc0ffc0ff0f

def z775 : W := mkw 0x004ba155414502a8 0x4009742aa828a055 0xf8db8fffe1c71fff 0xbf1b71fffc38e3ff

def z776 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x1800000011fcffe4 0x03000000023f9ffc

def z777 : W := mkw 0x0801930c311c7664 0x2100326186238ecc 0x28000104113cf666 0x0500002082279ecc

def z778 : W := mkw 0x235f6d57c0000000 0x046bedaaf8000000 0xe73fff3fe0000003 0xfce7ffe7fc000000

def z779 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9ffff604ffffe007 0xf3fffec09ffffc00

def z780 : W := mkw 0x084a3259705974cc 0x6109464b2e0b2e99 0x50fc7efbf0fbe998 0x6a1f8fdf7e1f7d33

def z781 : W := mkw 0x27ff6df7cea28913 0x84ffedbef9d45122 0xf7ffffffeec3099b 0xfefffffffdd86133

def z782 : W := mkw 0x05a00ca80aa80d03 0x00b40195015501a0 0x2fe001f80ff80780 0x85fc003f01ff00f0

def z783 : W := mkw 0x27ff6df7c0410088 0x44ffedbef8082011 0xe7ffffffe0c00183 0xfcfffffffc180030

def z784 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xc71c0e07fe07e07b 0x78e381c0ffc0fc0f

def z785 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9ffff0001fffff85 0xf3fffe0003fffff0

def z786 : W := mkw 0x08009208331c7e66 0x2100124106638fcc 0x180000001f3cfe64 0x0300000003e79fcc

def z787 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x68db89c701c71ffb 0x8d1b7138e038e3ff

def z788 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x58db88c701c71ffd 0x2b1b7118e038e3ff

def z789 : W := mkw 0x16b4d0000db6c000 0x02d69a0001b6d800 0x0727f0001e3ce001 0x40e4fe0003c79c00

def z790 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe00fff1ff81ffe 0xfffc01ffe3ff03ff

def z791 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xe827ff3ff13cfe7f 0xdd04ffe7fe279fcf

def z792 : W := mkw 0x0801b35d711c76ec 0x6100366bae238edd 0xf83ffffff13fffff 0xff07fffffe27ffff

def z793 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x6fe00ff81ff81f82 0xcdfc01ff03ff03f0

def z794 : W := mkw 0x035f2d57c0000000 0x006be5aaf8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z795 : W := mkw 0x14ead00009f54000 0x029d5a00013ea800 0x9fe7f0001ffce005 0xf3fcfe0003ff9c00

def z796 : W := mkw 0x27b56db6c0000000 0x04f6adb6d8000000 0x0727f63ce0000001 0x40e4fec79c000000

def z797 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe40ff81ffcff87 0xfffc81ff03ff9ff0

def z798 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x67fbffffe0000002 0xacff7ffffc000000

def z799 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xfff80ffb1ffb1f9e 0xffff01ff63ff63f3

def z800 : W := mkw 0x225f635fdaa81d07 0x044bec6bfb5503a0 0x181ff007fff81f85 0x0303fe00ffff03f0

def z801 : W := mkw 0x16b450000cb2c000 0x02d68a0001965800 0x8727f0001e38e001 0xd0e4fe0003c71c00

def z802 : W := mkw 0x27ff6df7c8a00000 0x04ffedbef9140000 0xfffffffffff81f87 0xffffffffffff03f0

def z803 : W := mkw 0x0801934d311c76ec 0x61003269a6238edd 0x680009c7113cfffe 0x0d000138e2279fff

def z804 : W := mkw 0x0801b11c611c6660 0x210036238c238ccc 0xa827f73ce13ce663 0xd504fee79c279ccc

def z805 : W := mkw 0x06fed0000516c000 0x00dfda0000a2d800 0x9ffff0001f3fe005 0xf3fffe0003e7fc00

def z806 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xf73c0f3ffe07f87f 0xfee781e7ffc0ff0f

def z807 : W := mkw 0x0001231c70083444 0x000024638e010688 0xa827f73cf13cf667 0xd504fee79e279ecc

def z808 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0xa8000100113cf666 0x9500002002279ecc

def z809 : W := mkw 0x09012f1c72083e66 0x212025e38e4107cc 0x60000f3ce0001e62 0x0c0001e79c0003cc

def z810 : W := mkw 0x08009208331c7e76 0xa100124106638fce 0x08000000113cfe7c 0x0100000002279fcf

def z811 : W := mkw 0x004ba155414502a8 0x4009742aa828a055 0xf8fbf9ff01c71fff 0xbf1f7f3fe038e3ff

def z812 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xffffffffe1c00007 0xfffffffffc380000

def z813 : W := mkw 0x0001215540000000 0x0000242aa8000000 0xe027ffffe0000003 0xdc04fffffc000000

def z814 : W := mkw 0x0da1bdb46bb46b63 0x21b437b68d768d6c 0x57c7f8c4eec4e9e1 0x2af8ff189dd89d3c

def z815 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0xd8180807113ffe7f 0x3b030100e227ffcf

def z816 : W := mkw 0x0800b218711c7444 0x210016430e238e88 0x8827f63cf13cf067 0xd104fec79e279e0c

def z817 : W := mkw 0x06b400aaacaaa551 0x80d68015559554aa 0x28fc01ffe1ffe7f9 0x851f803ffc3ffcff

def z818 : W := mkw 0x37ff6df7cca28000 0x06ffedbef9945000 0xe7ffffffee000003 0xfcfffffffdc00000

def z819 : W := mkw 0x21012ffff2083d57 0x842025fffe4107aa 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z820 : W := mkw 0x004b0145004102a8 0x40096028a0082055 0xf0db89c700c31ffb 0xbe1b7138e01863ff

def z821 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xdf3c0e07ff3ff87f 0xfbe781c0ffe7ff0f

def z822 : W := mkw 0x2ffedeebb11c7664 0x25ffdbdd76238ecc 0x4fd808c3113cf664 0x29fb011862279ecc

def z823 : W := mkw 0x004b211440000000 0x0009642288000000 0xa0fff73ce0000003 0xf41ffee79c000000

def z824 : W := mkw 0x05eb2df540000000 0x00bd65bea8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z825 : W := mkw 0x125ed0000df7c000 0x024bda0001bef800 0x9f1ff0001fffe005 0x73e3fe0003fffc00

def z826 : W := mkw 0x37ff6df7c4438000 0x06ffedbef8887000 0xe7ffffffe0030003 0xfcfffffffc006000

def z827 : W := mkw 0x004a8041014502a8 0x400950082028a055 0xf8d809c301c71ffe 0xbf1b01386038e3ff

def z828 : W := mkw 0x04a0900009b44000 0x0094120001368800 0x8f27f0001f3ce005 0xd1e4fe0003e79c00

def z829 : W := mkw 0x27ff6df7c4028000 0x04ffedbef8805000 0xe7fffffffe00e003 0xfcffffffffc01c00

def z830 : W := mkw 0x09012fbc72083f67 0x212025f78e4107ec 0x2000073ce0001662 0x040000e79c0002cc

def z831 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7ffffffe007007b 0xfcfffffffc00e00f

def z832 : W := mkw 0x08009208311c76ec 0x6100124106238edd 0x08000000113cfffc 0x0100000002279fff

def z833 : W := mkw 0x16fed0000df7c2a8 0x42dfda0001bef855 0xdffff8071fffffff 0xfbffff00e3ffffff

def z834 : W := mkw 0x035f8f47b747bafe 0xc06bf1e8f6e8f75f 0x2fc787c0ffc0e780 0xc5f8f0f81ff81cf0

def z835 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x7fe00ff81ff80f80 0xeffc01ff03ff01f0

def z836 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x7fe009f81ff81f84 0xaffc013f03ff03f0

def z837 : W := mkw 0x0001b31471147044 0x000036628e228e08 0xa827f73cf13cf067 0xd504fee79e279e0c

def z838 : W := mkw 0x180092083fffff67 0x2300124107ffffec 0x180000001fffffe4 0x0300000003fffffc

def z839 : W := mkw 0x27ff6df7c2000802 0x04ffedbef8400100 0xf7ffffffee000803 0xfefffffffdc00100

def z840 : W := mkw 0x37ff6df7cee38812 0x86ffedbef9dc7102 0xf7ffffffeec3081b 0xfefffffffdd86103

def z841 : W := mkw 0x04eb611440000000 0x009d6c2288000000 0xa0e7f73ce0000003 0xd41cfee79c000000

def z842 : W := mkw 0x0001211440000000 0x0000242288000000 0xa827f73cf1380007 0xd504fee79e270000

def z843 : W := mkw 0x27ff6df7cca28000 0x04ffedbef9945000 0xffffffffffffe007 0xfffffffffffffc00

def z844 : W := mkw 0x03152d16c6028812 0x8062a5a2d8c05102 0xf73fff3fee03081b 0xfee7ffe7fdc06103

def z845 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8df89c711c7ffff 0xff1bf138e238ffff

def z846 : W := mkw 0x03140e0ab60abc56 0x806281c156c1578a 0xfffc0fffffffffff 0xffff81ffffffffff

def z847 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xbf27f73cff3cf667 0xf7e4fee79fe79ecc

def z848 : W := mkw 0x0800920839bc7664 0x2100124107378ecc 0x180000001ffcf664 0x0300000003ff9ecc

def z849 : W := mkw 0x27b56db6c0000000 0x04f6adb6d8000000 0x2727f738e0000000 0xc4e4fee71c000000

def z850 : W := mkw 0x27fe6cb2c0000000 0x04ffcd9658000000 0x073ff638e0000001 0x40e7fec71c000000

def z851 : W := mkw 0x27fe6cf3c0000000 0x04ffcd9e78000000 0xc7fffefbe0000001 0xf8ffffdf7c000000

def z852 : W := mkw 0x01012d1440000000 0x002025a288000000 0xe727ff3ce0000003 0xfce4ffe79c000000

def z853 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xf7ffffffe0070007 0xfefffffffc00e000

def z854 : W := mkw 0x235f6df7c0000000 0x046bedbef8000000 0xe0dfffffe0000003 0xbc1bfffffc000000

def z855 : W := mkw 0x25eb6df7c0000000 0x04bd6dbef8000000 0xe7e3ffffe0000002 0xfcfc7ffffc000000

def z856 : W := mkw 0x07fe4ca280000000 0x00ffc99450000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z857 : W := mkw 0x09012ffd72083fef 0x612025ffae4107fd 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z858 : W := mkw 0x27ff6db6c0000000 0x04ffedb6d8000000 0xa7fff73ce0000003 0xf4fffee79c000000

def z859 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1ffbf0001fffe004 0xa3ff7e0003fffc00

def z860 : W := mkw 0x0b15bd1ec71ece32 0xa162b7a3d8e3d9c6 0x7f3bf93b0f3b0e18 0xafe77f2761e761c3

def z861 : W := mkw 0x0801b11c411c4620 0x21003623882388c4 0xa827f73cf13ce607 0xd504fee79e279cc0

def z862 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xffffffffe1c71fff 0xfffffffffc38e3ff

def z863 : W := mkw 0x04a1211440000000 0x0094242288000000 0xa7e7f73ce0000003 0xf4fcfee79c000000

def z864 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xbffff1c01fffe785 0xf7fffe3803fffcf0

def z865 : W := mkw 0x03140c02a602a852 0x8062818054c0550a 0xd71c0e07ee07e87b 0x7ae381c0fdc0fd0f

def z866 : W := mkw 0x05a00ca80aa80d03 0x00b40195015501a0 0xffe009f81ff80f84 0xfffc013f03ff01f0

def z867 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa83ff73ff13ff67f 0xd507fee7fe27fecf

def z868 : W := mkw 0x25eb6df7c0000000 0x04bd6dbef8000000 0xe0fbffffe0000003 0xbc1f7ffffc000000

def z869 : W := mkw 0x07ff6db440000000 0x00ffedb688000000 0xe7fffffce0000003 0xfcffffff9c000000

def z870 : W := mkw 0x29012ffff2083f67 0x252025fffe4107ec 0x60000fffe0001fe2 0x0c0001fffc0003fc

def z871 : W := mkw 0x37fe4ce38ee38903 0x06ffc99c71dc7120 0x57d808c30ec30980 0x2afb011861d86130

def z872 : W := mkw 0x03140ea2b602b957 0x806281d456c0572a 0xd71c0ec7fe07f9ff 0x7ae381d8ffc0ff3f

def z873 : W := mkw 0x0001211440000000 0x0000242288000000 0xe03fff3fe0000003 0xfc07ffe7fc000000

def z874 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x47fffeffe0000001 0x68ffffdffc000000

def z875 : W := mkw 0x0001211440000000 0x0000242288000000 0x2023f73ce0000002 0x84047ee79c000000

def z876 : W := mkw 0x16ff61144ce38000 0x02dfec22899c7000 0xb7fff73ceec30003 0xf6fffee79dd86000

def z877 : W := mkw 0x24eb61f540000000 0x049d6c3ea8000000 0x20e7f7f8e0000000 0xc41cfeff1c000000

def z878 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0x3fe001f80ff80780 0xa7fc003f01ff00f0

def z879 : W := mkw 0x0da09ea83bbc7f67 0x21b413d507778fec 0x5fc008c01ffcffe4 0x2bf8011803ff9ffc

def z880 : W := mkw 0x0001810401040220 0x0000302080208044 0xf8db89c701c71fff 0xbf1b7138e038e3ff

def z881 : W := mkw 0x121490000df7c000 0x0242920001bef800 0x9f3ff0001fffe005 0xf3e7fe0003fffc00

def z882 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2827f73ce13cf663 0x8504fee79c279ecc

def z883 : W := mkw 0x36fed0e10df7c000 0x06dfda1c21bef800 0x9ffff0c01fffe005 0xf3fffe1803fffc00

def z884 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x7fc00ff81ff81f86 0x2ff801ff03ff03f0

def z885 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xe827fffcf13cffe7 0xdd04ffff9e279ffc

def z886 : W := mkw 0x0b149e0ab71efe76 0xa16293c156e3dfce 0x5f1808031f3ffe7c 0x2be3010063e7ffcf

def z887 : W := mkw 0x004b0145004102a8 0x40096028a0082055 0xf0d809c700c71fff 0x3e1b0138e018e3ff

def z888 : W := mkw 0x0001211440000000 0x0000242288000000 0x0027f63ce0000001 0x4004fec79c000000

def z889 : W := mkw 0x03140e0ab60abc56 0x806281c156c1578a 0xd73c0e3ffe3ff87f 0x7ae781c7ffc7ff0f

def z890 : W := mkw 0x05a00eaa9aa81d17 0x80b401d5535503a2 0xffe00ffb1ff81f9e 0xfffc01ff63ff03f3

def z891 : W := mkw 0x06b490000db6c000 0x00d6920001b6d800 0x9ffff0001fffe005 0xf3fffe0003fffc00

def z892 : W := mkw 0x02140202b402b054 0x804280405680560a 0x971c0607fe07f07f 0x72e380c0ffc0fe0f

def z893 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x78d809c701c71ffe 0x2f1b0138e038e3ff

def z894 : W := mkw 0x02152116c0000000 0x0042a422d8000000 0xa03ff73fe0000003 0xd407fee7fc000000

def z895 : W := mkw 0x27ff6df7c04102a8 0x44ffedbef8082055 0xf7ffffffe0c31ffb 0xfefffffffc1863ff

def z896 : W := mkw 0x27ff6df7c8a00101 0x04ffedbef9140020 0xe7ffffffe0c00183 0xfcfffffffc180030

def z897 : W := mkw 0x03140c02a602a852 0x8062818054c0550a 0xd71c0807fe07e87d 0x7ae38100ffc0fd0f

def z898 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x57180e07fe07f87e 0x2ae301c0ffc0ff0f

def z899 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9ffff0071fffe07d 0xf3fffe00e3fffc0f

def z900 : W := mkw 0x0001211440000000 0x0000242288000000 0xa027f73cf004e007 0xd404fee79e009c00

def z901 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x0800000001381660 0x01000000002702cc

def z902 : W := mkw 0x16b4d0000db6c000 0x02d69a0001b6d800 0x0f27f0001f38e000 0xc1e4fe0003e71c00

def z903 : W := mkw 0x16fed0410df7c2a8 0x42dfda0821bef855 0xdffff8c31ffffffd 0xfbffff1863ffffff

def z904 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x88040000113cf665 0x5100800002279ecc

def z905 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe7fff81ff81f87 0xfffcffff03ff03f0

def z906 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xb827f73cf13ffe7f 0xd704fee79e27ffcf

def z907 : W := mkw 0x27ff6df7c00002a8 0x44ffedbef8000055 0xe7ffffffe0000783 0xfcfffffffc0000f0

def z908 : W := mkw 0x0800321870187444 0x210006430e030e88 0x8027f638f038e001 0xd004fec71e071c00

def z909 : W := mkw 0x08009208375ffefe 0xe100124106ebffdf 0x180000001ffffffc 0x0300000003ffffff

def z910 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xefffffffe1001607 0xfdfffffffc2002c0

def z911 : W := mkw 0x16fed0000df7c088 0x42dfda0001bef811 0x9ffff0001fffe99d 0xf3fffe0003fffd33

def z912 : W := mkw 0x27ff6df7c0410088 0x44ffedbef8082011 0xe7ffffffe003001b 0xfcfffffffc006003

def z913 : W := mkw 0x100092083ffffd57 0x8200124107ffffaa 0x180000001ffffffc 0x0300000003ffffff

def z914 : W := mkw 0x0001211440000000 0x0000242288000000 0x2007f73ce0000003 0x0400fee79c000000

def z915 : W := mkw 0x27fe6cb2c0000000 0x04ffcd9658000000 0x07e7f638e0000000 0xc0fcfec71c000000

def z916 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x18000000113ffe7c 0x030000000227ffcf

def z917 : W := mkw 0x0001211440000000 0x0000242288000000 0xf03fff3fe007187f 0xfe07ffe7fc00e30f

def z918 : W := mkw 0x004b215540410088 0x4009642aa8082011 0xf0ffffffe0c3099b 0xfe1ffffffc186133

def z919 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x871c0607fe07f07f 0x50e380c0ffc0fe0f

def z920 : W := mkw 0x01012d16c0000000 0x002025a2d8000000 0xe027ff3fe0000003 0xdc04ffe7fc000000

def z921 : W := mkw 0x16fe50000cb2c000 0x02dfca0001965800 0x97fff0001e3fe005 0xf2fffe0003c7fc00

def z922 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xb8e7f73cf1fcf667 0xf71cfee79e3f9ecc

def z923 : W := mkw 0x16fe50000cf3c000 0x02dfca00019e7800 0x97fff0001efbe001 0xf2fffe0003df7c00

def z924 : W := mkw 0x04a121b440000000 0x0094243688000000 0xa0e7f7fce0000003 0xd41cfeff9c000000

def z925 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x571c0807fe07f87d 0x2ae38100ffc0ff0f

def z926 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xf7fffffffe000007 0xfeffffffffc00000

def z927 : W := mkw 0x0801b31c715d76ec 0x610036638e2baedd 0xa827f73cf1fcf7e7 0xd504fee79e3f9efc

def z928 : W := mkw 0x03140c0284028000 0x0062818050805000 0xd71c0e07fe07f87f 0x7ae381c0ffc0ff0f

def z929 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9ffff0001ffff87d 0xf3fffe0003ffff0f

def z930 : W := mkw 0x09012f1ef2083e76 0xa12025e3de4107ce 0x2000073ce0001662 0x040000e79c0002cc

def z931 : W := mkw 0x06b5611440000000 0x00d6ac2288000000 0xa727f73ce0000003 0xd4e4fee79c000000

def z932 : W := mkw 0x27ff6df7c6028812 0x84ffedbef8c05102 0xf7fffffffe07e81f 0xfeffffffffc0fd03

def z933 : W := mkw 0x27ff6df7c0410088 0x44ffedbef8082011 0xffffffffe1c31f9f 0xfffffffffc3863f3

def z934 : W := mkw 0x1eff631c7cebb664 0x23dfec638f9d76cc 0x37d8073ceec31662 0x26fb00e79dd862cc

def z935 : W := mkw 0x084a9249315d76ec 0x61095249262baedd 0x58d808c311fffffc 0x2b1b0118623fffff

def z936 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa027f73cf03ce063 0xd404fee79e079c0c

def z937 : W := mkw 0x14ead0000df7c000 0x029d5a0001bef800 0x9fe3f0001fffe004 0xf3fc7e0003fffc00

def z938 : W := mkw 0x06fed00009b44000 0x00dfda0001368800 0x9ffff0001ffce005 0xf3fffe0003ff9c00

def z939 : W := mkw 0x36fed0438df7c000 0x06dfda0871bef800 0x9ffff0031fffe005 0xf3fffe0063fffc00

def z940 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x8027f63cf03cf067 0x5004fec79e079e0c

def z941 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x571c0e07fe07e879 0x6ae381c0ffc0fd0f

def z942 : W := mkw 0x37ff6df7c8e10000 0x06ffedbef91c2000 0xe7ffffffe0c00003 0xfcfffffffc180000

def z943 : W := mkw 0x0801331c70187444 0x210026638e030e88 0x2027f738f038e000 0xc404fee71e071c00

def z944 : W := mkw 0x004a8041014502a8 0x400950082028a055 0xd8db88c301c71ffd 0xbb1b71186038e3ff

def z945 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x8ffff0001ff8e001 0xf1fffe0003ff1c00

def z946 : W := mkw 0x16fed0000db6c000 0x02dfda0001b6d800 0x8ffff0001f3ce005 0xf1fffe0003e79c00

def z947 : W := mkw 0x235f6df7c0000000 0x046bedbef8000000 0xe03fffffe0000003 0xdc07fffffc000000

def z948 : W := mkw 0x225f6157c0000000 0x044bec2af8000000 0x003ff63fe0000001 0x4007fec7fc000000

def z949 : W := mkw 0x0801331c70187664 0x210026638e030ecc 0xa027f73cf038f663 0xd404fee79e071ecc

def z950 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x0727f638e0000000 0x40e4fec71c000000

def z951 : W := mkw 0x0001b31c511c5404 0x000036638a238a80 0xa827f73cf13cf607 0xd504fee79e279ec0

def z952 : W := mkw 0x0800b218711c7444 0x210016430e238e88 0x0027f638f03ce001 0x4004fec71e079c00

def z953 : W := mkw 0x0000b01041144000 0x0000160208228800 0x8827f638f13ce005 0xd104fec71e279c00

def z954 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xeffffffff1380007 0xfdfffffffe270000

def z955 : W := mkw 0x0801b35d711c76ec 0x6100366bae238edd 0xf8e7fffff1fcffff 0xff1cfffffe3f9fff

def z956 : W := mkw 0x004a8041014502a8 0x400950082028a055 0xd8d808c701c71fff 0x3b1b0118e038e3ff

def z957 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x973ff0001e3fe005 0x72e7fe0003c7fc00

def z958 : W := mkw 0x16fed0410df7c088 0x42dfda0821bef811 0x9ffff0031fffe01d 0xf3fffe0063fffc03

def z959 : W := mkw 0x34ebf1f549f542a8 0x469d7e3ea93ea855 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z960 : W := mkw 0x09012f5ff2083efe 0xe12025ebfe4107df 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z961 : W := mkw 0x05a00ea83aa83d47 0x00b401d5075507a8 0xffe40ff8fff8ff86 0xfffc81ff1fff1ff0

def z962 : W := mkw 0x0800920839bc7765 0x2100124107378eec 0x0800000011fcf7e4 0x01000000023f9efc

def z963 : W := mkw 0x025e90000557c000 0x004bd20000aaf800 0x9ffff0001fffe005 0xf3fffe0003fffc00

def z964 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe00ffc1ffc1fe7 0xfffc01ff83ff83fc

def z965 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa827f73cf138e603 0xd504fee79e271cc0

def z966 : W := mkw 0x0000201040000000 0x0000040208000000 0x8027f638e0000001 0xd004fec71c000000

def z967 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xf7ffffffe0c00983 0xfefffffffc180130

def z968 : W := mkw 0x214b6df7c0000000 0x04296dbef8000000 0x6003ffffe0000002 0x0c007ffffc000000

def z969 : W := mkw 0x16fed0000df7c2a8 0x42dfda0001bef855 0x9ffff0001fffe785 0xf3fffe0003fffcf0

def z970 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x87fff0001e3fe001 0xf0fffe0003c7fc00

def z971 : W := mkw 0x17b45eaabebafd57 0x82f68bd557d75faa 0x07247638fe38e000 0x40e48ec71fc71c00

def z972 : W := mkw 0x05a00eaabaa83d57 0x80b401d5575507aa 0xffe40ffffffcffff 0xfffc81ffffff9fff

def z973 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7ffffffe0041067 0xfcfffffffc00820c

def z974 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1fdff0001fffe005 0x23fbfe0003fffc00

def z975 : W := mkw 0x37fe4ce38ca28000 0x06ffc99c71945000 0x47d808c30e000000 0x28fb011861c00000

def z976 : W := mkw 0x21012df7c0000000 0x042025bef8000000 0x6023ffffe0000002 0x8c047ffffc000000

def z977 : W := mkw 0x27ff6df7c2000903 0x04ffedbef8400120 0xe7ffffffe0000983 0xfcfffffffc000130

def z978 : W := mkw 0x004b9145015542a8 0x40097228a02aa855 0xf8db89c711ffffff 0xbf1b7138e23fffff

def z979 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xfff80ff81fff1f87 0xffff01ff03ffe3f0

def z980 : W := mkw 0x26ff6157c0000000 0x04dfec2af8000000 0xa7fff73fe0000003 0xf4fffee7fc000000

def z981 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x000000000004f660 0x0000000000009ecc

def z982 : W := mkw 0x004bb155415542a8 0x4009762aa82aa855 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z983 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x8f3ff0001f3fe005 0xd1e7fe0003e7fc00

def z984 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x87fff63fe0000001 0xf0fffec7fc000000

def z985 : W := mkw 0x0ca0920839bc7664 0x2194124107378ecc 0x9fe000001ffcf664 0xf3fc000003ff9ecc

def z986 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x3fe007f81ff81f84 0xc7fc00ff03ff03f0

def z987 : W := mkw 0x08009208315d76ec 0x61001241062baedd 0x0800000011fcf7e4 0x01000000023f9efc

def z988 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xbffff7381fffe007 0xf7fffee703fffc00

def z989 : W := mkw 0x0801b31c731c7f67 0x210036638e638fec 0xa827f73cf13cffe7 0xd504fee79e279ffc

def z990 : W := mkw 0x01000e0812081c06 0x002001c102410380 0xffe00ff81ff81f86 0xfffc01ff03ff03f0

def z991 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xbffff1001ffff607 0xf7fffe2003fffec0

def z992 : W := mkw 0x0801b35d711c76ec 0x6100366bae238edd 0xa827f73ff13cf67f 0xd504fee7fe279ecf

def z993 : W := mkw 0x084bb155415542a8 0x6109762aa82aa855 0xf8dbf9c701c71fff 0xbf1b7f38e038e3ff

def z994 : W := mkw 0x004a800001450000 0x000950000028a000 0xf8db89c701c71fff 0xbf1b7138e038e3ff

def z995 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x78db89c301c71ffc 0xaf1b71386038e3ff

def z996 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa827f738f13ce605 0xd504fee71e279cc0

def z997 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x17fff0001effe001 0x62fffe0003dffc00

def z998 : W := mkw 0x27ff6df7c6028812 0x84ffedbef8c05102 0xf7ffffffee07187f 0xfefffffffdc0e30f

def z999 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x00000000103ce060 0x0000000002079c0c

def z1000 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2027f73cf03cf663 0x4404fee79e079ecc

def z1001 : W := mkw 0x05a00ca008a00000 0x00b4019401140000 0xffe00ff81ff81f86 0xfffc01ff03ff03f0

def z1002 : W := mkw 0x16fed0410df7c088 0x42dfda0821bef811 0x9ffff0c01fffe185 0xf3fffe1803fffc30

def z1003 : W := mkw 0x16fed0000df7c220 0x02dfda0001bef844 0x9ffff0001ffff665 0xf3fffe0003fffecc

def z1004 : W := mkw 0x021490000516c000 0x0042920000a2d800 0x8f27f0001f3ce005 0xd1e4fe0003e79c00

def z1005 : W := mkw 0x05a00ea83aa83d47 0x00b401d5075507a8 0xffe00ffcfff81fe6 0xfffc01ff9fff03fc

def z1006 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xdffff8031fffe81d 0xfbffff0063fffd03

def z1007 : W := mkw 0x27ff6df7c0410088 0x44ffedbef8082011 0xf7ffffffe0c719ff 0xfefffffffc18e33f

def z1008 : W := mkw 0x0801b31c715d76ec 0x610036638e2baedd 0xf83fff3ff1ffffff 0xff07ffe7fe3fffff

def z1009 : W := mkw 0x0801331c70187444 0x210026638e030e88 0x0027f63cf038e001 0x4004fec79e071c00

def z1010 : W := mkw 0x37fe4ce38ce38088 0x46ffc99c719c7011 0x57d808c30ec30998 0x2afb011861d86133

def z1011 : W := mkw 0x07b52db6c0000000 0x00f6a5b6d8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1012 : W := mkw 0x0801b31c715d76ec 0x610036638e2baedd 0xf8e7fffcf1ffffff 0xff1cffff9e3fffff

def z1013 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x0ffff0001fffe001 0xc1fffe0003fffc00

def z1014 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xe83fff3ff13cf667 0xfd07ffe7fe279ecc

def z1015 : W := mkw 0x0001211440000000 0x0000242288000000 0xa827f73ce1001607 0xd504fee79c2002c0

def z1016 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x080000001138e600 0x0100000002271cc0

def z1017 : W := mkw 0x080092083fbeff77 0xa100124107f7dfee 0x180000001ffffffc 0x0300000003ffffff

def z1018 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x67dfffffe0000003 0x2cfbfffffc000000

def z1019 : W := mkw 0x02140002a402a050 0x804280005480540a 0xd71c0807fe07f87f 0x7ae38100ffc0ff0f

def z1020 : W := mkw 0x05a00eaabaa83d57 0x80b401d5575507aa 0xfff80fffffff1fff 0xffff01ffffffe3ff

def z1021 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x27fff7ffe0000001 0xc4fffefffc000000

def z1022 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xefe00ff81ff80782 0xfdfc01ff03ff00f0

def z1023 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xe8e7fffcf13cf667 0xfd1cffff9e279ecc

def z1024 : W := mkw 0x0fb43ebafebafd57 0xa1f687d75fd75faa 0x07247638fe38e000 0x40e48ec71fc71c00

def z1025 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe40ffcfff81f87 0xfffc81ff9fff03f0

def z1026 : W := mkw 0x27ff6df7c4028010 0x84ffedbef8805002 0xe7ffffffe003001b 0xfcfffffffc006003

def z1027 : W := mkw 0x06fe40000ca28000 0x00dfc80001945000 0x9ffff0001fffe005 0xf3fffe0003fffc00

def z1028 : W := mkw 0x080092083bfd7fef 0x61001241077faffd 0x180000001ffffffc 0x0300000003ffffff

def z1029 : W := mkw 0x00012155400002a8 0x4000242aa8000055 0xe027ffffe0001ffb 0xdc04fffffc0003ff

def z1030 : W := mkw 0x03140e0ab60abd57 0x806281c156c157aa 0xd71c0e07fe07ffff 0x7ae381c0ffc0ffff

def z1031 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xa7fff7f8e0000001 0xf4fffeff1c000000

def z1032 : W := mkw 0x16fe50000cb2c000 0x02dfca0001965800 0x9ffff0001ff8e005 0xf3fffe0003ff1c00

def z1033 : W := mkw 0x21012db6c0000000 0x042025b6d8000000 0xa027f73ce0000003 0xd404fee79c000000

def z1034 : W := mkw 0x08009208331c7f67 0x2100124106638fec 0x08000000113cffe4 0x0100000002279ffc

def z1035 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xa827f738f138f606 0xd504fee71e271ec0

def z1036 : W := mkw 0x27b56db6c0000000 0x04f6adb6d8000000 0xe7e7fffce0000003 0xfcfcffff9c000000

def z1037 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0xffe009f81ff81f86 0xfffc013f03ff03f0

def z1038 : W := mkw 0x080092083bbc7f67 0x2100124107778fec 0x080000001f3cf664 0x0100000003e79ecc

def z1039 : W := mkw 0x27b56df7c0000000 0x04f6adbef8000000 0xe727ffffe0000003 0xdce4fffffc000000

def z1040 : W := mkw 0x26ff61f540000000 0x04dfec3ea8000000 0xa7fff7fce0000003 0xf4fffeff9c000000

def z1041 : W := mkw 0x05a12db44aa00903 0x00b425b689540120 0xf7e7fffceec00983 0xfefcffff9dd80130

def z1042 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x8fe7f0001ffce005 0xd1fcfe0003ff9c00

def z1043 : W := mkw 0x27ff6df7c4028000 0x04ffedbef8805000 0xf7fffffffe07f87f 0xfeffffffffc0ff0f

def z1044 : W := mkw 0x37ff6df7cce38000 0x06ffedbef99c7000 0xfffffffffffb0007 0xffffffffffff6000

def z1045 : W := mkw 0x08009208371efe76 0xa100124106e3dfce 0x080000001f3cf664 0x0100000003e79ecc

def z1046 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xdffff8c01fffe985 0xfbffff1803fffd30

def z1047 : W := mkw 0x02140002a402a050 0x804280005480540a 0x071c0007fe07e079 0x40e38000ffc0fc0f

def z1048 : W := mkw 0x00010145000002a8 0x40002028a0000055 0xf8d809c701c71fff 0xbf1b0138e038e3ff

def z1049 : W := mkw 0x1a5ff1556557e2e8 0x634bfe2aacaafc5d 0x001ff007e007e079 0x0003fe00fc00fc0f

def z1050 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7fffffff004e007 0xfcfffffffe009c00

def z1051 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x67fffffbe0000000 0xecffffff7c000000

def z1052 : W := mkw 0x24a161b440000000 0x04942c3688000000 0xa027f73ce0000003 0xd404fee79c000000

def z1053 : W := mkw 0x004b0145004102a8 0x40096028a0082055 0xf8d809c701c31ffe 0xbf1b0138e03863ff

def z1054 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xf827ff3cf13cfe67 0xff04ffe79e279fcc

def z1055 : W := mkw 0x03140ea2b602b856 0x806281d456c0570a 0xf71c0ffffe07f87f 0x7ee381ffffc0ff0f

def z1056 : W := mkw 0x16b4d0000df7c000 0x02d69a0001bef800 0x9f27f0001fffe005 0xd3e4fe0003fffc00

def z1057 : W := mkw 0x01012db440000000 0x002025b688000000 0xe027fffce0000003 0xdc04ffff9c000000

def z1058 : W := mkw 0x03140eaab60abd57 0x806281d556c157aa 0xff3c0fffff3fffff 0xffe781ffffe7ffff

def z1059 : W := mkw 0x0001211440000000 0x0000242288000000 0xe0e7fffce0000003 0xfc1cffff9c000000

def z1060 : W := mkw 0x08009208351ef664 0x2100124106a3decc 0x180000001f3ff664 0x0300000003e7fecc

def z1061 : W := mkw 0x37ff6df7cee38903 0x06ffedbef9dc7120 0xf7ffffffeec30983 0xfefffffffdd86130

def z1062 : W := mkw 0x02140202b602b856 0x8042804056c0570a 0x971c0007fe07f87d 0x72e38000ffc0ff0f

def z1063 : W := mkw 0x16fed0a00df7c101 0x02dfda1401bef820 0x9ffff0c01fffe185 0xf3fffe1803fffc30

def z1064 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z1065 : W := mkw 0x325ff157c557c2a8 0x464bfe2af8aaf855 0x001ff007e007e079 0x0003fe00fc00fc0f

def z1066 : W := mkw 0x104bd145015542a8 0x42097a28a02aa855 0xf8dbf9c701c71fff 0xbf1b7f38e038e3ff

def z1067 : W := mkw 0x180092083dbef664 0x2300124107b7decc 0x080000001f3cf664 0x0100000003e79ecc

def z1068 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8fb89c711ff1fff 0xff1f7138e23fe3ff

def z1069 : W := mkw 0x25a12df7c0000000 0x04b425bef8000000 0xe7e7ffffe0000003 0xfcfcfffffc000000

def z1070 : W := mkw 0x27ff6df7c00002a8 0x44ffedbef8000055 0xffffffffe1c01fff 0xfffffffffc3803ff

def z1071 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xbfe007f81ff80784 0xf7fc00ff03ff00f0

def z1072 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x171c0607fe07f87d 0x42e380c0ffc0ff0f

def z1073 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xfffff9c71fffffff 0xffffff38e3ffffff

def z1074 : W := mkw 0x08009208351ef674 0xa100124106a3dece 0x08000000113ff67c 0x010000000227fecf

def z1075 : W := mkw 0x02140002a402a050 0x804280005480540a 0x171c0007ee07e079 0x22e38000fdc0fc0f

def z1076 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xf8df8fc7e1c71fff 0xff1bf1f8fc38e3ff

def z1077 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0x7fe00ff80ff81f82 0xaffc01ff01ff03f0

def z1078 : W := mkw 0x16b4d0000db6c000 0x02d69a0001b6d800 0x9f3ff0001f3fe005 0xf3e7fe0003e7fc00

def z1079 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x0827f63cf13cf665 0x4104fec79e279ecc

def z1080 : W := mkw 0x27fe6cb2c0000000 0x04ffcd9658000000 0xe7fffff8e0000003 0xfcffffff1c000000

def z1081 : W := mkw 0x0001b11441144220 0x0000362288228844 0xa827f73cf13cf667 0xd504fee79e279ecc

def z1082 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xf7ffffffe003081b 0xfefffffffc006103

def z1083 : W := mkw 0x004ba155414502a8 0x4009742aa828a055 0xf8dff9c7e1c71fff 0xbf1bff38fc38e3ff

def z1084 : W := mkw 0x27b56db6c0000000 0x04f6adb6d8000000 0xe73fff3fe0000003 0xfce7ffe7fc000000

def z1085 : W := mkw 0x03140c02a602a852 0x8062818054c0550a 0xd71c0807ee07f87f 0x3ae38100fdc0ff0f

def z1086 : W := mkw 0x16fed0410df7c000 0x02dfda0821bef800 0xdffff8c31fffe005 0xfbffff1863fffc00

def z1087 : W := mkw 0x27fe4ce38ea28913 0x84ffc99c71d45122 0x57d808c30ec30998 0x2afb011861d86133

def z1088 : W := mkw 0x225f6157c0000000 0x044bec2af8000000 0x201ff73fe0000003 0x0403fee7fc000000

def z1089 : W := mkw 0x235f6df7c0000000 0x046bedbef8000000 0x001ff63fe0000001 0x0003fec7fc000000

def z1090 : W := mkw 0x04a002a81aa81d07 0x00940055035503a0 0xbfe001f81ff81f84 0xf7fc003f03ff03f0

def z1091 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1ffff0001ffbe000 0xe3fffe0003ff7c00

def z1092 : W := mkw 0x04a0020818a81404 0x0094004103150280 0xffe00ff81ff81f86 0xfffc01ff03ff03f0

def z1093 : W := mkw 0x180092083dfff6ec 0x6300124107bffedd 0x180000001ffffffc 0x0300000003ffffff

def z1094 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xdfdc0e07ffc7f87f 0xfbfb81c0fff8ff0f

def z1095 : W := mkw 0x021402003402b044 0x0042804006805608 0xd71c0e07fe07f87f 0x7ae381c0ffc0ff0f

def z1096 : W := mkw 0x25eb6df7c0000000 0x04bd6dbef8000000 0x20e3f7f8e0000000 0x841c7eff1c000000

def z1097 : W := mkw 0x0cebb1fd49fd47a9 0x619d763fa93fa8f5 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z1098 : W := mkw 0x214b2df7c0000000 0x042965bef8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1099 : W := mkw 0x06fe601040000000 0x00dfcc0208000000 0x87fff638e0000001 0xf0fffec71c000000

def z1100 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x471c0e07fe07f87b 0x48e381c0ffc0ff0f

def z1101 : W := mkw 0x37fe4ca28ce38000 0x06ffc994519c7000 0x17d800000ec30000 0x22fb000001d86000

def z1102 : W := mkw 0x08009208311c7664 0x2100124106238ecc 0x88200000113cf664 0xd104000002279ecc

def z1103 : W := mkw 0x0801b31c711c76ec 0x610036638e238edd 0xa827f73cf13cffff 0xd504fee79e279fff

def z1104 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xfff80fff1ff81f87 0xffff01ffe3ff03f0

def z1105 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x673fffffe0000003 0x4ce7fffffc000000

def z1106 : W := mkw 0x004b9145015542a8 0x40097228a02aa855 0xf8fbf9c701ff1fff 0xbf1f7f38e03fe3ff

def z1107 : W := mkw 0x16fed0000df7c2a8 0x42dfda0001bef855 0x9ffff0001fffe07d 0xf3fffe0003fffc0f

def z1108 : W := mkw 0x27ff6df7c0000088 0x44ffedbef8000011 0xe7ffffffe000099b 0xfcfffffffc000133

def z1109 : W := mkw 0x27ff6df7c8a00000 0x04ffedbef9140000 0xf7ffffffeec00003 0xfefffffffdd80000

def z1110 : W := mkw 0x05a00ca80aa80d03 0x00b40195015501a0 0xffe009f80ff81f86 0xbffc013f01ff03f0

def z1111 : W := mkw 0x22156116c0000000 0x0442ac22d8000000 0xa027f73ce0000003 0xd404fee79c000000

def z1112 : W := mkw 0x0800b218711c7664 0x210016430e238ecc 0x8827f638f13cf665 0xd104fec71e279ecc

def z1113 : W := mkw 0x05a00ca80aa80d03 0x00b40195015501a0 0xffe00ff80ff80f82 0xfffc01ff01ff01f0

def z1114 : W := mkw 0x27ff6df7c4028000 0x04ffedbef8805000 0xf7ffffffee030003 0xfefffffffdc06000

def z1115 : W := mkw 0x03140c02a602a852 0x8062818054c0550a 0x071c0007ee07e079 0x00e38000fdc0fc0f

def z1116 : W := mkw 0x1cebf15d49fd46a8 0x639d7e2ba93fa8d5 0x28e3f1f801f80780 0x851c7e3f003f00f0

def z1117 : W := mkw 0x27ff6df7caa00903 0x04ffedbef9540120 0xe7ffffffee000003 0xfcfffffffdc00000

def z1118 : W := mkw 0x27ff6df7c00002a8 0x44ffedbef8000055 0xf7ffffffe0071fff 0xfefffffffc00e3ff

def z1119 : W := mkw 0x24eb61f540000000 0x049d6c3ea8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1120 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1f3ff0001fffe005 0x43e7fe0003fffc00

def z1121 : W := mkw 0x29012ffff2083e76 0xa52025fffe4107ce 0x60000fffe0001e7a 0x0c0001fffc0003cf

def z1122 : W := mkw 0x37fe4ce38ee38812 0x86ffc99c71dc7102 0x57d808c30ec30818 0x2afb011861d86103

def z1123 : W := mkw 0x27ff6df7c0000220 0x04ffedbef8000044 0xe7ffffffe0001663 0xfcfffffffc0002cc

def z1124 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9fe7f0001ff8e004 0xf3fcfe0003ff1c00

def z1125 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xefffffffe1c00783 0xfdfffffffc3800f0

def z1126 : W := mkw 0x00009208311c7444 0x0000124106238e88 0xa827f73cf13cf667 0xd504fee79e279ecc

def z1127 : W := mkw 0x16fed0a00df7c000 0x02dfda1401bef800 0xbffff1f81fffe005 0xf7fffe3f03fffc00

def z1128 : W := mkw 0x16fed0028df7c010 0x82dfda0051bef802 0x9ffff0031fffe01d 0xf3fffe0063fffc03

def z1129 : W := mkw 0x05a12db440000000 0x00b425b688000000 0xa727f73ce0000003 0xd4e4fee79c000000

def z1130 : W := mkw 0x37ff6df7cce38000 0x06ffedbef99c7000 0xf7fffffffec7e007 0xfeffffffffd8fc00

def z1131 : W := mkw 0x27ff6df7c8a00000 0x04ffedbef9140000 0xefffffffe1f80003 0xfdfffffffc3f0000

def z1132 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xffe00ff81fff1ffe 0xfffc01ff03ffe3ff

def z1133 : W := mkw 0x25eb6df540000000 0x04bd6dbea8000000 0xe7e7fffce0000003 0xfcfcffff9c000000

def z1134 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x70db89c700c71ffb 0x2e1b7138e018e3ff

def z1135 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xd7dc0ec7fec7f9ff 0x7afb81d8ffd8ff3f

def z1136 : W := mkw 0x0215211444028000 0x0042a42288805000 0xb73ff73cfe07e007 0xf6e7fee79fc0fc00

def z1137 : W := mkw 0x16fed0410df7c088 0x42dfda0821bef811 0xfffff9c31fffff9f 0xffffff3863fffff3

def z1138 : W := mkw 0x26ff61f7c0000000 0x04dfec3ef8000000 0xa0fff7ffe0000003 0xd41ffefffc000000

def z1139 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xff1c0f07ff07fe7f 0xffe381e0ffe0ffcf

def z1140 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0x571c0e07ee07f87b 0x2ae381c0fdc0ff0f

def z1141 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0xb827f73cf1fcffe7 0xd704fee79e3f9ffc

def z1142 : W := mkw 0x05a00ca808a80501 0x00b40195011500a0 0xffe00ff81ff80786 0xfffc01ff03ff00f0

def z1143 : W := mkw 0x0a5fb157e557e2f8 0xe14bf62afcaafc5f 0x001ff007e007e079 0x0003fe00fc00fc0f

def z1144 : W := mkw 0x27ff6df7caa00903 0x04ffedbef9540120 0xffffffffefc01f87 0xfffffffffdf803f0

def z1145 : W := mkw 0x20012157c0000000 0x0400242af8000000 0xa027f73fe0000003 0xd404fee7fc000000

def z1146 : W := mkw 0x27ff6df7cae1098b 0x44ffedbef95c2131 0xf7ffffffeec3099b 0xfefffffffdd86133

def z1147 : W := mkw 0x16b4d0000db6c000 0x02d69a0001b6d800 0x9fe7f0001ffce005 0xf3fcfe0003ff9c00

def z1148 : W := mkw 0x16fed0028df7c000 0x02dfda0051bef800 0x9ffff007ffffe005 0xf3fffe00fffffc00

def z1149 : W := mkw 0x0801331c70187444 0x210026638e030e88 0xa027f73cf03cf067 0xd404fee79e079e0c

def z1150 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xf7dc0fc7fe07f87f 0xfefb81f8ffc0ff0f

def z1151 : W := mkw 0x004a004100410088 0x4009400820082011 0xf8d809c701c71fff 0xbf1b0138e038e3ff

def z1152 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2827f738f13cf664 0xc504fee71e279ecc

def z1153 : W := mkw 0x27b46ebafeaabd57 0x84f68dd75fd557aa 0x07247638fe38e000 0x40e48ec71fc71c00

def z1154 : W := mkw 0x16fe50000cb2c000 0x02dfca0001965800 0x073ff0001e38e001 0x40e7fe0003c71c00

def z1155 : W := mkw 0x09012fbef2083f77 0xa12025f7de4107ee 0x60000fffe0001ffa 0x0c0001fffc0003ff

def z1156 : W := mkw 0x0a149208351ef664 0x2142924106a3decc 0x9f1c00001f3ff665 0x73e3800003e7fecc

def z1157 : W := mkw 0x27fe6cb2c0000000 0x04ffcd9658000000 0xc7fffe3fe0000003 0xf8ffffc7fc000000

def z1158 : W := mkw 0x01000e0032003846 0x002001c006400708 0xd71c0e07fe07f87f 0x7ae381c0ffc0ff0f

def z1159 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xa7e7f7fce0000003 0xd4fcfeff9c000000

def z1160 : W := mkw 0x27ff6df7c643889a 0xc4ffedbef8c87113 0xf7ffffffeec3099b 0xfefffffffdd86133

def z1161 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x8827f63cf13ce065 0xd104fec79e279c0c

def z1162 : W := mkw 0x05a00ea81aa81d07 0x00b401d5035503a0 0xafe007f81ff81786 0xd5fc00ff03ff02f0

def z1163 : W := mkw 0x004a0041004102a8 0x4009400820082055 0x50d808c300c31ff8 0x2a1b0118601863ff

def z1164 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0xdffff8001ffff807 0xfbffff0003ffff00

def z1165 : W := mkw 0x0801b31c711c7444 0x210036638e238e88 0xa827f73cf13ce007 0xd504fee79e279c00

def z1166 : W := mkw 0x0000900001144000 0x0000120000228800 0x9f27f0001f3ce005 0xf3e4fe0003e79c00

def z1167 : W := mkw 0x04ea900009f54000 0x009d5200013ea800 0x9ffff0001fffe005 0xf3fffe0003fffc00

def z1168 : W := mkw 0x0801b31c715d76ec 0x610036638e2baedd 0xa827f73cf13ff67f 0xd504fee79e27fecf

def z1169 : W := mkw 0x0215211440000000 0x0042a42288000000 0xa73ff73ce0000003 0xf4e7fee79c000000

def z1170 : W := mkw 0x04a1211448a00000 0x0094242289140000 0xbfe7f73cfff80007 0xf7fcfee79fff0000

def z1171 : W := mkw 0x16fed0000df7c2a8 0x42dfda0001bef855 0xfffff9c01fffffff 0xffffff3803ffffff

def z1172 : W := mkw 0x27ff6df7c00002a8 0x44ffedbef8000055 0xe7ffffffe000007b 0xfcfffffffc00000f

def z1173 : W := mkw 0x004b215540000000 0x0009642aa8000000 0xa03ff73fe0000003 0xd407fee7fc000000

def z1174 : W := mkw 0x0801331c70187444 0x210026638e030e88 0xa827f73cf138f607 0xd504fee79e271ec0

def z1175 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x67e7ffffe0000002 0xccfcfffffc000000

def z1176 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0x78db89c701c31ffa 0xaf1b7138e03863ff

def z1177 : W := mkw 0x0001211440000000 0x0000242288000000 0xa027f73ce0041067 0xd404fee79c00820c

def z1178 : W := mkw 0x03140e02b602b856 0x806281c056c0570a 0xf71c0fc7fe07ffff 0x7ee381f8ffc0ffff

def z1179 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x9ffff0041ffff067 0xf3fffe0083fffe0c

def z1180 : W := mkw 0x004b014500000000 0x00096028a0000000 0xf8db89c701c71fff 0xbf1b7138e038e3ff

def z1181 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7e7fff8e0000002 0xfcfcffff1c000000

def z1182 : W := mkw 0x225f6157c0000000 0x044bec2af8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1183 : W := mkw 0x17fe4ca28ee38913 0x82ffc99451dc7122 0x57d808c30ec30998 0x2afb011861d86133

def z1184 : W := mkw 0x21012df7c0000000 0x042025bef8000000 0x6007ffffe0000003 0x0c00fffffc000000

def z1185 : W := mkw 0x180092083dfff444 0x2300124107bffe88 0x180000001fffe004 0x0300000003fffc00

def z1186 : W := mkw 0x004b8145014502a8 0x40097028a028a055 0xffdb89c71fc71fff 0xfffb7138e3f8e3ff

def z1187 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z1188 : W := mkw 0x16fed0000df7c000 0x02dfda0001bef800 0x1fe7f0001fffe004 0xc3fcfe0003fffc00

def z1189 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xc73ffe3fe0000003 0x78e7ffc7fc000000

def z1190 : W := mkw 0x04a000a808a80501 0x00940015011500a0 0x2fe001f81ff80780 0xc5fc003f03ff00f0

def z1191 : W := mkw 0x27ff6df7caa00903 0x04ffedbef9540120 0xfffffffffff80987 0xffffffffffff0130

def z1192 : W := mkw 0x204be155414502a8 0x44097c2aa828a055 0xf8dbf9c701c71fff 0xbf1b7f38e038e3ff

def z1193 : W := mkw 0x37ff6df7cce38088 0x46ffedbef99c7011 0xf7ffffffeec3099b 0xfefffffffdd86133

def z1194 : W := mkw 0x00008000014502a8 0x400010000028a055 0xf8d809c701c71fff 0xbf1b0138e038e3ff

def z1195 : W := mkw 0x1800920839fd7664 0x23001241073faecc 0x0800000011fcf664 0x01000000023f9ecc

def z1196 : W := mkw 0x03140c02a402a050 0x806281805480540a 0xd71c0e07fe07e07f 0x7ae381c0ffc0fc0f

def z1197 : W := mkw 0x0801b35d711c76ec 0x6100366bae238edd 0xa827f7fcf13cf7e7 0xd504feff9e279efc

def z1198 : W := mkw 0x18009208355ff664 0x2300124106abfecc 0x08000000113ff664 0x010000000227fecc

def z1199 : W := mkw 0x27ff6df7c0000000 0x04ffedbef8000000 0xe7ffffffe000187b 0xfcfffffffc00030f

def z1200 : W := mkw 0x0801b31c715d7664 0x210036638e2baecc 0xb827f73cf1fff667 0xd704fee79e3ffecc

def z1201 : W := mkw 0x0801b11461146260 0x210036228c228c4c 0xa827f73cf13ce067 0xd504fee79e279c0c

def z1202 : W := mkw 0x0801b31c711c7664 0x210036638e238ecc 0x2827f73cf13ce661 0xc504fee79e279ccc

def z1203 : W := mkw 0x16fed0410df7c088 0x42dfda0821bef811 0xdffff8c71ffff9ff 0xfbffff18e3ffff3f

def z1204 : W := mkw 0x200121f540000000 0x0400243ea8000000 0xa027f7fce0000003 0xd404feff9c000000

def z1205 : W := mkw 0x0800b218711c7444 0x210016430e238e88 0x0827f638f138e000 0xc104fec71e271c00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z8,z5,z6]),(0,[z1,z7,z3,z4,z9,z5,z6])],[(1,[z10,z1,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z12,z5,z6]),(0,[z1,z13,z7,z3,z4,z14,z6])],[(0,[z1,z15,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z16]),(1,[z1,z17,z18,z4,z5,z6])],[(0,[z1,z7,z3,z19,z4,z5,z6]),(0,[z1,z3,z20,z4,z21,z5,z6]),(1,[z1,z7,z22,z3,z4,z5]),(0,[z1,z23,z7,z3,z4,z5,z6])],[(0,[z1,z7,z24,z20,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z25,z6]),(0,[z26,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z27,z5,z6]),(0,[z28,z1,z7,z3,z4,z5,z6]),(0,[z29,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z30,z6]),(0,[z1,z31,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z5,z6,z32]),(0,[z1,z33,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z34,z35,z5,z6]),(0,[z1,z7,z3,z4,z36,z5,z37]),(0,[z1,z38,z3,z39,z4,z5,z6]),(1,[z1,z40,z3,z4,z21,z6]),(0,[z41,z1,z7,z3,z4,z5,z6]),(0,[z1,z42,z7,z3,z4,z5,z6]),(0,[z43,z1,z7,z44,z4,z5,z6]),(0,[z1,z7,z44,z3,z4,z5,z45])],[(0,[z1,z7,z3,z4,z5,z46,z6]),(0,[z47,z48,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z49,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z51]),(0,[z1,z7,z3,z4,z5,z6,z52]),(0,[z1,z13,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z53]),(0,[z1,z7,z3,z50,z4,z5,z54])]],
   [[(0,[z55,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z16,z6]),(0,[z1,z7,z3,z50,z4,z56,z5]),(0,[z1,z7,z3,z57,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z58,z6]),(0,[z59,z1,z7,z3,z4,z5,z6])],[(1,[z48,z7,z3,z34,z5,z6]),(0,[z1,z7,z3,z4,z5,z60,z6]),(0,[z1,z7,z3,z4,z61,z5,z6])],[(0,[z1,z7,z3,z4,z5,z62,z6]),(0,[z63,z1,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z64,z4,z5]),(0,[z1,z65,z7,z3,z4,z5,z6])],[(1,[z66,z7,z3,z56,z5,z6]),(0,[z47,z7,z3,z4,z56,z5,z6]),(0,[z48,z1,z7,z3,z4,z5,z67]),(0,[z1,z7,z3,z4,z68,z5,z6]),(0,[z1,z69,z7,z3,z4,z5,z6]),(0,[z43,z1,z7,z3,z4,z5,z6])],[(0,[z70,z1,z7,z3,z4,z5,z6]),(0,[z1,z71,z7,z3,z4,z5,z6]),(0,[z1,z7,z72,z3,z4,z5,z6]),(0,[z73,z7,z3,z4,z5,z6,z74]),(0,[z1,z7,z3,z4,z5,z6,z75]),(0,[z1,z7,z3,z4,z5,z76,z6]),(0,[z1,z7,z3,z77,z4,z5,z6]),(0,[z78,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z79,z5,z6])],[(0,[z1,z7,z3,z4,z80,z5,z6])],[(0,[z1,z7,z3,z4,z5,z37,z51]),(0,[z26,z1,z17,z7,z3,z4,z5]),(0,[z1,z40,z7,z3,z81,z4,z6]),(0,[z82,z26,z1,z7,z3,z4,z5]),(1,[z43,z1,z7,z4,z5,z45]),(0,[z1,z7,z3,z4,z5,z83,z6])],[(1,[z1,z7,z3,z4,z5,z84]),(0,[z85,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z86,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z87,z4,z5,z6]),(0,[z1,z7,z88,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z89]),(0,[z1,z7,z90,z3,z4,z5,z6])],[(0,[z1,z7,z3,z24,z50,z4,z5])],[(0,[z1,z7,z3,z4,z91,z5,z6]),(0,[z1,z7,z92,z3,z4,z5,z6]),(1,[z1,z7,z3,z93,z5,z6]),(0,[z1,z7,z3,z4,z94,z5,z6]),(1,[z1,z7,z95,z4,z5,z6]),(0,[z26,z26,z1,z7,z3,z4,z5]),(0,[z26,z1,z7,z3,z5,z6,z96]),(0,[z97,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z98,z5,z6]),(0,[z99,z1,z7,z100,z4,z5,z6]),(0,[z1,z7,z3,z4,z101,z5,z6]),(0,[z102,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z67]),(0,[z1,z7,z3,z103,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z104,z6]),(0,[z105,z1,z7,z3,z50,z4,z5])],[(0,[z7,z3,z4,z5,z37,z6,z74]),(0,[z1,z3,z20,z4,z106,z5,z6])],[(1,[z1,z7,z87,z4,z5,z6]),(0,[z99,z1,z7,z3,z4,z5,z16]),(0,[z107,z1,z7,z3,z5,z108,z6]),(0,[z29,z1,z7,z3,z4,z5,z6])],[(0,[z55,z1,z109,z3,z4,z5,z6]),(0,[z1,z7,z3,z110,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z111]),(0,[z1,z112,z7,z3,z4,z5,z113]),(0,[z1,z7,z95,z3,z4,z5,z6]),(0,[z114,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z66,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z115,z6]),(0,[z116,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z117,z4,z5,z6]),(0,[z1,z118,z7,z3,z4,z5,z6])],[(0,[z107,z1,z7,z3,z56,z5,z6]),(0,[z1,z7,z3,z119,z4,z5,z6]),(0,[z120,z7,z3,z20,z4,z5,z6]),(0,[z1,z7,z121,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z122,z6]),(0,[z1,z7,z3,z4,z123,z5,z6]),(1,[z107,z26,z1,z7,z3,z5]),(0,[z1,z7,z3,z4,z124,z5,z6]),(0,[z1,z7,z3,z125,z4,z36,z6])],[(0,[z1,z7,z3,z126,z4,z5,z6]),(0,[z1,z7,z127,z3,z4,z5,z128])],[(0,[z1,z7,z3,z129,z4,z5,z6]),(0,[z1,z130,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z108,z6]),(1,[z1,z7,z3,z4,z36,z131])],[(0,[z7,z3,z4,z56,z5,z25,z6]),(0,[z1,z112,z7,z3,z4,z5,z132]),(0,[z26,z1,z7,z133,z3,z4,z5])],[(0,[z99,z109,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z134]),(0,[z1,z7,z3,z4,z5,z135,z6]),(0,[z1,z7,z3,z4,z5,z11,z74]),(0,[z1,z7,z3,z136,z4,z5,z6]),(0,[z26,z1,z7,z3,z35,z4,z5]),(0,[z137,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z138]),(0,[z26,z1,z7,z3,z4,z36,z5])],[(1,[z1,z7,z3,z4,z139,z6]),(0,[z26,z1,z7,z3,z34,z4,z5]),(0,[z26,z1,z7,z3,z4,z5,z74]),(0,[z1,z140,z7,z3,z4,z5,z6])],[(0,[z141,z1,z7,z3,z4,z5,z6]),(0,[z142,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z56,z5,z6]),(0,[z73,z1,z7,z3,z4,z5,z37]),(0,[z1,z7,z3,z4,z143,z5,z6]),(0,[z107,z1,z112,z7,z3,z4,z6]),(0,[z82,z1,z7,z3,z4,z5,z6]),(0,[z1,z144,z7,z3,z4,z5,z6]),(0,[z1,z31,z7,z3,z50,z4,z5])]],
   [[(0,[z145,z7,z3,z4,z56,z5,z6]),(0,[z107,z1,z7,z3,z34,z5,z6])],[(0,[z1,z7,z127,z18,z4,z5,z6]),(0,[z85,z1,z7,z146,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z147,z6]),(0,[z1,z7,z3,z148,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z96])],[(0,[z145,z1,z7,z3,z4,z5,z149]),(0,[z145,z1,z7,z3,z4,z150,z6]),(0,[z1,z7,z3,z146,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z11,z6]),(0,[z151,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z152,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z153])],[(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z154,z5,z6]),(0,[z1,z155,z7,z3,z4,z5,z6])],[(0,[z156,z1,z7,z3,z4,z5,z6]),(0,[z43,z1,z7,z3,z50,z4,z5]),(0,[z157,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z18,z4,z14,z5,z6]),(1,[z1,z7,z3,z4,z5,z158]),(1,[z1,z7,z3,z81,z159,z6]),(0,[z1,z7,z3,z77,z50,z4,z5])],[(0,[z1,z160,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z34,z39,z5,z6]),(0,[z85,z26,z1,z7,z3,z4,z5]),(0,[z1,z7,z4,z14,z5,z161,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z162,z6]),(0,[z1,z13,z163,z3,z4,z5,z6])],[(0,[z1,z38,z7,z3,z106,z5,z6]),(0,[z1,z7,z3,z164,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z11,z165]),(0,[z1,z166,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z128,z6])],[(0,[z1,z7,z3,z4,z5,z167,z6]),(0,[z1,z168,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z37,z169]),(0,[z26,z1,z7,z3,z4,z5,z165])],[(0,[z1,z7,z3,z4,z5,z45,z74]),(0,[z170,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z171,z5,z6]),(0,[z1,z7,z163,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z172]),(1,[z1,z7,z3,z173,z5,z6]),(1,[z26,z1,z7,z3,z56,z5]),(0,[z1,z7,z3,z4,z5,z174,z6]),(0,[z85,z1,z7,z175,z4,z5,z6]),(0,[z1,z112,z7,z3,z4,z176,z6]),(0,[z1,z7,z3,z4,z177,z5,z6]),(0,[z1,z7,z3,z4,z5,z178,z108]),(0,[z1,z7,z3,z50,z4,z159,z5])],[(0,[z1,z7,z3,z20,z4,z5,z6]),(0,[z179,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z180,z6]),(0,[z1,z7,z3,z4,z5,z181,z6])],[(0,[z182,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z183,z6]),(0,[z1,z184,z7,z3,z4,z5,z6])],[(1,[z185,z7,z3,z4,z25,z6]),(0,[z186,z1,z7,z3,z4,z5,z6]),(0,[z1,z187,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z188]),(0,[z189,z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z34,z4,z56,z5,z6]),(0,[z1,z7,z190,z20,z4,z5,z6]),(0,[z1,z7,z3,z191,z4,z192,z5]),(0,[z193,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z194,z6]),(0,[z26,z195,z7,z3,z4,z5,z6]),(0,[z196,z1,z7,z3,z4,z5,z6])],[(0,[z26,z1,z7,z3,z24,z4,z5]),(0,[z1,z7,z3,z4,z197,z5,z6]),(0,[z198,z1,z7,z3,z4,z5,z6]),(1,[z73,z7,z3,z4,z5,z74]),(0,[z1,z7,z3,z4,z199,z5,z6])],[(1,[z55,z109,z3,z4,z5,z6]),(0,[z200,z1,z7,z3,z4,z5,z6]),(0,[z66,z1,z7,z3,z50,z4,z5]),(0,[z107,z1,z7,z127,z3,z4,z6]),(0,[z1,z7,z3,z4,z201,z5,z6])],[(0,[z1,z112,z3,z20,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z176,z6])],[(0,[z1,z7,z202,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z5,z6]),(0,[z185,z1,z7,z3,z4,z25,z6])],[(0,[z1,z7,z3,z203,z4,z5,z6]),(0,[z82,z1,z7,z4,z192,z5,z6]),(0,[z43,z1,z7,z3,z4,z5,z45]),(0,[z107,z204,z7,z3,z4,z5,z6])],[(0,[z205,z1,z7,z3,z4,z5,z6]),(0,[z1,z206,z7,z20,z4,z5,z6]),(0,[z207,z1,z7,z3,z4,z5,z6]),(0,[z1,z208,z7,z3,z4,z5,z51]),(1,[z1,z7,z3,z209,z4,z5]),(0,[z1,z7,z3,z4,z5,z210,z6]),(1,[z1,z13,z7,z4,z14,z6]),(0,[z1,z7,z3,z50,z4,z211,z5])],[(0,[z1,z7,z3,z4,z139,z5,z6]),(0,[z1,z7,z18,z100,z4,z5,z6]),(0,[z107,z1,z7,z3,z4,z150,z6]),(0,[z1,z7,z3,z4,z5,z212,z6]),(0,[z1,z7,z3,z4,z5,z45,z165])]],
   [[(0,[z1,z7,z3,z4,z5,z213,z6]),(1,[z1,z7,z3,z4,z5,z178])],[(0,[z1,z7,z3,z3,z4,z5,z6]),(0,[z214,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z215,z5,z6]),(0,[z82,z1,z7,z3,z50,z4,z5]),(0,[z26,z1,z7,z44,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z216,z6]),(1,[z1,z7,z3,z217,z4,z5]),(0,[z26,z59,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z218,z6]),(0,[z1,z219,z7,z3,z4,z5,z6]),(0,[z48,z7,z3,z34,z4,z5,z6]),(0,[z1,z7,z220,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z221]),(0,[z1,z7,z3,z4,z5,z6,z222])],[(0,[z99,z1,z223,z3,z4,z5,z6]),(0,[z224,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z225,z3,z4,z5,z6]),(0,[z226,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z227]),(0,[z107,z1,z40,z7,z3,z4,z6]),(0,[z228,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z229,z5,z6]),(1,[z230,z7,z100,z4,z5,z6]),(0,[z48,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z231,z4,z5,z6]),(0,[z1,z7,z3,z232,z4,z5,z6]),(0,[z43,z26,z1,z7,z3,z4,z5]),(0,[z26,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z152,z50,z4,z5])],[(0,[z0,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z233,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z25]),(0,[z234,z1,z7,z3,z4,z5,z6]),(0,[z235,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z236]),(0,[z1,z7,z3,z4,z5,z131,z6]),(0,[z1,z7,z237,z3,z4,z5,z6]),(0,[z1,z7,z238,z3,z4,z5,z6])],[(0,[z99,z1,z7,z3,z173,z5,z6]),(0,[z1,z7,z3,z239,z4,z5,z6]),(0,[z1,z240,z7,z3,z4,z5,z6]),(0,[z47,z1,z7,z3,z4,z5,z37]),(0,[z1,z17,z18,z3,z4,z5,z6]),(0,[z85,z1,z7,z3,z106,z5,z6]),(0,[z82,z1,z90,z3,z4,z5,z6]),(0,[z241,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z159,z5,z242,z6])]],
   [[(0,[z1,z7,z3,z98,z4,z5,z6]),(0,[z1,z243,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z81,z4,z150,z6]),(0,[z1,z7,z3,z4,z5,z6,z74]),(0,[z1,z7,z3,z125,z4,z5,z37]),(0,[z1,z244,z7,z3,z4,z5,z6])],[(0,[z1,z245,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z246,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z247])],[(0,[z1,z7,z3,z4,z5,z248,z6]),(0,[z1,z206,z7,z3,z4,z5,z6]),(1,[z1,z7,z127,z4,z161,z6]),(0,[z1,z7,z3,z4,z5,z249,z6])],[(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z26,z1,z7,z100,z3,z4,z5]),(0,[z66,z48,z7,z3,z4,z5,z6]),(0,[z250,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z251,z4,z5,z6]),(0,[z1,z7,z252,z3,z4,z5,z6]),(0,[z253,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z254]),(0,[z1,z7,z3,z4,z36,z5,z131])],[(0,[z1,z7,z3,z4,z5,z6,z6]),(0,[z255,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z256,z5,z6]),(0,[z1,z7,z3,z4,z5,z257,z6]),(0,[z1,z7,z3,z4,z5,z6,z258]),(1,[z26,z1,z7,z3,z5,z96])],[(0,[z1,z7,z259,z3,z4,z5,z6]),(0,[z0,z99,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z260,z4,z5,z6]),(0,[z1,z17,z3,z4,z21,z5,z6]),(0,[z1,z40,z7,z3,z4,z21,z6])],[(0,[z261,z1,z7,z3,z4,z5,z6]),(0,[z66,z7,z3,z4,z56,z5,z6]),(0,[z1,z7,z3,z20,z50,z4,z5]),(0,[z1,z7,z262,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z263,z5,z6]),(0,[z107,z1,z13,z7,z3,z4,z6]),(1,[z107,z1,z7,z3,z108,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z264]),(0,[z1,z7,z3,z265,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z75]),(0,[z1,z7,z190,z3,z192,z5,z6])],[(0,[z26,z1,z7,z2,z3,z4,z5]),(0,[z1,z7,z3,z4,z266,z5,z6]),(0,[z1,z40,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z267,z5,z6]),(0,[z1,z7,z3,z4,z5,z268,z6]),(0,[z1,z7,z269,z3,z4,z192,z6])],[(0,[z0,z1,z7,z3,z270,z5,z6]),(0,[z189,z1,z7,z3,z50,z4,z5])],[(0,[z271,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z217,z4,z5,z108]),(0,[z1,z7,z3,z4,z5,z272,z6])],[(0,[z0,z1,z109,z3,z4,z5,z6]),(0,[z48,z1,z7,z3,z4,z273,z6]),(0,[z1,z7,z3,z4,z21,z25,z6]),(0,[z1,z7,z3,z4,z274,z5,z6]),(0,[z1,z7,z3,z4,z5,z169,z74]),(0,[z1,z7,z3,z4,z5,z275,z6]),(0,[z1,z7,z3,z4,z276,z5,z6]),(1,[z1,z7,z3,z4,z277,z6]),(0,[z1,z278,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z165])],[(0,[z228,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z279,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z45]),(0,[z26,z1,z7,z3,z4,z5,z280]),(0,[z1,z7,z3,z4,z5,z6,z32])],[(0,[z281,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z282]),(0,[z1,z283,z7,z3,z4,z5,z6])],[(0,[z1,z7,z284,z3,z4,z5,z6]),(0,[z285,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z67]),(0,[z1,z7,z3,z4,z192,z5,z6]),(0,[z1,z7,z3,z4,z5,z286,z6]),(0,[z1,z7,z3,z50,z4,z5,z131])]],
   [[(0,[z1,z7,z100,z20,z4,z5,z6]),(0,[z26,z1,z7,z127,z3,z4,z5])],[(0,[z99,z1,z7,z3,z4,z5,z6]),(0,[z287,z1,z7,z3,z4,z5,z6]),(0,[z48,z7,z3,z4,z5,z25,z6]),(0,[z1,z7,z3,z4,z5,z149,z6]),(0,[z1,z7,z3,z125,z4,z150,z6]),(0,[z1,z7,z3,z4,z5,z288,z6]),(0,[z1,z7,z127,z3,z4,z5,z289]),(0,[z1,z7,z44,z3,z4,z5,z169])],[(0,[z99,z1,z7,z24,z4,z5,z6]),(0,[z26,z1,z7,z3,z20,z4,z5])],[(0,[z290,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z291,z4,z5]),(0,[z1,z7,z292,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z293,z6]),(0,[z26,z1,z7,z3,z4,z5,z96])],[(0,[z1,z7,z3,z50,z4,z5,z37]),(0,[z1,z7,z3,z209,z4,z5,z6]),(0,[z1,z294,z7,z3,z4,z5,z6]),(1,[z59,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z295]),(0,[z1,z7,z3,z291,z4,z56,z5]),(0,[z26,z1,z7,z3,z4,z150,z5]),(0,[z1,z7,z20,z4,z192,z5,z6]),(0,[z1,z7,z296,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z297,z6]),(0,[z1,z7,z3,z4,z298,z5,z6]),(0,[z1,z7,z3,z4,z299,z5,z6])],[(0,[z0,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z3,z300,z4,z5,z6]),(0,[z48,z1,z7,z3,z50,z4,z5]),(0,[z1,z301,z7,z3,z4,z5,z6]),(0,[z1,z17,z3,z4,z106,z5,z6]),(0,[z1,z302,z7,z3,z4,z5,z6]),(0,[z107,z26,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z303,z6]),(0,[z304,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z7,z3,z4,z56,z5,z6,z74]),(0,[z305,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z306,z6]),(0,[z1,z7,z3,z4,z5,z169,z165])],[(0,[z1,z7,z3,z4,z5,z307,z6]),(0,[z308,z1,z7,z3,z4,z5,z6])],[(0,[z309,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z310,z3,z4,z5,z6]),(0,[z26,z1,z40,z7,z3,z4,z5]),(0,[z1,z7,z311,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z312,z6])],[(0,[z1,z313,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z314,z5,z6]),(0,[z1,z7,z100,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z315,z5,z6]),(0,[z1,z206,z7,z3,z50,z4,z5]),(0,[z1,z38,z7,z3,z39,z5,z6]),(0,[z204,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z159,z5,z6])],[(0,[z1,z7,z3,z4,z5,z316,z6]),(1,[z1,z7,z3,z4,z293,z6]),(0,[z1,z317,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z318]),(0,[z1,z7,z44,z4,z5,z6,z169]),(0,[z26,z1,z319,z7,z3,z4,z5])],[(0,[z99,z1,z320,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z14,z150,z6]),(0,[z321,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z322,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z176])],[(0,[z1,z7,z3,z4,z150,z5,z6]),(0,[z1,z38,z3,z20,z4,z5,z6]),(0,[z323,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z324,z5,z6]),(1,[z1,z278,z3,z4,z5,z6])]],
   [[(0,[z145,z7,z3,z4,z150,z5,z6]),(0,[z1,z40,z7,z325,z4,z5,z6])],[(0,[z99,z1,z7,z3,z4,z5,z295]),(1,[z99,z7,z24,z4,z5,z6]),(0,[z326,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z242,z6])],[(0,[z1,z7,z3,z4,z5,z131,z11])],[(0,[z1,z7,z3,z327,z4,z5,z6]),(0,[z1,z40,z7,z3,z50,z4,z5]),(0,[z328,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z329,z5])],[(1,[z1,z7,z3,z270,z5,z6]),(0,[z185,z1,z7,z3,z4,z5,z6]),(0,[z1,z330,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z191,z4,z5,z6]),(0,[z1,z7,z3,z4,z331,z5,z6])],[(0,[z332,z1,z7,z3,z4,z5,z6]),(0,[z333,z1,z7,z3,z4,z5,z6]),(1,[z1,z112,z3,z4,z176,z6]),(0,[z1,z7,z3,z4,z5,z334,z6]),(0,[z26,z1,z13,z7,z3,z4,z5]),(0,[z335,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z336,z6]),(0,[z1,z7,z3,z50,z4,z5,z169]),(0,[z1,z7,z3,z4,z5,z337,z6])],[(0,[z1,z7,z338,z3,z4,z5,z6]),(0,[z107,z1,z7,z3,z4,z108,z6])]],
   [[(0,[z1,z7,z339,z3,z4,z5,z6]),(0,[z340,z1,z7,z3,z4,z5,z6]),(0,[z10,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z341,z4,z5,z6])],[(0,[z1,z7,z3,z4,z342,z5,z6]),(0,[z1,z7,z3,z4,z150,z131,z6]),(0,[z1,z7,z343,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z344]),(0,[z1,z7,z3,z4,z345,z5,z6]),(0,[z1,z7,z3,z50,z4,z21,z5]),(0,[z1,z7,z3,z4,z5,z161,z6]),(1,[z196,z1,z7,z3,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z346]),(1,[z1,z7,z3,z347,z5,z6]),(1,[z1,z7,z146,z4,z5,z6]),(0,[z348,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z132,z6]),(0,[z1,z7,z3,z349,z4,z5,z6]),(0,[z1,z350,z7,z3,z4,z5,z6])],[(1,[z1,z223,z3,z4,z5,z6]),(0,[z99,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z351,z6]),(0,[z1,z7,z3,z352,z4,z5,z6]),(0,[z1,z7,z3,z353,z4,z5,z6])],[],[(0,[z1,z7,z3,z39,z56,z5,z6]),(0,[z1,z7,z3,z4,z5,z354,z6]),(0,[z47,z1,z7,z3,z93,z5,z6]),(0,[z224,z26,z1,z7,z3,z4,z5])],[(0,[z66,z1,z7,z3,z56,z5,z6]),(0,[z1,z7,z3,z4,z5,z355,z6]),(0,[z1,z7,z18,z190,z4,z5,z6]),(0,[z1,z356,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z54,z6])],[(1,[z1,z206,z20,z4,z5,z6]),(1,[z1,z7,z3,z4,z357,z6]),(0,[z1,z7,z3,z4,z5,z358,z6])]],
   [[(0,[z230,z7,z100,z3,z4,z5,z6]),(0,[z1,z7,z3,z359,z4,z5,z6]),(0,[z1,z7,z3,z93,z4,z5,z6]),(0,[z360,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z361,z6]),(0,[z1,z7,z362,z3,z4,z5,z6]),(1,[z26,z1,z7,z3,z4,z5])],[(0,[z363,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z364,z6]),(0,[z365,z1,z7,z3,z4,z5,z6])],[(0,[z366,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z367]),(0,[z368,z1,z7,z3,z4,z5,z6]),(0,[z85,z1,z7,z3,z39,z5,z6]),(0,[z1,z7,z3,z369,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z370,z6])],[(0,[z1,z7,z3,z34,z192,z5,z6]),(0,[z1,z7,z3,z371,z4,z5,z6]),(0,[z1,z7,z3,z4,z372,z5,z6]),(0,[z373,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z108])],[(0,[z1,z7,z3,z4,z5,z6,z374]),(0,[z1,z7,z3,z4,z173,z5,z6]),(0,[z1,z7,z3,z4,z5,z111,z6]),(0,[z1,z7,z3,z375,z4,z5,z6]),(1,[z1,z7,z3,z376,z4,z5]),(0,[z377,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z81,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z378])],[(0,[z66,z1,z7,z3,z34,z5,z6]),(0,[z1,z7,z18,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z379,z5,z6]),(0,[z1,z380,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z381,z6]),(0,[z1,z7,z3,z4,z5,z6,z96])],[(0,[z0,z1,z7,z259,z4,z5,z6]),(0,[z1,z7,z18,z24,z4,z5,z6]),(0,[z1,z7,z100,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z382,z5,z6]),(0,[z1,z7,z3,z4,z5,z383,z6])],[(0,[z1,z320,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z384,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z289])]],
   [[(0,[z1,z18,z3,z20,z4,z5,z6]),(0,[z1,z3,z39,z4,z106,z5,z6]),(0,[z1,z112,z7,z3,z81,z4,z6]),(0,[z1,z7,z3,z385,z4,z5,z6]),(1,[z386,z7,z3,z4,z5,z6])],[(0,[z1,z109,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z387,z5,z6]),(0,[z388,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z389,z4,z5,z6]),(0,[z26,z1,z7,z3,z56,z5,z6]),(0,[z1,z390,z7,z3,z4,z5,z6]),(0,[z73,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z391,z5,z6])],[(0,[z1,z7,z3,z50,z4,z192,z5]),(0,[z26,z1,z7,z190,z3,z4,z5])],[(0,[z392,z1,z7,z3,z4,z5,z6]),(0,[z393,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z394,z6]),(0,[z395,z1,z7,z3,z4,z5,z6]),(0,[z82,z1,z7,z3,z35,z5,z6]),(0,[z1,z7,z3,z4,z5,z396,z6]),(0,[z1,z7,z3,z4,z5,z6,z397])],[(0,[z1,z7,z3,z4,z21,z5,z6]),(0,[z1,z7,z3,z4,z5,z398,z6]),(0,[z26,z1,z7,z3,z4,z5,z51]),(0,[z1,z7,z3,z399,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z128]),(0,[z1,z7,z3,z400,z4,z5,z6])],[(0,[z26,z1,z7,z3,z4,z56,z5]),(0,[z1,z7,z3,z401,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z106,z5])],[(0,[z109,z7,z100,z3,z4,z5,z6]),(0,[z1,z402,z7,z3,z4,z5,z6]),(0,[z1,z403,z7,z3,z4,z5,z6]),(0,[z185,z1,z7,z3,z50,z4,z5]),(0,[z145,z1,z7,z3,z4,z25,z6]),(0,[z1,z206,z17,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z404,z5,z6]),(0,[z1,z7,z269,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z4,z5]),(0,[z1,z7,z3,z125,z4,z5,z131])],[(0,[z1,z7,z405,z3,z4,z5,z6]),(0,[z230,z1,z7,z24,z4,z5,z6]),(0,[z145,z1,z7,z3,z4,z5,z84]),(0,[z1,z7,z3,z4,z5,z406,z6]),(0,[z1,z7,z3,z4,z407,z5,z6]),(0,[z1,z7,z190,z3,z4,z5,z6]),(0,[z1,z7,z3,z35,z4,z5,z6]),(0,[z332,z1,z7,z3,z50,z4,z5])]],
   [[(0,[z1,z7,z3,z34,z159,z5,z6]),(0,[z26,z1,z7,z3,z34,z5,z6]),(0,[z408,z1,z7,z3,z4,z5,z6]),(0,[z26,z1,z112,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z409]),(0,[z1,z7,z3,z50,z4,z14,z5])],[(1,[z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z56,z5,z242,z6]),(0,[z1,z7,z3,z4,z215,z5,z6]),(0,[z1,z410,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z277,z192,z6]),(0,[z411,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z412,z3,z4,z5,z6]),(0,[z1,z7,z190,z35,z4,z5,z6]),(0,[z1,z7,z3,z413,z4,z5,z6]),(1,[z26,z59,z7,z3,z4,z5])],[(0,[z1,z414,z7,z3,z4,z5,z6]),(0,[z99,z26,z1,z7,z3,z4,z5]),(0,[z230,z1,z7,z100,z4,z5,z6]),(0,[z1,z7,z3,z4,z415,z5,z6]),(0,[z1,z7,z416,z3,z4,z5,z6]),(0,[z1,z7,z3,z417,z4,z5,z6]),(0,[z107,z1,z7,z3,z4,z159,z6])],[(0,[z1,z7,z3,z4,z5,z418,z6]),(0,[z419,z1,z7,z3,z4,z5,z6]),(0,[z420,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z3,z34,z5,z242,z6]),(0,[z1,z7,z3,z4,z5,z11,z37]),(0,[z82,z1,z410,z3,z4,z5,z6]),(0,[z1,z421,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z422])],[(0,[z1,z7,z3,z4,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z423,z6]),(0,[z1,z7,z3,z4,z5,z6,z424]),(0,[z1,z7,z3,z4,z5,z273,z6]),(0,[z26,z1,z7,z3,z4,z5,z37]),(0,[z1,z425,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z217,z4,z5,z6])],[(0,[z426,z1,z7,z3,z4,z5,z6]),(0,[z1,z427,z7,z3,z4,z5,z6]),(0,[z10,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z242])]],
   [[(0,[z26,z55,z1,z7,z3,z4,z5]),(0,[z1,z7,z428,z3,z4,z5,z6]),(0,[z1,z7,z22,z3,z4,z106,z5]),(0,[z1,z7,z429,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z430,z6]),(0,[z1,z7,z3,z50,z5,z242,z6])],[(0,[z1,z7,z3,z4,z431,z5,z6])],[(0,[z1,z7,z432,z3,z4,z5,z6]),(0,[z1,z7,z18,z4,z192,z5,z6]),(0,[z1,z208,z3,z4,z5,z6,z51]),(0,[z1,z7,z3,z4,z159,z5,z378])],[(0,[z145,z185,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z433,z4,z5,z6]),(0,[z1,z7,z3,z81,z4,z159,z6]),(1,[z26,z1,z7,z3,z50,z5]),(0,[z434,z1,z7,z3,z4,z5,z6])],[(0,[z48,z7,z3,z4,z5,z6,z74]),(0,[z1,z7,z3,z4,z435,z5,z6]),(0,[z1,z7,z3,z4,z25,z161,z6]),(0,[z1,z7,z3,z4,z5,z436,z6]),(0,[z1,z7,z3,z376,z4,z106,z5]),(0,[z437,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z438,z4,z5,z6]),(0,[z1,z439,z7,z3,z4,z5,z6])],[(0,[z99,z230,z7,z3,z4,z5,z6]),(1,[z1,z320,z3,z4,z5,z6]),(1,[z1,z7,z3,z440,z5,z6]),(1,[z47,z7,z3,z4,z5,z37]),(0,[z1,z17,z38,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z441,z5,z6]),(0,[z442,z1,z7,z3,z4,z5,z6]),(1,[z195,z7,z3,z4,z5,z6])],[(0,[z443,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z18,z3,z50,z4,z5]),(1,[z1,z38,z3,z39,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z444]),(0,[z1,z7,z3,z4,z5,z6,z445]),(1,[z1,z7,z3,z125,z4,z165])]],
   [[(1,[z1,z7,z259,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z446,z6]),(1,[z1,z7,z3,z4,z273,z6]),(0,[z48,z1,z7,z3,z4,z447,z6]),(0,[z1,z448,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z449,z4,z5,z6]),(0,[z1,z7,z3,z4,z450,z5,z6])],[(0,[z1,z7,z3,z4,z5,z451,z6]),(1,[z1,z7,z3,z4,z5,z295]),(0,[z47,z73,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z452,z6]),(0,[z453,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z454,z6])],[(0,[z455,z1,z7,z3,z4,z5,z6]),(0,[z99,z1,z7,z3,z4,z456,z6]),(0,[z1,z7,z457,z3,z4,z5,z6]),(0,[z1,z458,z7,z3,z4,z5,z6]),(0,[z1,z7,z459,z3,z4,z5,z6])],[(0,[z1,z109,z7,z3,z50,z4,z5]),(0,[z48,z1,z7,z3,z56,z5,z6]),(0,[z107,z1,z7,z3,z4,z25,z6]),(0,[z1,z7,z3,z4,z440,z5,z6]),(0,[z73,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z45,z37]),(0,[z1,z7,z3,z325,z4,z5,z6]),(1,[z1,z7,z190,z35,z5,z6]),(1,[z26,z1,z7,z3,z159,z5]),(0,[z460,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z150,z161,z6]),(0,[z47,z1,z7,z3,z215,z5,z6]),(0,[z1,z7,z3,z4,z5,z461,z6])],[(0,[z420,z1,z7,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z4,z5,z374]),(0,[z1,z17,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z462,z6]),(0,[z7,z100,z3,z24,z4,z5,z6]),(0,[z1,z7,z3,z463,z4,z5,z6]),(0,[z1,z7,z464,z3,z4,z5,z6])],[(0,[z465,z1,z7,z3,z4,z5,z6]),(0,[z145,z1,z7,z3,z347,z5,z6]),(0,[z1,z7,z466,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z467,z6]),(0,[z332,z26,z1,z7,z3,z4,z5])]],
   [[(0,[z1,z7,z3,z468,z4,z5,z6]),(1,[z1,z7,z325,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z169]),(0,[z1,z7,z3,z4,z5,z469,z6]),(0,[z1,z470,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z471,z4,z5,z6]),(0,[z1,z7,z3,z4,z456,z5,z6]),(0,[z47,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z51,z74]),(0,[z120,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z190,z3,z50,z4,z5]),(0,[z472,z1,z7,z3,z4,z5,z6])],[(0,[z1,z2,z3,z20,z4,z5,z6]),(0,[z1,z473,z7,z3,z4,z5,z6]),(0,[z48,z1,z7,z3,z34,z5,z6]),(0,[z26,z185,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z474,z4,z5,z6])],[(0,[z99,z7,z3,z24,z4,z5,z6]),(0,[z1,z7,z3,z4,z475,z5,z6]),(0,[z1,z7,z3,z4,z476,z5,z6]),(1,[z1,z7,z3,z50,z4,z5])],[(0,[z1,z7,z3,z81,z4,z25,z6])],[(0,[z1,z7,z3,z477,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z478,z6]),(0,[z1,z7,z3,z479,z4,z5,z6]),(0,[z1,z7,z3,z4,z480,z5,z6]),(0,[z10,z1,z208,z3,z4,z5,z6]),(0,[z481,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z482])],[(0,[z1,z7,z3,z4,z36,z5,z74]),(0,[z1,z7,z3,z4,z5,z6,z51]),(0,[z1,z13,z7,z4,z14,z5,z6]),(0,[z1,z7,z3,z4,z5,z483,z6]),(0,[z1,z7,z3,z4,z5,z6,z484]),(0,[z107,z1,z7,z3,z5,z242,z6]),(0,[z1,z7,z485,z3,z4,z5,z6]),(0,[z1,z486,z7,z3,z4,z5,z6])],[(0,[z1,z17,z109,z3,z4,z5,z6]),(0,[z1,z7,z175,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z50,z5,z6])]],
   [[(1,[z1,z7,z3,z4,z462,z6]),(0,[z1,z487,z7,z3,z4,z5,z6]),(1,[z1,z488,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z489,z6])],[(0,[z47,z7,z3,z4,z5,z37,z6]),(1,[z120,z7,z3,z4,z5,z6]),(0,[z10,z1,z7,z3,z50,z4,z5]),(1,[z1,z90,z3,z4,z5,z6]),(0,[z1,z7,z490,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z491,z5,z6]),(0,[z1,z7,z127,z3,z81,z4,z6]),(0,[z1,z492,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z159,z5])],[(0,[z0,z1,z7,z3,z4,z5,z493]),(0,[z1,z7,z3,z494,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z495,z6]),(0,[z1,z7,z3,z81,z159,z5,z6])],[(0,[z1,z7,z3,z4,z496,z5,z6]),(0,[z1,z497,z7,z3,z4,z5,z6]),(0,[z498,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z499,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z36,z5,z6])],[(0,[z1,z7,z3,z4,z500,z5,z6]),(0,[z1,z7,z3,z4,z501,z5,z6]),(0,[z460,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z502])],[(0,[z1,z503,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z25,z131,z6]),(0,[z1,z7,z3,z4,z5,z504,z6]),(0,[z1,z7,z3,z4,z505,z5,z6]),(0,[z1,z7,z3,z4,z5,z51,z165]),(0,[z1,z7,z3,z4,z5,z506,z6]),(0,[z1,z7,z3,z4,z507,z5,z6]),(0,[z26,z1,z7,z3,z4,z5,z108]),(0,[z373,z26,z1,z7,z3,z4,z5])],[(0,[z1,z7,z508,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z509,z5,z6]),(0,[z1,z7,z3,z4,z510,z5,z6]),(0,[z26,z1,z38,z7,z3,z4,z5]),(1,[z82,z1,z7,z192,z5,z6]),(0,[z26,z1,z7,z3,z81,z4,z5])],[(1,[z1,z7,z3,z4,z5,z132]),(0,[z1,z7,z511,z3,z4,z5,z6]),(0,[z512,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z513,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z514,z6]),(0,[z1,z7,z190,z3,z4,z5,z30]),(0,[z1,z7,z3,z50,z35,z4,z5]),(0,[z1,z7,z3,z50,z4,z36,z5])],[(0,[z285,z1,z7,z3,z4,z56,z5]),(0,[z47,z1,z7,z3,z4,z452,z6]),(1,[z7,z3,z117,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z113]),(0,[z1,z7,z3,z4,z515,z5,z6])],[(0,[z1,z7,z3,z4,z516,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z517]),(0,[z1,z7,z3,z34,z4,z5,z6]),(0,[z518,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z30]),(0,[z1,z7,z3,z4,z5,z178,z6]),(1,[z26,z195,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z519]),(0,[z1,z7,z3,z4,z329,z5,z6]),(0,[z1,z7,z3,z4,z36,z5,z165])],[(0,[z520,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z131,z45]),(0,[z1,z7,z3,z4,z5,z521,z6]),(0,[z453,z1,z7,z3,z50,z4,z5])],[(0,[z1,z7,z3,z4,z270,z5,z6]),(0,[z1,z7,z522,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z192,z5]),(0,[z1,z7,z3,z64,z4,z5,z6])],[(0,[z1,z1,z7,z3,z4,z5,z6]),(0,[z523,z1,z7,z3,z4,z5,z6]),(0,[z524,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z125,z4,z25,z6]),(0,[z1,z525,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z176,z6]),(0,[z1,z7,z3,z4,z526,z5,z6]),(0,[z1,z7,z127,z3,z4,z14,z6]),(0,[z527,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z36,z131,z6])],[(0,[z528,z1,z7,z3,z4,z5,z6]),(0,[z145,z1,z7,z3,z4,z5,z6]),(0,[z1,z17,z7,z20,z4,z5,z6]),(0,[z529,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z44,z4,z5,z169]),(0,[z1,z7,z3,z530,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z61,z5])],[(0,[z531,z1,z7,z3,z4,z5,z6])]],
   [[(1,[z1,z7,z3,z4,z5,z374]),(0,[z1,z532,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z533,z4,z5,z6]),(0,[z1,z534,z7,z3,z4,z5,z6]),(0,[z1,z112,z7,z3,z4,z21,z6]),(1,[z1,z7,z3,z4,z5,z378])],[(0,[z1,z535,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z536]),(1,[z1,z7,z269,z3,z4,z6])],[(0,[z1,z7,z3,z4,z5,z537,z6]),(0,[z538,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z56,z192,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z539]),(0,[z1,z13,z7,z3,z81,z4,z6]),(0,[z107,z26,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z468,z50,z4,z5])],[(0,[z99,z1,z7,z3,z540,z5,z6]),(0,[z99,z1,z7,z3,z4,z462,z6]),(0,[z47,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z541,z6]),(0,[z1,z112,z7,z3,z4,z5,z6]),(0,[z1,z112,z3,z4,z5,z176,z6]),(1,[z1,z7,z3,z4,z5,z289]),(0,[z1,z7,z3,z81,z4,z108,z6]),(0,[z1,z7,z3,z542,z4,z5,z6])],[(0,[z26,z73,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z543,z5,z6]),(0,[z1,z7,z3,z4,z544,z5,z6])],[(0,[z1,z7,z545,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z37,z6]),(0,[z546,z1,z7,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z98,z5,z6]),(0,[z547,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z277,z5,z6])],[(0,[z1,z7,z3,z548,z4,z5,z6]),(0,[z73,z1,z7,z3,z4,z5,z74]),(0,[z1,z549,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z550,z5,z6])]],
   [[(0,[z47,z1,z7,z3,z4,z293,z6]),(1,[z1,z7,z175,z4,z5,z6]),(0,[z1,z7,z3,z551,z4,z5,z6]),(0,[z1,z3,z4,z5,z11,z6,z51]),(0,[z1,z7,z3,z4,z5,z552,z6]),(0,[z1,z7,z3,z4,z159,z5,z381])],[(0,[z553,z1,z7,z3,z4,z5,z6]),(0,[z1,z554,z7,z3,z4,z5,z6]),(0,[z1,z7,z22,z3,z4,z5,z6]),(0,[z10,z1,z3,z4,z5,z11,z6]),(0,[z10,z26,z1,z7,z3,z4,z5])],[(0,[z55,z109,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z14,z25,z6]),(0,[z1,z17,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z169]),(0,[z107,z386,z7,z3,z4,z5,z6]),(0,[z1,z195,z7,z3,z4,z5,z6]),(0,[z1,z7,z555,z3,z4,z5,z6])],[(0,[z1,z7,z3,z556,z4,z5,z6]),(0,[z185,z7,z3,z4,z5,z25,z6]),(0,[z1,z7,z557,z3,z4,z5,z6]),(0,[z145,z1,z7,z3,z440,z5,z6]),(0,[z1,z7,z3,z4,z5,z558,z6]),(0,[z1,z7,z559,z3,z4,z5,z6])],[(0,[z560,z1,z7,z3,z4,z5,z6]),(0,[z1,z561,z7,z3,z4,z5,z6]),(0,[z1,z7,z190,z3,z4,z5,z562]),(0,[z1,z13,z7,z127,z4,z5,z6]),(1,[z1,z163,z3,z4,z5,z6])],[(0,[z1,z7,z3,z347,z4,z5,z6]),(0,[z1,z7,z3,z563,z4,z5,z6])],[(0,[z1,z7,z3,z376,z4,z5,z6]),(0,[z1,z208,z7,z3,z4,z5,z11]),(1,[z1,z7,z3,z4,z5,z562]),(0,[z1,z7,z3,z564,z4,z5,z6])],[(0,[z1,z7,z3,z56,z159,z5,z6]),(0,[z1,z7,z3,z4,z5,z158,z6]),(0,[z43,z1,z7,z4,z5,z45,z6])]],
   [[(0,[z1,z7,z3,z565,z4,z5,z6]),(0,[z1,z7,z3,z566,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z567])],[(0,[z0,z1,z7,z3,z4,z139,z6]),(0,[z230,z1,z7,z3,z4,z5,z6]),(0,[z568,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z456,z6]),(0,[z1,z206,z3,z20,z4,z5,z6]),(0,[z1,z40,z7,z3,z4,z176,z6]),(0,[z1,z569,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z50,z4,z5,z161]),(0,[z43,z1,z7,z3,z4,z5,z169]),(0,[z107,z1,z7,z3,z4,z5,z6])],[(0,[z1,z570,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z34,z50,z4,z5]),(0,[z26,z1,z7,z3,z4,z5,z131])],[(0,[z1,z7,z3,z4,z5,z6,z562]),(0,[z1,z7,z3,z571,z4,z5,z6])],[(0,[z1,z7,z572,z3,z4,z5,z6]),(0,[z26,z1,z7,z18,z3,z4,z5]),(0,[z573,z1,z7,z3,z4,z5,z6]),(0,[z574,z1,z7,z3,z4,z5,z6])],[(0,[z575,z1,z7,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z4,z5,z158]),(0,[z1,z7,z3,z4,z576,z5,z6])]],
   [[(0,[z577,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z578,z5,z6]),(0,[z145,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z579,z6]),(0,[z1,z580,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z50,z4,z5])],[(0,[z1,z7,z581,z3,z4,z5,z6]),(0,[z582,z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z150,z5,z25,z6]),(0,[z1,z7,z3,z50,z4,z5,z25]),(0,[z85,z1,z38,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z39,z4,z5]),(0,[z1,z7,z127,z4,z5,z161,z6]),(0,[z1,z7,z3,z4,z211,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z583])],[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z1,z206,z7,z18,z4,z5,z6]),(0,[z1,z7,z3,z584,z4,z5,z6]),(0,[z1,z319,z7,z3,z4,z5,z6])],[(0,[z47,z26,z1,z7,z3,z4,z5]),(0,[z585,z1,z7,z3,z4,z5,z6]),(0,[z1,z13,z278,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z26,z1,z206,z7,z3,z4,z5]),(0,[z1,z7,z3,z81,z4,z5,z6])],[(0,[z1,z7,z3,z4,z357,z106,z6]),(0,[z1,z112,z7,z3,z50,z4,z5])],[(0,[z1,z7,z3,z4,z5,z6,z586]),(0,[z587,z1,z7,z3,z4,z5,z6]),(0,[z588,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z127,z3,z4,z161,z6]),(0,[z1,z7,z3,z4,z5,z589,z6])],[(0,[z1,z590,z7,z3,z4,z5,z6]),(0,[z1,z7,z591,z3,z4,z5,z6]),(0,[z1,z7,z592,z3,z4,z5,z6]),(0,[z546,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z593,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z594,z5,z6]),(1,[z26,z1,z7,z3,z34,z5]),(0,[z1,z7,z127,z20,z4,z5,z6]),(0,[z1,z7,z3,z4,z106,z5,z6])],[(0,[z1,z7,z3,z4,z25,z176,z6]),(0,[z595,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z596,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z131,z6,z165]),(0,[z1,z7,z3,z4,z5,z6,z597])],[(0,[z1,z7,z3,z50,z4,z5,z11]),(0,[z26,z59,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z551,z50,z4,z5])],[(0,[z0,z7,z100,z3,z4,z5,z6]),(0,[z48,z1,z7,z3,z4,z5,z111]),(0,[z1,z7,z3,z4,z5,z6,z84]),(0,[z1,z598,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z599,z6]),(0,[z7,z3,z117,z20,z4,z5,z6]),(0,[z1,z7,z3,z4,z600,z5,z6]),(0,[z601,z26,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z5,z6,z32,z165])],[(0,[z602,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z447,z6]),(0,[z603,z1,z7,z3,z4,z5,z6]),(0,[z1,z17,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z39,z4,z5,z6]),(0,[z1,z7,z555,z3,z50,z4,z5])],[(0,[z1,z7,z3,z4,z5,z604,z6]),(0,[z1,z7,z3,z35,z56,z5,z6]),(0,[z85,z1,z3,z4,z106,z5,z6]),(0,[z1,z40,z3,z4,z21,z5,z6]),(0,[z82,z1,z7,z190,z4,z5,z6]),(0,[z1,z7,z4,z5,z45,z6,z169])],[(0,[z605,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z50,z5,z242]),(0,[z1,z7,z3,z4,z606,z5,z6])],[(0,[z1,z7,z3,z4,z5,z607,z6]),(0,[z47,z1,z7,z3,z4,z5,z74]),(0,[z1,z7,z3,z4,z608,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z609]),(0,[z1,z7,z3,z4,z610,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z611]),(0,[z1,z7,z612,z3,z4,z5,z6])]],
   [[(0,[z185,z1,z7,z3,z4,z150,z6]),(0,[z1,z7,z3,z4,z150,z176,z6]),(0,[z1,z7,z3,z125,z4,z5,z74]),(0,[z1,z613,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z45])],[(0,[z145,z48,z7,z3,z4,z5,z6]),(0,[z1,z614,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z615,z6])],[(0,[z0,z1,z7,z3,z4,z616,z6]),(0,[z617,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z223,z3,z4,z5,z6]),(0,[z1,z40,z7,z95,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z131,z51])],[(0,[z230,z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z618,z6]),(0,[z1,z7,z190,z3,z35,z5,z6]),(0,[z1,z7,z3,z619,z4,z5,z6])],[(1,[z285,z1,z7,z3,z4,z5]),(0,[z1,z7,z127,z3,z4,z5,z6]),(0,[z1,z7,z44,z3,z4,z5,z6]),(0,[z620,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z621,z6]),(0,[z1,z7,z3,z4,z5,z622,z6]),(0,[z1,z208,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z623,z5,z6]),(0,[z1,z7,z3,z209,z4,z192,z5]),(0,[z1,z7,z3,z4,z5,z624,z6]),(0,[z107,z1,z7,z3,z50,z4,z5]),(1,[z1,z7,z3,z4,z5,z381]),(0,[z1,z7,z3,z125,z4,z5,z6]),(0,[z1,z7,z3,z625,z4,z5,z6])],[(0,[z1,z7,z626,z3,z4,z5,z6]),(0,[z1,z627,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z21,z5])],[(0,[z1,z7,z3,z628,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z629]),(0,[z1,z38,z7,z3,z4,z5,z6]),(0,[z1,z13,z7,z3,z4,z161,z6])]],
   [[(0,[z145,z26,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z50,z4,z150,z5]),(0,[z10,z1,z7,z3,z4,z5,z51]),(0,[z630,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z191,z4,z5]),(0,[z1,z7,z631,z3,z4,z5,z6]),(0,[z632,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z280,z6])],[(0,[z1,z7,z3,z4,z5,z493,z6]),(0,[z633,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z634,z3,z4,z5,z6]),(1,[z85,z1,z3,z106,z5,z6]),(0,[z1,z7,z3,z5,z242,z6,z96]),(0,[z635,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z540,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z636]),(0,[z637,z1,z7,z3,z4,z5,z6]),(0,[z638,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z593,z5])],[(0,[z1,z7,z639,z3,z4,z5,z6]),(0,[z640,z1,z7,z3,z4,z5,z6]),(0,[z601,z1,z7,z3,z4,z5,z6]),(0,[z1,z641,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z642,z4,z5,z6]),(0,[z1,z7,z3,z125,z4,z5,z165])],[(0,[z1,z7,z3,z4,z5,z643,z6]),(0,[z1,z7,z3,z644,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z113]),(0,[z1,z7,z3,z4,z5,z645,z6]),(0,[z1,z7,z3,z4,z646,z5,z6])],[(0,[z1,z7,z2,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z647,z6]),(0,[z1,z7,z3,z4,z648,z5,z6])],[(0,[z26,z48,z1,z7,z3,z4,z5]),(1,[z1,z410,z3,z4,z5,z6]),(0,[z1,z386,z7,z3,z4,z5,z6]),(0,[z1,z7,z649,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z650]),(0,[z1,z7,z3,z4,z651,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z652]),(0,[z26,z1,z208,z7,z3,z4,z5]),(0,[z82,z1,z7,z3,z192,z5,z6]),(0,[z1,z7,z35,z4,z192,z5,z6]),(0,[z1,z7,z3,z4,z653,z5,z6]),(0,[z1,z654,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z125,z4,z5])],[(0,[z1,z488,z7,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z4,z5,z75]),(0,[z1,z7,z3,z50,z4,z5,z176]),(0,[z1,z7,z3,z4,z5,z655,z6])],[(0,[z1,z7,z3,z4,z5,z616,z6]),(0,[z1,z7,z3,z540,z4,z5,z6]),(0,[z1,z7,z3,z656,z4,z5,z6]),(0,[z1,z7,z3,z4,z14,z5,z6])],[(0,[z657,z1,z7,z3,z4,z5,z6]),(0,[z1,z658,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z659,z5,z6]),(0,[z1,z7,z3,z4,z447,z5,z6]),(0,[z1,z7,z3,z660,z4,z5,z6]),(0,[z107,z1,z7,z3,z81,z5,z6])],[(0,[z661,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z5,z74]),(0,[z1,z7,z3,z662,z4,z5,z6]),(0,[z1,z663,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z664,z5,z6])],[(0,[z1,z7,z3,z4,z452,z5,z6]),(0,[z1,z13,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z45,z6]),(0,[z26,z1,z7,z3,z4,z648,z5])],[(0,[z55,z1,z7,z3,z4,z5,z6]),(0,[z109,z7,z2,z3,z4,z5,z6]),(0,[z665,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z666,z5,z6]),(0,[z1,z7,z3,z4,z5,z667,z6]),(0,[z26,z1,z7,z499,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z668])],[(0,[z1,z7,z3,z4,z5,z6,z669]),(0,[z1,z112,z17,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z670,z6]),(0,[z1,z7,z671,z3,z4,z5,z6]),(0,[z1,z7,z3,z672,z4,z5,z6])]],
   [[(0,[z0,z55,z7,z3,z4,z5,z6]),(0,[z1,z7,z7,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z673,z4,z5,z6]),(0,[z1,z674,z7,z3,z4,z5,z6]),(0,[z26,z66,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z56,z106,z5,z6]),(0,[z1,z7,z3,z4,z21,z150,z6]),(0,[z1,z7,z20,z4,z14,z5,z6]),(1,[z1,z208,z3,z4,z5,z51])],[(0,[z1,z7,z3,z4,z675,z5,z6])],[(0,[z676,z1,z7,z3,z4,z5,z6]),(0,[z1,z677,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z678,z6]),(0,[z26,z1,z7,z3,z4,z106,z5]),(0,[z1,z679,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z680,z5,z6]),(0,[z1,z7,z681,z3,z4,z5,z6]),(0,[z157,z1,z7,z3,z4,z5,z6]),(1,[z204,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z616,z6]),(0,[z682,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z34,z106,z5,z6])],[(0,[z683,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z684,z6]),(1,[z1,z7,z3,z4,z5,z149]),(0,[z85,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z685]),(0,[z26,z1,z7,z3,z4,z5,z161]),(0,[z26,z1,z7,z3,z4,z14,z5]),(0,[z1,z7,z3,z125,z4,z6,z165])],[(0,[z1,z7,z3,z686,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z687,z6]),(0,[z1,z7,z127,z3,z50,z4,z5]),(0,[z1,z7,z44,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z131,z169]),(0,[z26,z1,z195,z7,z3,z4,z5]),(0,[z196,z1,z7,z3,z5,z6,z165])],[(0,[z688,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z24,z4,z5,z6]),(0,[z1,z40,z112,z3,z4,z5,z6]),(0,[z1,z689,z7,z3,z4,z5,z6]),(0,[z1,z208,z7,z3,z50,z4,z5]),(0,[z1,z690,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z125,z50,z4,z5])]],
   [[(0,[z1,z7,z3,z50,z4,z5,z165])],[(0,[z1,z7,z3,z4,z691,z5,z6]),(0,[z1,z109,z3,z20,z4,z5,z6]),(0,[z26,z230,z1,z7,z3,z4,z5]),(0,[z105,z1,z7,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z159,z5,z108,z6]),(0,[z26,z1,z7,z3,z159,z5,z6])],[(0,[z692,z1,z7,z3,z4,z5,z6]),(0,[z26,z1,z109,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z693,z5,z6]),(0,[z1,z694,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z695,z4,z5,z6]),(0,[z1,z488,z7,z3,z4,z106,z6]),(0,[z1,z7,z3,z696,z4,z5,z6])],[(0,[z0,z1,z7,z87,z4,z5,z6]),(0,[z1,z7,z3,z291,z4,z5,z6]),(0,[z697,z1,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z39,z4,z5]),(0,[z698,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z699,z6]),(0,[z1,z7,z3,z700,z4,z5,z6])],[(0,[z26,z1,z7,z3,z4,z5,z242]),(0,[z635,z1,z7,z3,z50,z4,z5])],[(0,[z1,z7,z3,z4,z5,z701,z6]),(0,[z702,z1,z7,z3,z4,z5,z6])],[(0,[z703,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z704,z6]),(0,[z1,z7,z705,z3,z4,z5,z6]),(0,[z1,z7,z133,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z493]),(0,[z1,z17,z7,z18,z4,z5,z6]),(0,[z1,z7,z3,z4,z357,z5,z6]),(0,[z706,z1,z7,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z1,z7,z3,z98,z5]),(0,[z1,z708,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z357]),(0,[z1,z709,z3,z4,z5,z6]),(0,[z26,z1,z7,z190,z35,z5]),(0,[z1,z710,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z711]),(0,[z26,z1,z7,z3,z91,z5]),(0,[z1,z7,z3,z50,z347,z5]),(0,[z47,z7,z3,z4,z593,z5]),(0,[z1,z7,z3,z4,z5,z712]),(0,[z1,z7,z238,z4,z5,z45]),(0,[z26,z1,z7,z3,z5,z32])],[(0,[z1,z7,z3,z4,z139,z6]),(0,[z1,z7,z3,z713,z4,z5]),(0,[z26,z1,z7,z3,z5,z282]),(0,[z1,z7,z3,z50,z5,z272])],[(0,[z1,z7,z3,z714,z4,z5]),(0,[z285,z1,z7,z3,z4,z5]),(0,[z204,z7,z3,z347,z5,z6]),(0,[z1,z7,z3,z715,z5,z6]),(0,[z1,z7,z3,z4,z716,z6]),(0,[z1,z7,z3,z4,z5,z717]),(0,[z1,z7,z3,z4,z5,z718])],[(0,[z1,z7,z3,z719,z4,z5]),(0,[z1,z7,z720,z4,z5,z6]),(0,[z1,z488,z3,z20,z4,z6]),(0,[z1,z7,z721,z4,z5,z6]),(0,[z82,z1,z410,z192,z5,z6]),(0,[z1,z7,z44,z64,z4,z5])],[(0,[z1,z20,z4,z431,z5,z6]),(0,[z1,z7,z3,z722,z5,z6]),(0,[z1,z7,z3,z4,z723,z6]),(0,[z26,z1,z7,z3,z441,z5]),(0,[z196,z1,z7,z3,z5,z169])],[(0,[z724,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z125,z4,z629]),(0,[z1,z7,z3,z4,z5,z725]),(0,[z85,z1,z3,z357,z106,z6]),(0,[z1,z3,z4,z726,z5,z6])],[(0,[z99,z7,z727,z4,z5,z6]),(0,[z1,z31,z3,z4,z5,z51]),(0,[z1,z728,z3,z4,z5,z6]),(0,[z26,z386,z7,z3,z4,z5]),(0,[z196,z1,z7,z3,z50,z5])]],
   [[(0,[z1,z7,z3,z4,z5,z729]),(0,[z1,z7,z3,z540,z456,z6]),(0,[z1,z7,z3,z4,z5,z730]),(0,[z1,z7,z3,z731,z4,z5]),(0,[z1,z38,z3,z50,z39,z5]),(0,[z1,z7,z3,z191,z4,z5]),(0,[z1,z278,z3,z81,z4,z6]),(0,[z26,z732,z7,z3,z4,z5])],[(0,[z1,z7,z3,z270,z5,z493]),(0,[z99,z7,z24,z4,z5,z16]),(0,[z48,z7,z3,z34,z5,z111]),(0,[z1,z7,z3,z4,z5,z733])],[(0,[z1,z7,z3,z734,z4,z5]),(0,[z85,z1,z3,z50,z106,z5]),(0,[z1,z7,z3,z735,z5,z6])],[(0,[z1,z7,z736,z3,z4,z5]),(0,[z7,z3,z4,z737,z25,z6]),(0,[z498,z7,z3,z4,z150,z6]),(0,[z82,z1,z90,z192,z5,z6])],[(0,[z59,z7,z3,z93,z5,z6]),(0,[z1,z40,z3,z50,z4,z21]),(0,[z1,z7,z3,z4,z5,z738])],[(0,[z739,z1,z7,z3,z4,z5]),(0,[z1,z223,z24,z4,z5,z6]),(0,[z1,z7,z3,z4,z740,z6]),(0,[z26,z1,z7,z3,z101,z5]),(1,[z1,z7,z4,z741,z6]),(0,[z26,z742,z7,z3,z4,z5])],[(0,[z1,z7,z743,z4,z5,z6]),(0,[z7,z3,z4,z5,z37,z725]),(0,[z1,z7,z744,z4,z5,z6]),(0,[z1,z7,z3,z745,z5,z6]),(0,[z1,z7,z3,z4,z746,z6]),(0,[z747,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z748,z5,z6]),(0,[z1,z7,z3,z749,z5,z6]),(0,[z1,z7,z3,z4,z5,z750]),(0,[z546,z26,z1,z7,z3,z5])]],
   [[(0,[z1,z751,z3,z4,z5,z6]),(0,[z26,z48,z7,z3,z34,z5]),(0,[z1,z7,z95,z50,z4,z5])],[(0,[z1,z223,z100,z4,z5,z6]),(0,[z1,z7,z3,z752,z5,z6]),(0,[z1,z7,z3,z4,z5,z753]),(0,[z1,z7,z3,z50,z4,z447]),(0,[z26,z1,z7,z3,z5,z318])],[(0,[z1,z7,z3,z50,z4,z452]),(0,[z120,z7,z3,z754,z5,z6]),(0,[z1,z112,z362,z3,z4,z6])],[(0,[z1,z7,z3,z755,z5,z6]),(0,[z185,z7,z3,z4,z25,z6]),(0,[z620,z7,z3,z4,z5,z37]),(0,[z1,z7,z3,z4,z756,z6]),(0,[z26,z1,z7,z3,z385,z5])],[(0,[z757,z1,z7,z3,z4,z5]),(0,[z59,z7,z3,z56,z5,z6]),(0,[z758,z1,z7,z3,z5,z6]),(0,[z1,z525,z20,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z759]),(0,[z1,z3,z4,z5,z11,z760]),(0,[z1,z319,z3,z4,z5,z11]),(0,[z1,z7,z3,z125,z4,z761])],[(0,[z1,z7,z3,z4,z762,z6]),(0,[z1,z7,z3,z93,z293,z6]),(0,[z1,z7,z763,z4,z5,z6]),(0,[z107,z1,z7,z95,z4,z6])],[(0,[z55,z109,z3,z4,z5,z6]),(0,[z1,z7,z3,z764,z5,z6]),(0,[z1,z7,z3,z765,z4,z5]),(0,[z1,z7,z3,z4,z5,z766]),(0,[z1,z767,z3,z4,z5,z6]),(0,[z1,z7,z768,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z769]),(0,[z1,z7,z3,z770,z4,z5]),(0,[z1,z7,z3,z4,z5,z771]),(0,[z1,z7,z3,z4,z5,z772])]],
   [[(0,[z1,z2,z87,z4,z5,z6]),(0,[z1,z773,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z357]),(0,[z1,z774,z3,z4,z5,z6]),(0,[z26,z775,z7,z3,z4,z5])],[(0,[z1,z7,z3,z776,z173,z5]),(0,[z1,z7,z3,z777,z4,z5]),(0,[z1,z7,z3,z4,z5,z778])],[(0,[z204,z7,z3,z4,z5,z6]),(0,[z1,z17,z488,z3,z4,z6]),(0,[z26,z1,z7,z3,z4,z779])],[(0,[z1,z7,z3,z4,z616,z6]),(0,[z109,z223,z3,z4,z5,z6]),(0,[z7,z3,z780,z56,z5,z6]),(0,[z1,z7,z3,z4,z452,z37])],[(0,[z1,z674,z18,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z781]),(0,[z1,z7,z4,z14,z741,z6])],[(0,[z1,z7,z782,z4,z5,z6]),(0,[z26,z1,z7,z3,z543,z5]),(0,[z1,z7,z3,z152,z4,z329])],[(0,[z1,z7,z3,z4,z5,z783]),(0,[z26,z1,z7,z3,z4,z273]),(0,[z1,z7,z3,z347,z25,z6]),(0,[z1,z7,z721,z50,z4,z5]),(0,[z1,z7,z3,z4,z6,z761])],[(0,[z1,z7,z87,z270,z5,z6]),(0,[z1,z784,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z785,z6]),(0,[z1,z7,z3,z347,z5,z84]),(0,[z434,z7,z3,z4,z5,z37]),(0,[z1,z7,z3,z786,z4,z5]),(0,[z787,z7,z3,z4,z5,z6]),(0,[z234,z26,z1,z7,z3,z5]),(0,[z788,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z789,z6]),(0,[z1,z13,z163,z4,z14,z6])]],
   [[(0,[z1,z7,z3,z50,z4,z616]),(0,[z1,z7,z790,z4,z5,z6]),(0,[z1,z7,z3,z791,z5,z6]),(0,[z1,z7,z3,z173,z5,z295]),(0,[z1,z7,z557,z4,z161,z6]),(0,[z1,z7,z3,z792,z5,z6])],[(0,[z1,z7,z793,z4,z5,z6]),(0,[z1,z7,z794,z3,z4,z5]),(0,[z59,z7,z3,z4,z5,z37]),(0,[z1,z325,z4,z21,z5,z6]),(0,[z1,z40,z3,z4,z550,z6]),(0,[z107,z1,z7,z3,z589,z6]),(0,[z105,z1,z3,z4,z211,z5]),(0,[z1,z728,z3,z50,z4,z5])],[(0,[z230,z7,z727,z4,z5,z6]),(0,[z1,z38,z146,z4,z5,z6]),(0,[z1,z7,z3,z191,z4,z277])],[(0,[z120,z7,z3,z715,z5,z6]),(0,[z1,z7,z3,z4,z795,z6]),(0,[z1,z7,z3,z4,z5,z796]),(0,[z157,z1,z7,z64,z4,z5])],[(0,[z1,z7,z797,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z798]),(0,[z26,z1,z7,z3,z79,z5])],[(0,[z1,z7,z799,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z293]),(0,[z1,z425,z3,z4,z21,z6]),(0,[z1,z7,z4,z5,z800,z6]),(0,[z26,z196,z1,z7,z3,z5]),(0,[z26,z1,z7,z3,z4,z801])],[(0,[z0,z2,z259,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z802]),(0,[z1,z7,z3,z803,z4,z5]),(0,[z1,z7,z3,z804,z5,z6]),(0,[z1,z7,z3,z805,z4,z6]),(0,[z1,z806,z3,z4,z5,z6])],[(0,[z26,z1,z223,z3,z4,z5]),(0,[z7,z3,z4,z5,z111,z74]),(0,[z807,z1,z7,z3,z5,z6]),(0,[z481,z26,z1,z7,z3,z5])]],
   [[(0,[z1,z7,z3,z270,z139,z6]),(0,[z1,z7,z3,z808,z4,z5]),(0,[z1,z7,z3,z4,z809,z6]),(0,[z26,z1,z7,z3,z610,z5]),(0,[z1,z7,z3,z810,z4,z5]),(0,[z26,z1,z278,z3,z4,z5]),(0,[z26,z1,z7,z3,z5,z378]),(0,[z26,z811,z7,z3,z4,z5])],[(0,[z1,z7,z259,z4,z5,z374]),(0,[z1,z7,z3,z4,z5,z16]),(0,[z1,z7,z3,z540,z462,z6]),(0,[z1,z7,z3,z4,z5,z812]),(0,[z156,z7,z3,z56,z5,z6]),(0,[z813,z1,z7,z3,z4,z5]),(0,[z1,z17,z18,z4,z5,z6]),(0,[z82,z1,z7,z814,z5,z6])],[(0,[z1,z7,z259,z4,z616,z6]),(0,[z1,z7,z3,z815,z4,z5]),(0,[z1,z7,z3,z816,z5,z6]),(0,[z26,z1,z7,z3,z4,z452]),(0,[z1,z3,z817,z4,z5,z6]),(0,[z1,z7,z22,z3,z4,z5]),(0,[z1,z112,z325,z4,z5,z6]),(0,[z195,z7,z3,z4,z5,z169]),(0,[z1,z7,z133,z4,z5,z45])],[(0,[z1,z7,z3,z4,z5,z818]),(0,[z26,z185,z7,z3,z4,z25]),(0,[z1,z7,z3,z4,z819,z6]),(0,[z1,z38,z3,z479,z5,z6]),(0,[z1,z7,z4,z741,z161,z6]),(0,[z107,z1,z7,z3,z108,z6])],[(0,[z41,z7,z3,z4,z5,z74]),(0,[z234,z1,z7,z192,z5,z6]),(0,[z1,z7,z127,z4,z174,z6]),(0,[z1,z7,z3,z4,z5,z75]),(1,[z1,z3,z4,z726,z6]),(0,[z1,z13,z7,z50,z4,z14]),(0,[z820,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z6,z32]),(0,[z1,z7,z3,z50,z5,z32])],[(0,[z1,z821,z3,z4,z5,z6]),(0,[z107,z26,z204,z7,z3,z5]),(0,[z1,z7,z3,z5,z6,z822]),(0,[z1,z7,z3,z50,z5,z822])],[(0,[z26,z230,z7,z100,z4,z5]),(0,[z823,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z413,z4,z165]),(0,[z26,z1,z7,z3,z593,z5])],[(0,[z99,z223,z24,z4,z5,z6]),(0,[z1,z7,z3,z824,z4,z5]),(0,[z1,z7,z3,z468,z93,z5]),(0,[z26,z1,z7,z3,z375,z5]),(0,[z1,z7,z190,z265,z5,z6]),(0,[z1,z7,z3,z4,z825,z6]),(0,[z1,z7,z3,z4,z5,z826])]],
   [[(0,[z26,z1,z7,z3,z197,z5]),(0,[z48,z7,z3,z34,z5,z6]),(0,[z26,z827,z7,z3,z4,z5])],[(0,[z0,z2,z3,z50,z4,z5]),(0,[z7,z100,z471,z4,z5,z6]),(0,[z1,z7,z828,z3,z4,z6]),(0,[z26,z1,z206,z20,z4,z5])],[(0,[z1,z7,z3,z4,z5,z829]),(1,[z1,z817,z4,z5,z6])],[(0,[z99,z7,z24,z173,z5,z6]),(0,[z1,z7,z3,z4,z830,z6]),(0,[z120,z7,z3,z4,z756,z6]),(1,[z1,z3,z4,z5,z760]),(0,[z1,z3,z4,z5,z760,z6]),(0,[z107,z1,z7,z3,z217,z108])],[(0,[z1,z7,z3,z4,z5,z831]),(0,[z7,z3,z4,z780,z5,z6]),(0,[z1,z7,z3,z832,z440,z5]),(0,[z1,z7,z3,z93,z5,z74]),(0,[z1,z7,z3,z4,z833,z6]),(0,[z1,z7,z3,z209,z4,z277]),(0,[z204,z7,z3,z50,z4,z5]),(0,[z107,z1,z7,z3,z280,z6]),(0,[z1,z7,z555,z77,z4,z5])],[(0,[z1,z7,z259,z4,z5,z493]),(0,[z55,z834,z3,z4,z5,z6]),(0,[z109,z834,z3,z4,z5,z6]),(0,[z348,z7,z3,z34,z5,z6]),(0,[z43,z1,z7,z4,z5,z45])],[(0,[z1,z7,z835,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z84]),(0,[z1,z7,z836,z4,z5,z6]),(0,[z837,z1,z7,z3,z5,z6])],[(0,[z26,z1,z7,z3,z4,z456]),(0,[z1,z7,z3,z4,z5,z838]),(0,[z386,z7,z3,z5,z242,z6]),(0,[z26,z59,z7,z3,z4,z801]),(0,[z195,z7,z3,z125,z4,z5])]],
   [[(0,[z26,z1,z7,z3,z4,z616]),(0,[z1,z243,z20,z4,z5,z6]),(0,[z426,z1,z3,z106,z5,z6]),(0,[z1,z7,z3,z4,z5,z839]),(0,[z1,z7,z3,z4,z5,z840]),(0,[z1,z7,z841,z3,z4,z5]),(0,[z1,z7,z555,z4,z5,z169])],[(0,[z145,z7,z3,z4,z447,z6]),(0,[z7,z3,z4,z5,z725,z6]),(0,[z842,z1,z7,z3,z4,z5]),(0,[z1,z7,z4,z741,z5,z6])],[(0,[z26,z55,z109,z3,z4,z5]),(0,[z26,z1,z7,z3,z5,z424]),(0,[z1,z7,z3,z4,z5,z843]),(0,[z1,z7,z844,z3,z4,z5]),(0,[z1,z7,z190,z35,z5,z562]),(0,[z1,z7,z127,z4,z741,z6]),(0,[z1,z7,z3,z125,z32,z165])],[(0,[z7,z3,z4,z737,z5,z6]),(0,[z845,z7,z3,z4,z5,z6]),(0,[z26,z59,z7,z3,z5,z96])],[(0,[z1,z7,z87,z4,z5,z6]),(0,[z1,z846,z3,z4,z5,z6]),(0,[z1,z7,z3,z847,z5,z6]),(0,[z1,z3,z4,z726,z176,z6]),(0,[z1,z7,z3,z848,z4,z5]),(0,[z107,z1,z7,z3,z178,z108]),(0,[z195,z7,z3,z4,z648,z5]),(0,[z1,z7,z3,z4,z761,z165])],[(0,[z26,z1,z7,z87,z4,z5]),(0,[z1,z590,z20,z4,z5,z6]),(0,[z1,z223,z3,z173,z5,z6]),(0,[z1,z488,z7,z3,z376,z4]),(0,[z1,z7,z3,z4,z5,z849]),(0,[z1,z7,z3,z4,z5,z850]),(0,[z195,z7,z499,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z111]),(0,[z1,z7,z3,z4,z5,z851]),(0,[z1,z852,z7,z3,z4,z5]),(0,[z10,z1,z3,z4,z5,z760])],[(0,[z1,z7,z3,z4,z5,z853]),(0,[z0,z834,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z854]),(0,[z48,z7,z3,z34,z273,z6]),(0,[z26,z1,z7,z3,z5,z264]),(0,[z1,z7,z3,z4,z5,z855])]],
   [[(0,[z1,z488,z7,z3,z56,z6]),(0,[z1,z7,z3,z856,z4,z5]),(0,[z107,z26,z1,z7,z3,z5]),(0,[z1,z7,z3,z217,z159,z5])],[(0,[z1,z7,z269,z3,z191,z4])],[(0,[z1,z7,z3,z4,z857,z6]),(0,[z26,z1,z13,z7,z4,z14]),(0,[z107,z26,z1,z7,z3,z648]),(0,[z1,z7,z3,z4,z36,z131])],[(0,[z120,z7,z24,z4,z5,z6]),(0,[z26,z66,z7,z3,z56,z5]),(0,[z1,z7,z3,z4,z5,z858]),(0,[z1,z7,z3,z440,z5,z84]),(0,[z1,z278,z3,z4,z5,z6]),(0,[z1,z17,z18,z50,z4,z5]),(0,[z1,z7,z3,z4,z859,z6]),(0,[z85,z1,z3,z860,z5,z6]),(0,[z1,z7,z3,z861,z5,z6]),(0,[z1,z13,z7,z4,z9,z6])],[(0,[z26,z1,z7,z3,z4,z139]),(0,[z99,z26,z7,z24,z4,z5]),(0,[z1,z7,z3,z125,z4,z134]),(0,[z1,z7,z3,z4,z5,z862]),(0,[z1,z40,z325,z4,z21,z6]),(0,[z1,z7,z863,z3,z4,z5])],[(0,[z1,z7,z3,z4,z864,z6]),(0,[z99,z7,z24,z4,z5,z6]),(0,[z553,z1,z3,z4,z5,z11]),(0,[z26,z1,z7,z95,z4,z5]),(0,[z1,z865,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z5,z822])],[(0,[z0,z2,z3,z4,z5,z374]),(0,[z47,z7,z3,z93,z5,z37]),(0,[z1,z7,z866,z4,z5,z6]),(0,[z1,z112,z3,z4,z726,z6]),(0,[z1,z208,z499,z3,z4,z5]),(0,[z820,z7,z3,z50,z4,z5])],[(0,[z1,z7,z3,z867,z5,z6]),(0,[z1,z7,z3,z4,z5,z868]),(0,[z120,z7,z100,z4,z5,z6]),(0,[z1,z7,z3,z869,z4,z5]),(0,[z1,z7,z3,z4,z6,z870]),(0,[z1,z7,z3,z5,z6,z871]),(0,[z1,z7,z3,z4,z5,z800])]],
   [[(0,[z1,z7,z3,z4,z462,z16]),(0,[z1,z872,z3,z4,z5,z6]),(0,[z195,z7,z3,z159,z5,z6])],[(0,[z1,z7,z259,z98,z5,z6]),(0,[z1,z7,z3,z50,z4,z273]),(0,[z1,z7,z3,z93,z452,z6]),(0,[z1,z7,z3,z4,z36,z761])],[(0,[z873,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z616,z374]),(0,[z1,z7,z3,z4,z5,z874]),(0,[z26,z195,z7,z3,z56,z5]),(0,[z875,z1,z7,z3,z4,z5])],[(0,[z1,z130,z18,z4,z5,z6]),(0,[z26,z1,z112,z3,z4,z176]),(0,[z26,z1,z7,z3,z5,z876])],[(1,[z7,z727,z4,z5,z6]),(0,[z340,z1,z7,z192,z5,z6]),(0,[z1,z7,z3,z4,z5,z877]),(0,[z82,z1,z7,z50,z192,z5]),(0,[z1,z7,z878,z4,z5,z6]),(0,[z546,z1,z7,z3,z4,z54])],[(0,[z363,z7,z3,z4,z25,z6]),(0,[z1,z7,z3,z4,z150,z149]),(0,[z1,z7,z3,z4,z5,z158]),(0,[z1,z3,z860,z106,z5,z6]),(0,[z1,z7,z3,z4,z879,z5]),(0,[z1,z7,z3,z81,z159,z6]),(0,[z196,z1,z7,z3,z5,z6])],[(0,[z1,z7,z3,z347,z5,z6]),(0,[z1,z7,z146,z4,z5,z6]),(0,[z880,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z695,z5]),(0,[z1,z7,z3,z4,z881,z6]),(0,[z26,z1,z7,z3,z5,z647]),(0,[z59,z195,z7,z3,z4,z5])],[(0,[z1,z223,z3,z4,z5,z6]),(0,[z26,z7,z3,z56,z5,z74]),(0,[z411,z7,z3,z56,z5,z6]),(0,[z1,z7,z3,z882,z5,z6]),(0,[z1,z7,z3,z4,z6,z883]),(0,[z1,z13,z7,z4,z741,z6]),(0,[z26,z1,z7,z884,z4,z5])]],
   [[(0,[z1,z7,z3,z885,z5,z6]),(0,[z1,z7,z3,z50,z4,z293]),(0,[z1,z7,z3,z4,z886,z5]),(0,[z887,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z349,z5]),(0,[z1,z7,z3,z4,z5,z761])],[(0,[z888,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z56,z447,z6]),(0,[z1,z7,z269,z3,z56,z6]),(0,[z420,z195,z7,z3,z4,z5])],[(0,[z99,z320,z24,z4,z5,z6]),(0,[z1,z889,z3,z4,z5,z6]),(0,[z1,z7,z890,z4,z5,z6]),(0,[z107,z26,z195,z7,z3,z5])],[(0,[z1,z7,z3,z173,z5,z6]),(0,[z888,z1,z7,z3,z540,z5]),(0,[z26,z1,z7,z3,z56,z5]),(0,[z1,z206,z20,z4,z5,z6]),(0,[z1,z7,z3,z891,z4,z6]),(0,[z1,z892,z3,z4,z5,z6]),(0,[z893,z7,z3,z4,z5,z6])],[(0,[z1,z7,z259,z4,z139,z6]),(0,[z59,z7,z3,z4,z5,z111]),(0,[z1,z894,z7,z3,z4,z5]),(0,[z204,z7,z3,z4,z5,z895])],[(0,[z99,z7,z24,z4,z5,z295]),(0,[z1,z17,z466,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z896]),(0,[z1,z897,z3,z4,z5,z6]),(0,[z26,z1,z898,z3,z4,z5])],[(0,[z1,z7,z87,z50,z4,z5]),(0,[z1,z7,z3,z4,z899,z6]),(0,[z1,z7,z508,z35,z5,z6]),(0,[z900,z1,z7,z3,z4,z5]),(0,[z26,z1,z7,z3,z4,z859]),(1,[z1,z7,z3,z5,z822])],[]],
   [[(0,[z1,z7,z3,z34,z447,z6]),(0,[z7,z3,z34,z780,z5,z6]),(0,[z73,z7,z3,z4,z5,z74]),(0,[z1,z7,z3,z376,z4,z5]),(0,[z1,z7,z3,z901,z4,z5])],[(0,[z1,z7,z3,z4,z902,z6]),(0,[z26,z1,z163,z3,z4,z5]),(0,[z195,z7,z3,z64,z4,z5]),(0,[z26,z59,z7,z3,z4,z903])],[(0,[z1,z7,z3,z384,z159,z6]),(0,[z1,z7,z3,z56,z5,z381]),(0,[z107,z26,z1,z7,z3,z25]),(0,[z1,z7,z3,z904,z4,z5]),(0,[z26,z1,z7,z325,z4,z5]),(0,[z26,z1,z7,z905,z4,z5]),(0,[z1,z7,z3,z4,z131,z761])],[(0,[z1,z7,z3,z906,z5,z6]),(0,[z1,z7,z3,z4,z5,z907]),(0,[z1,z7,z3,z780,z5,z6]),(0,[z1,z245,z7,z4,z14,z6]),(0,[z665,z1,z7,z3,z50,z5])],[(0,[z120,z7,z87,z4,z5,z6]),(0,[z1,z7,z3,z81,z342,z6]),(0,[z234,z1,z3,z106,z5,z6]),(0,[z732,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z908,z5,z6])],[(0,[z1,z7,z3,z909,z4,z5]),(0,[z1,z7,z3,z4,z5,z910]),(0,[z1,z7,z3,z4,z911,z6]),(0,[z1,z7,z3,z209,z4,z5]),(0,[z1,z13,z7,z4,z14,z6]),(0,[z1,z278,z3,z50,z4,z5])],[(0,[z99,z7,z87,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z912]),(0,[z1,z7,z3,z4,z913,z5]),(0,[z914,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z201,z131])],[(0,[z1,z223,z3,z4,z5,z295]),(0,[z99,z7,z24,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z178]),(0,[z420,z1,z7,z133,z4,z5])]],
   [[(0,[z1,z71,z20,z4,z5,z6]),(0,[z1,z320,z3,z173,z5,z6]),(0,[z1,z7,z3,z215,z5,z6]),(0,[z85,z26,z1,z3,z106,z5]),(0,[z1,z7,z3,z4,z5,z915]),(0,[z1,z7,z3,z217,z4,z5]),(0,[z26,z1,z7,z3,z474,z5])],[(0,[z1,z7,z3,z916,z270,z5]),(0,[z917,z1,z7,z3,z4,z5]),(0,[z120,z2,z3,z4,z5,z6]),(0,[z518,z7,z3,z56,z5,z6]),(0,[z48,z7,z3,z4,z5,z84]),(0,[z1,z7,z3,z34,z5,z381]),(0,[z1,z7,z3,z4,z415,z131]),(0,[z26,z1,z7,z836,z4,z5])],[(0,[z1,z7,z3,z50,z4,z456]),(0,[z1,z7,z127,z50,z4,z161])],[(0,[z918,z1,z7,z3,z4,z5]),(0,[z1,z40,z3,z4,z726,z6]),(0,[z26,z195,z7,z3,z5,z96]),(0,[z1,z7,z3,z4,z329,z165])],[(0,[z1,z109,z87,z4,z5,z6]),(0,[z230,z7,z100,z4,z5,z6]),(0,[z48,z7,z3,z93,z5,z6]),(0,[z120,z7,z3,z4,z5,z862]),(0,[z1,z7,z127,z4,z161,z128])],[(0,[z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z56,z5,z84]),(0,[z285,z7,z3,z4,z5,z74]),(0,[z26,z59,z7,z3,z56,z5]),(0,[z1,z7,z3,z291,z215,z5])],[(0,[z1,z919,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z563,z5]),(0,[z1,z7,z269,z20,z4,z6]),(0,[z1,z18,z817,z4,z5,z6]),(0,[z1,z920,z7,z3,z4,z5]),(0,[z1,z7,z127,z696,z4,z6]),(0,[z26,z59,z7,z3,z4,z5])],[(0,[z26,z1,z7,z3,z691,z5]),(0,[z1,z3,z4,z21,z726,z6])]],
   [[(0,[z1,z7,z3,z4,z921,z6]),(0,[z1,z7,z3,z922,z5,z6]),(0,[z1,z7,z3,z4,z923,z6]),(0,[z1,z7,z3,z191,z34,z5]),(0,[z26,z1,z7,z3,z154,z5]),(0,[z1,z7,z924,z3,z4,z5]),(0,[z1,z7,z146,z50,z4,z5]),(0,[z601,z195,z7,z3,z4,z5]),(0,[z26,z1,z925,z3,z4,z5]),(0,[z635,z7,z3,z468,z4,z5])],[(0,[z1,z7,z3,z98,z5,z374]),(0,[z1,z834,z3,z4,z5,z6]),(0,[z7,z834,z3,z4,z5,z6]),(0,[z1,z223,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z926]),(0,[z85,z1,z488,z3,z106,z6]),(0,[z1,z7,z127,z4,z161,z6]),(0,[z26,z386,z7,z3,z5,z6]),(0,[z107,z26,z1,z7,z3,z280]),(0,[z1,z7,z3,z50,z81,z159])],[(0,[z26,z1,z7,z3,z98,z5]),(0,[z1,z7,z3,z927,z5,z6]),(0,[z1,z7,z3,z4,z456,z16]),(0,[z66,z7,z3,z291,z56,z5]),(0,[z1,z928,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z215,z5]),(0,[z26,z1,z488,z7,z3,z4]),(1,[z26,z386,z7,z3,z5]),(0,[z107,z26,z1,z7,z3,z159])],[(0,[z1,z7,z3,z50,z270,z5]),(0,[z1,z7,z3,z4,z929,z6]),(0,[z1,z7,z3,z4,z930,z6]),(0,[z26,z363,z1,z7,z3,z5]),(0,[z107,z26,z1,z112,z7,z3]),(0,[z1,z7,z3,z4,z741,z6])],[(0,[z1,z7,z3,z931,z4,z5]),(0,[z195,z7,z3,z4,z36,z5]),(0,[z26,z1,z7,z3,z5,z96])],[(0,[z204,z7,z3,z4,z447,z6]),(1,[z7,z3,z4,z5,z725]),(0,[z47,z7,z3,z215,z5,z37]),(0,[z1,z206,z20,z50,z4,z5]),(0,[z1,z7,z3,z50,z324,z5]),(0,[z1,z7,z3,z50,z331,z5]),(0,[z1,z7,z3,z4,z5,z932])],[(0,[z326,z7,z3,z56,z5,z6]),(0,[z26,z1,z7,z3,z4,z277]),(0,[z1,z7,z3,z4,z5,z933]),(1,[z1,z7,z3,z934,z6])],[(0,[z1,z7,z3,z50,z4,z139]),(0,[z120,z223,z3,z4,z5,z6]),(0,[z66,z7,z3,z50,z56,z5]),(0,[z26,z7,z3,z56,z5,z25]),(0,[z26,z1,z7,z3,z935,z5]),(1,[z1,z7,z814,z5,z6]),(0,[z107,z1,z7,z3,z217,z5]),(0,[z1,z7,z3,z5,z242,z378])]],
   [[(0,[z1,z7,z3,z936,z5,z6]),(0,[z204,z7,z3,z56,z5,z6]),(0,[z1,z7,z3,z215,z452,z6]),(0,[z1,z7,z3,z4,z937,z6]),(0,[z1,z7,z3,z938,z4,z6]),(0,[z1,z7,z3,z4,z6,z939])],[(0,[z1,z7,z3,z940,z5,z6]),(0,[z1,z941,z3,z4,z5,z6]),(0,[z7,z3,z727,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z942]),(0,[z1,z7,z3,z943,z5,z6]),(0,[z196,z1,z7,z3,z5,z11]),(0,[z26,z944,z7,z3,z4,z5])],[(0,[z1,z320,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z945,z6]),(0,[z1,z7,z3,z173,z462,z6]),(0,[z26,z7,z3,z34,z56,z5]),(0,[z195,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z440,z5,z6]),(0,[z1,z7,z3,z4,z946,z6]),(0,[z47,z7,z3,z4,z5,z37]),(0,[z1,z488,z7,z22,z3,z4]),(0,[z1,z7,z3,z4,z5,z947])],[(0,[z55,z109,z3,z50,z4,z5]),(0,[z7,z3,z4,z447,z25,z6]),(0,[z1,z7,z3,z4,z5,z948]),(0,[z26,z1,z7,z3,z93,z5]),(0,[z1,z7,z3,z949,z5,z6]),(0,[z120,z206,z20,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z950]),(0,[z26,z1,z40,z3,z4,z21]),(0,[z1,z7,z3,z4,z277,z6]),(0,[z951,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z952,z5,z6]),(0,[z1,z7,z3,z125,z4,z165])],[(0,[z1,z7,z3,z4,z139,z374]),(0,[z630,z7,z3,z34,z5,z6])],[(0,[z1,z7,z3,z916,z4,z5]),(0,[z1,z7,z3,z4,z5,z295]),(0,[z26,z1,z7,z3,z371,z5]),(0,[z1,z7,z3,z4,z452,z6]),(0,[z953,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z954]),(0,[z1,z7,z3,z955,z5,z6]),(0,[z26,z956,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z957,z6]),(0,[z1,z7,z3,z4,z5,z67]),(0,[z59,z7,z3,z4,z5,z74]),(0,[z1,z7,z3,z50,z700,z5])],[(0,[z26,z1,z7,z3,z173,z5]),(0,[z1,z7,z3,z4,z958,z6]),(0,[z47,z285,z7,z3,z4,z5]),(0,[z204,z7,z3,z34,z5,z6]),(0,[z1,z3,z4,z5,z6,z959]),(0,[z7,z3,z4,z5,z725,z74]),(0,[z116,z1,z20,z4,z5,z6]),(0,[z26,z1,z7,z3,z159,z5])]],
   [[],[(0,[z873,z1,z7,z3,z270,z5]),(0,[z48,z7,z3,z347,z5,z6])],[(0,[z834,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z960,z6]),(0,[z1,z7,z961,z4,z5,z6]),(0,[z1,z7,z3,z291,z4,z5]),(0,[z1,z390,z3,z4,z176,z6]),(0,[z1,z7,z3,z962,z4,z5]),(0,[z1,z7,z612,z4,z5,z169]),(0,[z107,z26,z59,z7,z3,z5])],[(0,[z1,z963,z7,z3,z4,z6]),(0,[z59,z7,z3,z4,z5,z6]),(0,[z813,z1,z7,z3,z440,z5]),(0,[z206,z117,z20,z4,z5,z6]),(0,[z1,z40,z95,z4,z21,z6]),(0,[z78,z1,z7,z3,z50,z5])],[(0,[z1,z7,z964,z4,z5,z6]),(0,[z1,z7,z3,z965,z5,z6]),(0,[z966,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z81,z159,z378]),(0,[z224,z59,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z967]),(0,[z107,z1,z7,z3,z354,z6]),(0,[z1,z7,z3,z4,z5,z968]),(1,[z1,z3,z860,z5,z6]),(0,[z1,z38,z3,z39,z5,z75]),(0,[z1,z7,z3,z50,z5,z286])],[(0,[z1,z7,z3,z4,z969,z6]),(0,[z1,z7,z3,z4,z970,z6]),(0,[z230,z7,z100,z50,z4,z5]),(0,[z7,z3,z93,z56,z5,z6]),(0,[z7,z3,z4,z5,z971,z6]),(0,[z1,z90,z190,z4,z5,z6]),(0,[z107,z195,z7,z3,z5,z6]),(0,[z1,z7,z972,z4,z5,z6])],[(0,[z1,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z973]),(0,[z1,z7,z3,z215,z293,z6]),(0,[z1,z7,z3,z4,z974,z6]),(0,[z26,z1,z7,z3,z148,z5]),(0,[z1,z31,z3,z551,z4,z5])]],
   [[(0,[z1,z7,z3,z4,z139,z493]),(0,[z1,z7,z3,z5,z6,z975]),(0,[z1,z7,z3,z4,z5,z976]),(0,[z1,z7,z3,z4,z5,z977]),(0,[z978,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z341,z5])],[(0,[z1,z7,z979,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z980]),(0,[z1,z7,z3,z981,z4,z5]),(0,[z26,z1,z7,z3,z81,z159]),(0,[z228,z195,z7,z3,z4,z5]),(0,[z196,z982,z7,z3,z5,z6])],[(0,[z1,z320,z3,z4,z5,z295]),(0,[z1,z7,z3,z4,z983,z6]),(0,[z1,z7,z3,z4,z5,z984]),(0,[z632,z7,z3,z4,z25,z6]),(0,[z26,z1,z7,z3,z215,z5]),(0,[z47,z7,z3,z4,z452,z37]),(0,[z1,z7,z3,z4,z985,z5]),(0,[z546,z196,z1,z7,z3,z5])],[(0,[z26,z1,z7,z3,z270,z5]),(0,[z1,z7,z986,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z462]),(0,[z48,z7,z3,z34,z447,z6]),(0,[z1,z140,z20,z4,z5,z6]),(0,[z1,z7,z190,z814,z5,z6])],[(0,[z1,z7,z3,z987,z4,z5]),(0,[z1,z7,z3,z4,z293,z6]),(0,[z1,z7,z3,z713,z347,z5]),(0,[z1,z488,z7,z3,z4,z6]),(0,[z742,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z4,z988]),(0,[z26,z1,z774,z3,z4,z5]),(0,[z453,z1,z7,z4,z61,z5])],[(0,[z120,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z273,z67]),(0,[z107,z26,z1,z40,z7,z3]),(0,[z1,z7,z190,z50,z35,z5]),(0,[z373,z195,z7,z3,z4,z5]),(0,[z26,z59,z7,z3,z93,z5]),(0,[z26,z1,z7,z3,z4,z974])],[(0,[z99,z7,z24,z4,z456,z6]),(0,[z48,z7,z3,z780,z5,z6]),(0,[z1,z7,z3,z989,z5,z6])],[(0,[z1,z990,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z991,z6]),(0,[z1,z7,z3,z992,z5,z6]),(0,[z185,z7,z3,z4,z737,z6]),(0,[z7,z3,z4,z993,z5,z6])]],
   [[(0,[z702,z7,z3,z4,z25,z6]),(0,[z1,z20,z4,z80,z5,z6]),(0,[z994,z7,z3,z4,z5,z6]),(0,[z1,z7,z814,z192,z5,z6]),(0,[z26,z1,z7,z127,z4,z161]),(0,[z26,z1,z7,z3,z103,z5]),(0,[z26,z995,z7,z3,z4,z5]),(0,[z196,z1,z7,z3,z125,z5])],[(0,[z1,z7,z3,z996,z5,z6]),(0,[z1,z7,z3,z4,z997,z6]),(0,[z1,z7,z3,z4,z5,z998]),(0,[z204,z7,z3,z4,z5,z772]),(0,[z26,z59,z7,z3,z159,z5])],[(0,[z0,z2,z3,z4,z616,z6]),(0,[z1,z7,z3,z999,z4,z5]),(0,[z1,z7,z3,z1000,z5,z6]),(0,[z1,z7,z22,z3,z34,z5]),(0,[z1,z7,z1001,z4,z5,z6]),(0,[z26,z1,z7,z3,z5,z579]),(0,[z1,z7,z3,z814,z5,z6]),(0,[z26,z1,z7,z3,z4,z903]),(0,[z196,z1,z7,z3,z36,z5])],[(0,[z1,z7,z3,z270,z5,z6]),(0,[z1,z7,z3,z540,z5,z16])],[(0,[z1,z7,z3,z4,z1002,z6]),(0,[z1,z320,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z1003,z6]),(0,[z1,z112,z3,z4,z176,z6]),(0,[z1,z3,z4,z5,z760,z51]),(0,[z10,z1,z3,z4,z211,z5]),(0,[z195,z7,z3,z50,z4,z5]),(0,[z26,z893,z7,z3,z4,z5]),(0,[z1,z7,z3,z5,z242,z822])],[(0,[z1,z425,z7,z4,z14,z6]),(0,[z944,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z159,z5,z876]),(0,[z982,z7,z3,z4,z5,z6])],[(0,[z1,z1004,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z30]),(0,[z26,z195,z7,z3,z4,z5])],[(0,[z513,z109,z3,z4,z5,z6]),(0,[z66,z7,z3,z780,z5,z6]),(0,[z26,z1,z7,z3,z468,z5]),(0,[z1,z7,z1005,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z1006,z6]),(0,[z1,z223,z3,z4,z456,z6]),(0,[z1,z7,z3,z4,z273,z111]),(0,[z1,z7,z3,z4,z5,z1007]),(0,[z1,z7,z3,z1008,z5,z6]),(0,[z1,z7,z3,z1009,z5,z6])],[(0,[z109,z100,z20,z4,z5,z6]),(0,[z1,z7,z3,z4,z447,z111]),(0,[z1,z7,z3,z5,z6,z1010]),(0,[z47,z7,z3,z4,z293,z37]),(0,[z1,z7,z269,z3,z209,z4])],[(0,[z120,z26,z7,z3,z4,z5]),(0,[z1,z7,z3,z1011,z4,z5]),(0,[z1,z112,z3,z4,z541,z6]),(0,[z1,z488,z7,z3,z50,z4]),(0,[z82,z1,z7,z191,z192,z5]),(1,[z1,z7,z3,z4,z761])],[(0,[z281,z1,z7,z4,z5,z45])],[(0,[z1,z7,z3,z98,z139,z6]),(0,[z1,z7,z3,z173,z456,z6]),(0,[z1,z7,z3,z4,z462,z295]),(0,[z7,z100,z727,z4,z5,z6]),(0,[z1,z7,z3,z56,z5,z111]),(0,[z1,z163,z4,z14,z5,z6]),(0,[z26,z1,z7,z3,z544,z5]),(0,[z1,z7,z3,z1012,z5,z6]),(0,[z1,z7,z3,z4,z5,z378])],[(0,[z1,z7,z3,z4,z1013,z6]),(0,[z1,z7,z3,z50,z98,z5]),(0,[z1,z7,z3,z1014,z5,z6]),(0,[z0,z2,z3,z4,z5,z493]),(0,[z1015,z1,z7,z3,z4,z5]),(0,[z1,z7,z269,z3,z4,z6]),(0,[z26,z1,z7,z3,z5,z484]),(0,[z59,z7,z3,z50,z4,z5])],[(0,[z1,z7,z3,z1016,z4,z5]),(0,[z1,z7,z3,z1017,z4,z5]),(0,[z1,z7,z3,z4,z357,z6]),(0,[z195,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z1018]),(0,[z775,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z125,z4,z280])],[(0,[z26,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z988,z6]),(0,[z1,z898,z3,z4,z5,z6])]],
   [[(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1,z7,z1020,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1021]),(0,[z1,z7,z3,z4,z616,z493]),(0,[z1,z7,z1022,z4,z5,z6]),(0,[z26,z1,z7,z3,z540,z5]),(0,[z1,z7,z3,z1023,z5,z6]),(0,[z26,z1,z7,z3,z651,z5]),(0,[z1,z7,z3,z50,z4,z277])],[(0,[z393,z7,z100,z4,z5,z6]),(0,[z7,z3,z4,z1024,z5,z6]),(0,[z26,z1,z38,z3,z39,z5]),(0,[z1,z7,z4,z5,z800,z169]),(0,[z978,z7,z3,z50,z4,z5])],[(0,[z107,z285,z1,z7,z3,z5]),(0,[z1,z7,z3,z34,z5,z111]),(0,[z1,z7,z127,z4,z161,z289]),(0,[z26,z1,z7,z1025,z4,z5]),(0,[z1,z7,z3,z4,z903,z6])],[(0,[z1,z7,z3,z93,z5,z37]),(0,[z1,z7,z175,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1026]),(0,[z195,z7,z3,z4,z5,z45])],[(0,[z1,z7,z3,z1027,z4,z6])],[(0,[z1,z7,z3,z1028,z4,z5]),(0,[z26,z1,z7,z3,z291,z5]),(0,[z1,z160,z3,z39,z5,z6]),(0,[z1029,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z50,z93,z5]),(0,[z1,z7,z817,z4,z5,z6]),(0,[z1,z38,z3,z39,z5,z158]),(0,[z377,z1,z7,z3,z50,z5]),(0,[z1,z1030,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1031]),(0,[z1,z7,z3,z4,z1032,z6]),(0,[z386,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1033]),(0,[z47,z195,z7,z3,z4,z5]),(0,[z120,z7,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z895]),(0,[z1,z7,z3,z159,z934,z6]),(0,[z460,z1,z499,z3,z4,z5])]],
   [[(0,[z1,z163,z3,z4,z5,z6]),(0,[z1,z7,z3,z1034,z4,z5])],[(0,[z1,z7,z3,z1035,z5,z6]),(0,[z107,z1,z7,z3,z263,z6]),(0,[z1,z7,z884,z4,z5,z6]),(0,[z189,z7,z3,z4,z593,z5])],[(0,[z1,z7,z3,z50,z173,z5]),(0,[z1,z7,z3,z4,z5,z1036]),(0,[z26,z1,z7,z3,z5,z668]),(0,[z1,z865,z3,z50,z4,z5])],[(0,[z1,z7,z1037,z4,z5,z6]),(0,[z1,z7,z3,z1038,z4,z5]),(0,[z1,z7,z3,z4,z5,z1039]),(0,[z1,z7,z3,z4,z5,z1040]),(0,[z1,z7,z3,z1041,z4,z5]),(0,[z1,z7,z269,z3,z50,z4]),(0,[z1,z7,z3,z4,z5,z128])],[(0,[z1,z7,z3,z4,z1042,z6]),(0,[z1,z7,z3,z4,z5,z1043]),(0,[z1,z7,z3,z4,z5,z1044]),(0,[z1,z7,z3,z50,z642,z5])],[(0,[z1,z7,z3,z1045,z4,z5]),(0,[z1,z7,z3,z4,z1046,z6]),(0,[z47,z7,z3,z4,z5,z111]),(0,[z1,z1047,z3,z4,z5,z6]),(0,[z1048,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z146,z4,z5])],[(0,[z1,z7,z3,z4,z456,z6]),(0,[z26,z1,z320,z3,z4,z5]),(0,[z1,z7,z4,z5,z1049,z6]),(0,[z26,z1,z7,z3,z440,z5]),(0,[z1,z7,z3,z4,z5,z1050])],[(0,[z1,z7,z3,z4,z5,z1051]),(0,[z1,z7,z3,z4,z5,z1052]),(0,[z99,z7,z24,z4,z462,z6]),(0,[z204,z7,z3,z4,z25,z6]),(0,[z1053,z7,z3,z4,z5,z6]),(0,[z107,z204,z7,z3,z108,z6])]],
   [[],[(0,[z1,z7,z3,z1054,z5,z6]),(0,[z26,z1,z7,z259,z4,z5]),(0,[z0,z2,z3,z98,z5,z6]),(0,[z7,z727,z24,z4,z5,z6]),(0,[z1,z7,z3,z4,z737,z6]),(0,[z1,z7,z3,z4,z25,z149]),(0,[z1,z7,z3,z81,z159,z381])],[(0,[z1,z112,z3,z50,z4,z176]),(0,[z1,z1055,z3,z4,z5,z6]),(0,[z43,z1,z7,z4,z5,z800]),(0,[z26,z195,z7,z3,z50,z5])],[(0,[z0,z2,z87,z4,z5,z6]),(0,[z1,z7,z3,z4,z1056,z6]),(0,[z1,z7,z22,z3,z4,z357]),(0,[z1,z1057,z7,z3,z4,z5]),(0,[z1,z1058,z3,z4,z5,z6]),(0,[z29,z1,z7,z3,z4,z648])],[(0,[z1,z7,z3,z1016,z98,z5]),(0,[z1,z7,z3,z125,z4,z422])],[(0,[z1,z7,z3,z98,z616,z6]),(0,[z120,z109,z3,z4,z5,z6]),(0,[z107,z1,z7,z3,z478,z6])],[(0,[z1,z7,z87,z4,z5,z374]),(0,[z1,z7,z3,z50,z4,z462]),(0,[z137,z7,z3,z4,z150,z6]),(0,[z26,z1,z7,z269,z3,z4]),(0,[z26,z1,z7,z3,z329,z5])],[(0,[z1,z7,z87,z4,z616,z6]),(0,[z1059,z1,z7,z3,z4,z5]),(0,[z145,z26,z7,z3,z56,z5]),(0,[z48,z7,z3,z4,z293,z6]),(0,[z85,z1,z146,z106,z5,z6]),(0,[z1,z7,z3,z1060,z4,z5]),(0,[z1,z7,z3,z4,z5,z1061]),(0,[z1,z1062,z3,z4,z5,z6])]],
   [[(0,[z47,z7,z3,z4,z5,z725]),(0,[z1,z7,z3,z4,z1063,z6])],[(0,[z1,z223,z3,z540,z5,z6]),(0,[z1,z223,z3,z4,z462,z6]),(0,[z1,z7,z3,z4,z5,z1064]),(0,[z82,z26,z1,z7,z192,z5]),(0,[z26,z195,z7,z3,z159,z5]),(0,[z59,z7,z3,z4,z903,z6]),(0,[z1,z7,z3,z4,z5,z822])],[(0,[z26,z1,z7,z3,z260,z5]),(0,[z107,z7,z3,z56,z25,z6]),(0,[z368,z26,z1,z7,z3,z5]),(0,[z1,z7,z4,z5,z6,z1065]),(0,[z7,z3,z4,z1066,z5,z6]),(0,[z1,z163,z127,z4,z5,z6])],[(0,[z1,z320,z3,z4,z456,z6]),(0,[z7,z3,z4,z56,z293,z6]),(0,[z1,z7,z3,z4,z5,z1067]),(0,[z1,z7,z3,z4,z452,z74]),(0,[z1068,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z3,z50,z5])],[(0,[z0,z2,z3,z4,z139,z6]),(0,[z1,z7,z3,z4,z5,z1069]),(0,[z1,z7,z3,z934,z108,z6])],[(0,[z85,z1,z22,z3,z106,z5]),(0,[z107,z1,z278,z3,z4,z6]),(0,[z601,z1,z319,z3,z4,z5])],[(0,[z1,z7,z3,z4,z456,z295]),(0,[z1,z613,z20,z4,z5,z6]),(0,[z1,z38,z3,z39,z5,z6]),(0,[z1,z7,z175,z50,z4,z5])],[(0,[z1,z7,z259,z4,z5,z6]),(0,[z1,z7,z3,z4,z273,z6]),(0,[z1,z7,z3,z4,z5,z1070]),(0,[z1,z7,z3,z4,z5,z876])]],
   [[(0,[z1,z7,z3,z98,z5,z493]),(0,[z1,z7,z1071,z4,z5,z6]),(0,[z1,z1072,z3,z4,z5,z6]),(0,[z635,z7,z3,z4,z5,z74]),(0,[z1,z7,z3,z4,z1073,z6]),(0,[z1,z7,z3,z1074,z4,z5])],[(0,[z1,z598,z20,z4,z5,z6]),(0,[z1,z7,z18,z269,z4,z6]),(0,[z386,z7,z3,z50,z4,z5]),(0,[z1,z1075,z3,z4,z5,z6])],[(0,[z1,z7,z87,z4,z5,z493]),(0,[z185,z7,z3,z50,z4,z25]),(0,[z1,z7,z190,z35,z5,z6]),(0,[z1,z163,z3,z50,z4,z5]),(0,[z196,z1,z7,z3,z5,z45]),(0,[z1,z7,z3,z5,z934,z6]),(0,[z26,z1076,z7,z3,z4,z5])],[(0,[z73,z7,z3,z4,z5,z725]),(0,[z1,z7,z1077,z4,z5,z6]),(0,[z1,z7,z95,z81,z4,z6]),(0,[z1,z7,z3,z4,z801,z6])],[(0,[z1,z7,z3,z4,z1078,z6]),(0,[z1,z7,z3,z1079,z5,z6]),(0,[z1,z7,z3,z4,z5,z1080]),(0,[z1081,z1,z7,z3,z5,z6]),(0,[z82,z1,z7,z277,z192,z6])],[(0,[z1,z7,z3,z4,z5,z1082]),(0,[z66,z285,z7,z3,z56,z5]),(0,[z335,z7,z3,z4,z5,z74]),(0,[z1,z38,z3,z860,z5,z6])],[(0,[z1,z7,z457,z4,z5,z169]),(0,[z1083,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z50,z4,z923])],[(0,[z0,z26,z2,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z1084]),(0,[z1,z1085,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1086,z6]),(0,[z1,z7,z325,z4,z5,z6]),(0,[z1,z7,z3,z5,z1087,z6]),(0,[z588,z26,z1,z7,z3,z5]),(0,[z1,z7,z3,z4,z5,z1088])]],
   [[(0,[z1,z7,z3,z4,z5,z1089])],[(0,[z107,z1,z7,z3,z355,z6]),(0,[z827,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z381]),(0,[z107,z26,z1,z7,z3,z108])],[(1,[z7,z3,z780,z5,z6]),(0,[z1,z7,z3,z347,z150,z6]),(0,[z1,z7,z3,z347,z5,z149]),(0,[z107,z26,z1,z7,z3,z150]),(0,[z1,z3,z4,z860,z5,z6]),(0,[z1,z7,z1090,z4,z5,z6]),(0,[z107,z1,z7,z3,z50,z108])],[(0,[z1,z7,z3,z4,z1091,z6]),(0,[z1,z7,z1092,z4,z5,z6]),(0,[z1,z166,z18,z4,z5,z6])],[(0,[z1,z7,z3,z50,z540,z5]),(0,[z1,z7,z3,z191,z56,z5]),(0,[z1,z7,z3,z4,z5,z1093]),(0,[z107,z1,z7,z3,z407,z6]),(0,[z1,z7,z3,z50,z5,z76]),(0,[z1,z486,z3,z4,z5,z51])],[(0,[z1,z1094,z3,z4,z5,z6]),(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1096]),(0,[z26,z59,z7,z3,z50,z5])],[(0,[z1,z3,z4,z1097,z5,z6]),(0,[z1,z7,z3,z4,z5,z1098]),(0,[z1,z7,z3,z1099,z4,z5]),(0,[z26,z59,z7,z3,z34,z5]),(0,[z85,z1,z3,z106,z5,z6])],[(0,[z1,z7,z3,z540,z5,z6]),(0,[z1,z7,z3,z4,z462,z6]),(0,[z1,z1100,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z6,z1101]),(0,[z1,z7,z3,z1102,z4,z5])]],
   [[(0,[z1,z7,z3,z1103,z5,z6]),(0,[z1,z90,z3,z4,z5,z6]),(0,[z43,z1,z7,z4,z61,z5]),(0,[z26,z1,z7,z3,z5,z597])],[(0,[z1,z7,z1104,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1105]),(0,[z1,z7,z3,z4,z447,z67]),(0,[z26,z1,z7,z3,z342,z5]),(0,[z1106,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z113]),(0,[z1,z7,z3,z4,z934,z6]),(0,[z26,z195,z7,z3,z468,z5])],[(0,[z1,z7,z3,z4,z1107,z6]),(0,[z706,z7,z3,z56,z5,z6]),(0,[z1,z7,z3,z4,z5,z1108]),(0,[z1,z7,z3,z662,z4,z165]),(0,[z1,z7,z3,z4,z5,z1109])],[(0,[z1,z7,z1110,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1111]),(0,[z7,z3,z347,z56,z5,z6]),(0,[z1,z7,z3,z1112,z5,z6]),(0,[z1,z7,z3,z50,z5,z275]),(0,[z1,z410,z3,z4,z5,z6]),(0,[z1,z7,z1113,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1114]),(0,[z195,z7,z3,z4,z5,z51])],[(0,[z1,z1115,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1116,z6])],[(0,[z1,z7,z3,z4,z5,z1117]),(0,[z97,z7,z3,z4,z5,z74]),(0,[z1,z3,z39,z860,z5,z6]),(0,[z1,z7,z3,z4,z5,z1118]),(0,[z82,z1,z7,z192,z5,z6]),(0,[z26,z788,z7,z3,z4,z5]),(0,[z26,z1,z806,z3,z4,z5])],[(0,[z1,z7,z87,z98,z5,z6]),(0,[z1,z7,z3,z4,z5,z1119]),(0,[z1,z7,z3,z4,z5,z132]),(0,[z26,z1,z410,z3,z4,z5])],[(0,[z1,z7,z3,z999,z540,z5]),(0,[z1,z7,z3,z4,z648,z131])]],
   [[(1,[z834,z3,z4,z5,z6]),(0,[z7,z3,z117,z4,z5,z6]),(0,[z1,z223,z3,z4,z5,z16]),(0,[z1,z7,z3,z4,z1120,z6]),(0,[z1,z7,z3,z4,z36,z316]),(0,[z1,z7,z3,z4,z6,z1121]),(0,[z1,z7,z3,z5,z6,z1122]),(0,[z1,z7,z35,z814,z5,z6]),(0,[z26,z204,z7,z3,z4,z5]),(0,[z1,z7,z905,z4,z5,z6])],[(0,[z1,z7,z259,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z1123]),(0,[z1,z7,z3,z50,z440,z5]),(0,[z1,z569,z20,z4,z5,z6]),(0,[z1,z7,z3,z50,z449,z5]),(0,[z26,z1,z7,z3,z5,z138]),(0,[z59,z7,z3,z4,z801,z6]),(0,[z196,z1,z7,z3,z125,z165])],[(0,[z1,z7,z3,z4,z1124,z6]),(0,[z1,z7,z3,z4,z5,z1125]),(0,[z1059,z1,z7,z3,z173,z5]),(0,[z585,z7,z3,z4,z5,z37]),(0,[z1126,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z1127,z6])],[(0,[z1,z7,z3,z4,z1128,z6])],[(0,[z1,z320,z3,z540,z5,z6]),(0,[z1,z320,z3,z4,z462,z6]),(0,[z1,z7,z3,z173,z5,z16]),(0,[z1,z7,z3,z1129,z4,z5]),(0,[z1,z7,z3,z935,z56,z5]),(0,[z1,z694,z3,z4,z21,z6]),(0,[z1,z208,z3,z4,z5,z51])],[(0,[z26,z1,z7,z3,z80,z5]),(0,[z1,z7,z3,z4,z5,z1130]),(0,[z26,z1,z90,z3,z4,z5]),(0,[z1,z7,z44,z4,z5,z169])],[(0,[z26,z1,z7,z3,z347,z5]),(0,[z120,z7,z3,z4,z5,z950]),(0,[z1,z7,z3,z4,z5,z1131]),(0,[z107,z26,z1,z13,z7,z3])],[(0,[z1,z7,z3,z4,z5,z374]),(0,[z1,z17,z339,z4,z5,z6]),(0,[z1,z7,z3,z540,z5,z295]),(0,[z1,z146,z4,z106,z5,z6]),(0,[z1,z7,z4,z814,z5,z6])]],
   [[(0,[z1,z7,z1132,z4,z5,z6]),(0,[z47,z26,z7,z3,z56,z5]),(0,[z59,z7,z3,z34,z5,z6]),(0,[z26,z1,z7,z3,z566,z5]),(0,[z120,z7,z3,z4,z1073,z6]),(0,[z1,z7,z3,z4,z5,z1133]),(0,[z1134,z7,z3,z4,z5,z6])],[(0,[z1,z7,z87,z4,z139,z6]),(0,[z1,z1135,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z149]),(0,[z365,z7,z3,z4,z25,z6]),(0,[z1,z7,z3,z376,z4,z357]),(0,[z1,z1136,z7,z3,z4,z5]),(0,[z1,z7,z325,z50,z4,z5]),(0,[z1,z7,z3,z4,z1137,z6])],[(0,[z1,z7,z3,z4,z5,z1138]),(0,[z1,z17,z817,z4,z5,z6]),(0,[z1,z7,z3,z4,z27,z131]),(0,[z1,z7,z3,z4,z5,z289]),(0,[z26,z1083,z7,z3,z4,z5])],[(0,[z1,z1139,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z935,z5]),(0,[z1,z206,z817,z4,z5,z6]),(0,[z1,z7,z3,z4,z726,z6]),(0,[z1,z1140,z3,z4,z5,z6]),(0,[z1,z7,z3,z81,z441,z6])],[(0,[z1,z7,z3,z1141,z5,z6]),(0,[z1,z535,z3,z4,z5,z51]),(0,[z1,z7,z1142,z4,z5,z6])],[(0,[z1,z7,z259,z270,z5,z6]),(0,[z1,z7,z4,z1143,z5,z6]),(0,[z1,z7,z3,z4,z5,z1144]),(0,[z1,z7,z3,z4,z5,z1145])],[(0,[z109,z3,z477,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1146]),(0,[z1,z7,z3,z4,z1147,z6]),(0,[z1,z7,z3,z4,z1148,z6]),(0,[z1076,z7,z3,z4,z5,z6]),(0,[z1,z90,z4,z192,z5,z6]),(0,[z107,z386,z7,z3,z108,z6])],[(0,[z1,z7,z3,z1149,z5,z6]),(0,[z1,z1150,z3,z4,z5,z6]),(0,[z1151,z7,z3,z4,z5,z6]),(0,[z26,z1,z7,z175,z4,z5])]],
   [[(0,[z1,z7,z3,z1152,z5,z6]),(0,[z7,z3,z4,z5,z1153,z6]),(0,[z26,z1,z17,z18,z4,z5]),(0,[z1,z7,z3,z4,z779,z6]),(0,[z26,z1,z7,z3,z5,z506]),(0,[z1,z7,z3,z4,z1154,z6])],[(0,[z26,z1,z7,z3,z673,z5]),(0,[z26,z156,z1,z7,z3,z5]),(0,[z1,z7,z3,z4,z1155,z6]),(0,[z1,z7,z3,z4,z1156,z5])],[(0,[z0,z223,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1157]),(0,[z1,z1158,z3,z4,z5,z6]),(0,[z1,z7,z3,z832,z4,z5]),(0,[z1,z7,z3,z4,z5,z760]),(0,[z1,z90,z3,z50,z4,z5])],[(0,[z1,z7,z3,z4,z5,z493]),(0,[z285,z1,z7,z3,z159,z5]),(0,[z85,z1,z3,z376,z106,z5]),(0,[z1,z7,z190,z35,z5,z30])],[(0,[z1,z7,z3,z4,z5,z1159]),(0,[z1,z488,z7,z3,z34,z6]),(0,[z1,z817,z20,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1160]),(0,[z1,z7,z3,z1161,z5,z6]),(0,[z1,z7,z727,z4,z5,z6]),(0,[z1,z641,z20,z4,z5,z6]),(0,[z956,z7,z3,z4,z5,z6]),(0,[z10,z1,z3,z4,z5,z11]),(0,[z1,z410,z3,z50,z4,z5]),(0,[z1,z7,z3,z4,z5,z562]),(0,[z26,z1,z386,z7,z3,z5]),(0,[z1,z7,z1113,z50,z4,z5])],[(0,[z1,z7,z1162,z4,z5,z6]),(0,[z1,z7,z22,z3,z56,z5]),(0,[z26,z1,z7,z3,z4,z447]),(0,[z1,z7,z3,z440,z5,z149]),(0,[z196,z1163,z7,z3,z5,z6])],[(0,[z1,z7,z3,z4,z1164,z6]),(0,[z1,z7,z3,z125,z4,z567]),(0,[z82,z1,z7,z209,z192,z5]),(0,[z107,z26,z386,z7,z3,z5]),(0,[z1,z7,z3,z159,z6,z153])]],
   [[(0,[z1,z7,z3,z1165,z5,z6]),(0,[z1166,z1,z7,z3,z4,z6])],[(0,[z1,z7,z1167,z3,z4,z6]),(0,[z1,z7,z3,z1168,z5,z6]),(0,[z1,z7,z3,z860,z5,z6]),(0,[z1,z1169,z7,z3,z4,z5]),(0,[z196,z1,z7,z3,z5,z51]),(0,[z1,z7,z1170,z3,z4,z5]),(1,[z1,z7,z4,z5,z800]),(0,[z1,z7,z3,z4,z1171,z6]),(0,[z1,z7,z3,z5,z32,z378])],[(0,[z707,z1,z7,z3,z4,z5]),(0,[z99,z7,z24,z540,z5,z6]),(0,[z1,z7,z3,z4,z5,z1172]),(0,[z7,z3,z117,z50,z4,z5]),(0,[z1,z40,z3,z4,z21,z6]),(0,[z26,z1,z7,z3,z124,z5]),(0,[z26,z1,z7,z3,z625,z5])],[(0,[z7,z100,z87,z4,z5,z6]),(0,[z1173,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z1174,z5,z6]),(0,[z1,z925,z3,z4,z5,z6]),(0,[z107,z1,z7,z3,z934,z6]),(0,[z1,z7,z3,z50,z4,z1003])],[(0,[z1,z7,z3,z4,z5,z1175]),(0,[z1176,z7,z3,z4,z5,z6])],[(0,[z434,z7,z3,z4,z150,z6]),(0,[z73,z195,z7,z3,z4,z5])],[(0,[z26,z195,z7,z3,z34,z5]),(0,[z442,z7,z3,z4,z25,z6]),(0,[z1,z33,z3,z4,z5,z11]),(0,[z1,z13,z278,z4,z14,z6])],[(0,[z1177,z1,z7,z3,z4,z5]),(0,[z1,z1178,z3,z4,z5,z6]),(0,[z66,z7,z3,z56,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z1179,z6]),(0,[z1,z112,z3,z4,z176,z113]),(0,[z107,z26,z1,z7,z127,z3])],[(0,[z1180,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z81,z934,z6])],[(0,[z1,z7,z3,z4,z5,z1181]),(0,[z1,z7,z3,z4,z5,z1182]),(0,[z1,z7,z3,z754,z5,z6]),(0,[z1,z7,z3,z5,z1183,z6]),(0,[z1,z17,z86,z4,z5,z6]),(0,[z1,z7,z1025,z4,z5,z6]),(0,[z26,z1,z7,z3,z232,z5]),(0,[z1,z7,z3,z4,z5,z1184])],[(0,[z1,z320,z3,z4,z5,z16]),(0,[z1,z7,z3,z4,z5,z1185])],[(0,[z1186,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1187])],[(0,[z1,z7,z3,z4,z1188,z6]),(0,[z1,z7,z3,z4,z5,z1189]),(0,[z1,z7,z269,z3,z34,z6]),(0,[z1,z7,z1190,z4,z5,z6]),(0,[z1,z112,z3,z4,z176,z132]),(0,[z1,z7,z3,z4,z5,z1191])],[(0,[z1,z7,z3,z776,z4,z5]),(0,[z1,z7,z3,z93,z5,z6]),(0,[z1,z7,z95,z4,z5,z6]),(0,[z7,z3,z4,z5,z1192,z6]),(0,[z1,z7,z3,z5,z822,z96])],[(0,[z1,z7,z3,z98,z5,z6]),(0,[z26,z1,z7,z3,z34,z5])]],
   [[(0,[z1,z7,z3,z291,z5,z242]),(0,[z1,z208,z3,z4,z5,z760])],[(0,[z1,z7,z3,z4,z5,z1193]),(0,[z1194,z7,z3,z4,z5,z6]),(0,[z811,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1195]),(0,[z1,z1196,z3,z4,z5,z6])],[(0,[z0,z2,z3,z270,z5,z6]),(0,[z1,z7,z3,z1197,z5,z6]),(0,[z285,z195,z7,z3,z4,z5]),(0,[z26,z1,z7,z3,z584,z5]),(0,[z1,z7,z3,z4,z5,z1198]),(0,[z373,z1,z7,z3,z4,z280]),(0,[z1,z7,z3,z4,z36,z54])],[(0,[z1,z7,z3,z4,z447,z6]),(0,[z26,z7,z3,z117,z4,z5]),(0,[z995,z7,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z45,z800])],[(0,[z665,z7,z3,z56,z5,z6])],[(0,[z1,z7,z3,z270,z5,z374]),(0,[z1,z7,z3,z4,z5,z1199]),(0,[z1,z7,z3,z1200,z5,z6]),(0,[z85,z1,z175,z106,z5,z6]),(0,[z1,z7,z3,z1201,z5,z6]),(0,[z1,z7,z3,z50,z5,z242])],[(0,[z1,z7,z3,z1202,z5,z6]),(0,[z1,z7,z3,z270,z616,z6]),(0,[z48,z7,z3,z34,z5,z67]),(0,[z966,z1,z7,z3,z347,z5]),(0,[z1,z7,z3,z81,z610,z6]),(0,[z82,z1,z7,z269,z192,z6])],[(0,[z1,z7,z3,z4,z1203,z6]),(0,[z1,z7,z3,z4,z5,z1204]),(0,[z1,z7,z3,z1205,z5,z6]),(0,[z1,z7,z44,z4,z5,z800]),(0,[z1163,z7,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 520).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1040).take 209) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1249)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [520, 520, 209] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 100).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 200).take 56).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [100, 100, 56] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_38933

theorem PEqualNP.Outside.L_meta_38933 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276145344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276145344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38933.solve