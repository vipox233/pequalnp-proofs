import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37803

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
  Nat.testBit (4277074600 * 2 ^ 32 + 4276681384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x20001812810a04a1#64 ++ 0x110000c094085025#64 ++ 0xd812387f831e1ffe#64 ++ 0xfec091c3fc18f0ff#64 : BitVec 256),
   (0xc024c6490c659256#64 ++ 0x2e01263248632c92#64 ++ 0xb66dc6499ce7927d#64 ++ 0xbdb36e324ce73c93#64 : BitVec 256),
   (0x808e028c20b0a304#64 ++ 0x0404701461058518#64 ++ 0x798e078e60f9e39b#64 ++ 0xebcc703c7307cf1c#64 : BitVec 256),
   (0x0170056056015818#64 ++ 0x480b802b02b00ac0#64 ++ 0xfbf007f07f01fc17#64 ++ 0xe7df803f83f80fe0#64 : BitVec 256),
   (0x03db68007bde0000#64 ++ 0x701edb4003def000#64 ++ 0xf7fff8007ffe000f#64 ++ 0x9fbfffc003fff000#64 : BitVec 256),
   (0x05ffb7ff8000001f#64 ++ 0x802ffdbffc000000#64 ++ 0xf5ffffff80000000#64 ++ 0x7faffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f07f01fc17 0xe7df803f83f80fe0

def z1 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8007ffe000f 0x9fbfffc003fff000

def z2 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x8471f87180000000 0x14238fc38c000000

def z3 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd812387f831e1ffe 0xfec091c3fc18f0ff

def z4 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078e60f9e39b 0xebcc703c7307cf1c

def z5 : W := mkw 0x81fe07ec76b1fb1c 0x4c0ff03f63b58fd8 0xfbfe07fe7ff9ff9f 0xefdff03ff3ffcffc

def z6 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6499ce7927d 0xbdb36e324ce73c93

def z7 : W := mkw 0x07fffffffbde001f 0xf03fffffffdef000 0xf7fffffffffe000f 0xffbffffffffff000

def z8 : W := mkw 0x00000800010a0000 0x1000004000085000 0xd0123800031e000e 0x9e8091c00018f000

def z9 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80000000 0x7faffffffc000000

def z10 : W := mkw 0x23db7812fbde04a1 0x711edbc097def025 0xfffff87ffffe1fff 0xffffffc3fffff0ff

def z11 : W := mkw 0x0150000052000000 0x400a800002900000 0xfbf000707f001c17 0xe7df800383f800e0

def z12 : W := mkw 0x8004028c0020a304 0x0400201460010518 0x0800078e0001e390 0x6040003c70000f1c

def z13 : W := mkw 0x85ffb7ff8020a31f 0x842ffdbffc010518 0xfdffffff8001e390 0x7feffffffc000f1c

def z14 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xf3f007f07c01e001 0x679f803f83e00f00

def z15 : W := mkw 0x05ffb7ff8401581f 0x882ffdbffc200ac0 0xfdffffff8001fc10 0x7feffffffc000fe0

def z16 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0x040ff80000fe0008 0x18207fc00007f000

def z17 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe0f9e39b 0xffefffffff07cf1c

def z18 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x000e000e00f80388 0x080070007007c01c

def z19 : W := mkw 0x0000400008440000 0x2000020000422000 0xb66dc0001ce6000d 0x9db36e0000e73000

def z20 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000007ffe000f 0x8010000003fff000

def z21 : W := mkw 0x01ffa64900000016 0x000ffd3248000000 0xf5fffe4980000000 0x3faffff24c000000

def z22 : W := mkw 0xc3ffee497fff9256 0x7e1fff724bfffc92 0xf7fffe49ffff927f 0xbfbffff24ffffc93

def z23 : W := mkw 0x4000c00108440042 0x2200060008422002 0x0401c00180060060 0x10200e000c003003

def z24 : W := mkw 0x0150000052000000 0x400a800002900000 0xf3f000007f000007 0x879f800003f80000

def z25 : W := mkw 0x05ffb7ffd200001f 0xc02ffdbffe900000 0xf7ffffffff000007 0xffbffffffff80000

def z26 : W := mkw 0x81de028c72b0a304 0x440ef01463958518 0xfbfe078e7ff9e39f 0xefdff03c73ffcf1c

def z27 : W := mkw 0x008b200000000000 0x0004590000000000 0x040ff80000000000 0x18207fc000000000

def z28 : W := mkw 0xc174c7695e65da5e 0x6e0ba63b4af32ed2 0xb67dc6799fe79e7d 0xbdb3ee33ccff3cf3

def z29 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x48123836031e1ffe 0xc24091c1b018f0ff

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x5802000e0018039a 0xeac010007000c01c

def z31 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf207fe7f19ff9f 0xefdf903ff3f8cffc

def z32 : W := mkw 0xa000080021baa7a0 0x15000040010dd53d 0x0800000063ffffff 0x80400000031fffff

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0xd810007003001c16 0xe6c08003801800e0

def z34 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8707ffe1c1f 0xffffffc383fff0e0

def z35 : W := mkw 0xa08e129ea0b0a7a5 0x05047094f505853d 0x798e07ffe0f9fffb 0xebcc703fff07cfff

def z36 : W := mkw 0x0024864900000016 0x0001243248000000 0xb46dc64980000000 0x3da36e324c000000

def z37 : W := mkw 0xc5fff7ff8c65925f 0xae2fffbffc632c92 0xf7ffffff9ce7927d 0xffbffffffce73c93

def z38 : W := mkw 0x00004800094e0000 0x30000240004a7000 0xf67ff8001ffe000f 0x9fb3ffc000fff000

def z39 : W := mkw 0xc00040000c659240 0x2e00020000632c92 0x020000001ce7927d 0x8010000000e73c93

def z40 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040ff80f80000000 0x18207fc07c000000

def z41 : W := mkw 0xc004c20908648246 0x2600261048432412 0x040dc00980e60268 0x18206e004c073013

def z42 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff80000000000 0x1fafffc000000000

def z43 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xa7fdf8007fe60005 0x153fefc003ff3000

def z44 : W := mkw 0x0401b01380000003 0x80200d809c000000 0x0401f80180000000 0x10200fc00c000000

def z45 : W := mkw 0x008e028c00000004 0x0004701460000000 0x718e078e00000000 0x6b8c703c70000000

def z46 : W := mkw 0x03716d605f4f5818 0x781b8b6b02fa7ac0 0xfff1fff07f07fc17 0xf7ff8fff83f83fe0

def z47 : W := mkw 0x008e028c00000004 0x0004701460000000 0x798e078e0018039a 0xebcc703c7000c01c

def z48 : W := mkw 0xa08e0a8c21baa7a4 0x15047054610dd53d 0x798e078e63ffffff 0xebcc703c731fffff

def z49 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffff80f80388 0x7faffffffc07c01c

def z50 : W := mkw 0xc3ffeecd7fffb356 0x7e1fff766bfffd9a 0xffffffcffffff3ff 0xfffffffe7fffff9f

def z51 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffffff01fc17 0xfffffffffff80fe0

def z52 : W := mkw 0x8000000020b0a300 0x0400000001058518 0x0000000000f80388 0x000000000007c01c

def z53 : W := mkw 0x22005812fbde04a1 0x711002c097def025 0xda12387ffffe1fff 0xfed091c3fffff0ff

def z54 : W := mkw 0x808e020820b08204 0x0404701041058410 0x718e060860f9821b 0xab8c70304307cc10

def z55 : W := mkw 0xe024de5b8d6f96f7 0x3f0126f2dc6b7cb7 0xfe7ffe7f9fff9fff 0xfff3fff3fcfffcff

def z56 : W := mkw 0x25ffbfff810a04bf 0x912ffdfffc085025 0xfdffffff831e1ffe 0xffeffffffc18f0ff

def z57 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x23e007807c01e001 0x011f003c03e00f00

def z58 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7ffffff9f001c04 0x7fbffffffcf800e0

def z59 : W := mkw 0x0020044004011010 0x0801002200200880 0xb26006401c019015 0xa593003200e00c80

def z60 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0x8671f8001f060004 0x14338fc000f83000

def z61 : W := mkw 0x8000000020b0a300 0x0400000001058518 0x0800000060f9e39b 0x804000000307cf1c

def z62 : W := mkw 0x0170056000000018 0x000b802b00000000 0xf1f007f000000000 0x678f803f80000000

def z63 : W := mkw 0x817407685621da1c 0x4c0ba03b42b10ed0 0xfbfc07f87fe1fe1f 0xefdfe03fc3ff0ff0

def z64 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7fffffffc01e001 0x7fbfffffffe00f00

def z65 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0x25edc78000000000 0x012f6e3c00000000

def z66 : W := mkw 0x035048007bde0000 0x701a824003def000 0xf3f000007ffe000f 0x879f800003fff000

def z67 : W := mkw 0x21701d72d70b5cb9 0x590b80eb96b85ae5 0xda72387f9f1e1ffe 0xfed391c3fcf8f0ff

def z68 : W := mkw 0x03704d607fdf5818 0x781b826b03fefac0 0xfbf007f07ffffc1f 0xe7df803f83ffffe0

def z69 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0x419239b600000000 0x420c91cdb0000000

def z70 : W := mkw 0x0200480029de0000 0x30100240014ef000 0x0000000000fe0008 0x000000000007f000

def z71 : W := mkw 0xc004c2090c659246 0x2e00261048632c92 0x060dc0099ce7927d 0x98306e004ce73c93

def z72 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6001ce18001 0x01336e3000e70c00

def z73 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0x27edc0007ce00001 0x013f6e0003e70000

def z74 : W := mkw 0x042497ff8000001f 0x802124bffc000000 0x000007ff80000000 0x6000003ffc000000

def z75 : W := mkw 0x03db2800739a0000 0x501ed940039cd000 0x4192380063180002 0x020c91c00318c000

def z76 : W := mkw 0xc024864904219256 0x0e01243248210c92 0x0000064980019270 0x200000324c000c93

def z77 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff80e7ffe039f 0xffffffc073fff01c

def z78 : W := mkw 0x21701d72d70b5cb9 0x590b80eb96b85ae5 0xfbf23ff67f19fd97 0xe7df91ffb3f8cfec

def z79 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x27eff8007cfe0009 0x193f7fc003e7f000

def z80 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x298c078e60e1e391 0x614c603c73070f1c

def z81 : W := mkw 0x028a48007bde0000 0x7014524003def000 0x738e00007ffe000f 0x8b9c700003fff000

def z82 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x4812383603180d82 0x424091c1b018c06c

def z83 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff83001c16 0xffeffffffc1800e0

def z84 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0x8661c0419c061064 0x14330e020ce03083

def z85 : W := mkw 0xc5fff7ffacf5b35f 0xae2fffbffd67ad9a 0xfffffffffcfff3ff 0xffffffffffe7ff9f

def z86 : W := mkw 0x0575b77b8000001f 0x802badbbdc000000 0xb47dfe7980000000 0x3da3eff3cc000000

def z87 : W := mkw 0x20001012800004a1 0x0100008094000025 0xd810007f83001ff6 0xe6c08003fc1800ff

def z88 : W := mkw 0x008a000000000000 0x0004500000000000 0x718e000000000000 0x0b8c700000000000

def z89 : W := mkw 0x23db3812f39a04a1 0x511ed9c0979cd025 0x4992383663180d82 0x424c91c1b318c06c

def z90 : W := mkw 0x048fa28d00000006 0x80247d1468000000 0x040dc00000000000 0x00206e0000000000

def z91 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x758fff8f80000000 0x7bac7ffc7c000000

def z92 : W := mkw 0x20000800570b5ca0 0x5900004002b85ae5 0x0a0000007f1fffff 0x8050000003f8ffff

def z93 : W := mkw 0x23db7812fbde04a1 0x711edbc097def025 0xf7fff80ffffe03ef 0x9fbfffc07ffff01f

def z94 : W := mkw 0x20000800010a04a0 0x1100004000085025 0x08000000031e1ffe 0x804000000018f0ff

def z95 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd812387f83180d82 0x7ec091c3fc18c06c

def z96 : W := mkw 0x0020056056015818 0x4801002b02b00ac0 0x0a0007f07f01fc17 0xe050003f83f80fe0

def z97 : W := mkw 0x0000000056015800 0x4800000002b00ac0 0x0a0000007f01fc17 0x8050000003f80fe0

def z98 : W := mkw 0x0020056004015818 0x0801002b00200ac0 0x080007f00001fc10 0x6040003f80000fe0

def z99 : W := mkw 0xc024c7690c65da5e 0x2e01263b48632ed2 0xbe6dc7f99ce7fe7d 0xfdf36e3fcce73ff3

def z100 : W := mkw 0x85ffb7fff6b1fb1f 0xcc2ffdbfffb58fd8 0xfffffffffff9ff9f 0xffffffffffffcffc

def z101 : W := mkw 0x008a008420902100 0x0004500421048108 0x4982018660186182 0x424c100c3300c30c

def z102 : W := mkw 0x0575b7ff8000001f 0x802badbffc000000 0x8471ffff80000000 0x74238ffffc000000

def z103 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xa3f007f07f01fc05 0x051f803f83f80fe0

def z104 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff8018039a 0xffeffffffc00c01c

def z105 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf98e07cfe0fff3ff 0xffcc703e7f07ff9f

def z106 : W := mkw 0x03fb6d607fdf5818 0x781fdb6b03fefac0 0xfffffff07ffffc1f 0xffffffff83ffffe0

def z107 : W := mkw 0x028b68007bde0000 0x70145b4003def000 0x060ff8007ffe000f 0x98307fc003fff000

def z108 : W := mkw 0x008a000020900000 0x0004500001048000 0x718e000060f8000b 0x8b8c70000307c000

def z109 : W := mkw 0x05ffb7ffa090001f 0x802ffdbffd048000 0xf5ffffffe0f8000b 0xffafffffff07c000

def z110 : W := mkw 0x0150012052004808 0x400a800902900240 0xfbf001b07f006c07 0xc7df800d83f80360

def z111 : W := mkw 0xc00040000c659240 0x2e00020000632c92 0x020000001ce18001 0x0010000000e70c00

def z112 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffffe0e1e001 0x7fafffffff070f00

def z113 : W := mkw 0x0020044004011010 0x0801002200200880 0xfa7006701f019c17 0xe7d3803380f80ce0

def z114 : W := mkw 0x8004020800208204 0x0400201040010410 0x300c060800e18219 0xa980603040070c10

def z115 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x718e000e60f8038b 0x8b8c70007307c01c

def z116 : W := mkw 0x8004028c0020a304 0x0400201460010518 0x000007800001e000 0x0000003c00000f00

def z117 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x8010387183061c64 0x140081c38c1830e3

def z118 : W := mkw 0x04afb7ff8000001f 0x80257dbffc000000 0x040fffff80000000 0x78207ffffc000000

def z119 : W := mkw 0x0150012052004808 0x400a800902900240 0x499001b063006c02 0x424c800d83180360

def z120 : W := mkw 0x21701d72d70b5cb9 0x590b80eb96b85ae5 0xfbf23fffff1fffff 0xffdf91fffff8ffff

def z121 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xf5ffff8000000000 0x1faffffc00000000

def z122 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0002380f801e03e8 0x180011c07c00f01f

def z123 : W := mkw 0xc024c6cd0c65b356 0x2e01263668632d9a 0xbe6dc7cf9ce7f3fd 0xfdf36e3e7ce73f9f

def z124 : W := mkw 0x8024864900208216 0x0401243248010410 0xb46dc64980e18219 0xbda36e324c070c10

def z125 : W := mkw 0xc0aec6cd0c659256 0x2e05763668632c92 0xf7efc7cf9ce7927d 0xffbf7e3e7ce73c93

def z126 : W := mkw 0x01db200020900000 0x000ed90001048000 0xf5fff80060f8000b 0x9fafffc00307c000

def z127 : W := mkw 0x01fb256000000018 0x000fd92b00000000 0xf5fffff000000000 0x7fafffff80000000

def z128 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x9010387983061e7c 0xbc8081c3cc1830f3

def z129 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xfe7dc6799fe79e7f 0xfff3ee33ccff3cf3

def z130 : W := mkw 0x2571bd73810a04bb 0x912b8deb9c085025 0xdc73f87f831e1ffe 0xfee39fc3fc18f0ff

def z131 : W := mkw 0xa08e1a9ea1baa7a5 0x150470d4f50dd53d 0xf99e3fffe3ffffff 0xffccf1ffff1fffff

def z132 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff849fffe127f 0xbfbfffc24ffff093

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000e00000390 0x604000007000001c

def z134 : W := mkw 0x0000101280000001 0x0000008094000000 0xd012387f80000000 0x7e8091c3fc000000

def z135 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xf5f1fff180000000 0x77af8fff8c000000

def z136 : W := mkw 0x8004020800208204 0x0400201040010410 0x798c078860e1e21b 0xebcc603c43070f10

def z137 : W := mkw 0x83df6a8c7bfea304 0x741efb5463dff518 0xffffff8e7fffe39f 0xfffffffc73ffff1c

def z138 : W := mkw 0x05ffb7ffa090211f 0x802ffdbffd048108 0xfdffffffe0186182 0x7fefffffff00c30c

def z139 : W := mkw 0x808e028c00208204 0x0404701460010410 0x718e078e00e18219 0xeb8c703c70070c10

def z140 : W := mkw 0x842497ff8020a31f 0x842124bffc010518 0x080007ff8001e390 0x6040003ffc000f1c

def z141 : W := mkw 0x00000800010a0000 0x1000004000085000 0xd812380e031e039e 0xfec091c07018f01c

def z142 : W := mkw 0x808a008420b0a300 0x0404500421058518 0x4982018660f9e39b 0xc24c100c3307cf1c

def z143 : W := mkw 0x0150012052004808 0x400a800902900240 0x0010003003000c00 0x0000800180180060

def z144 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0x040ff80f80f80388 0x18207fc07c07c01c

def z145 : W := mkw 0xa08e1a9ea1baa7a5 0x150470d4f50dd53d 0x798e3f8fe0ffe3fb 0xfbcc71fc7f07ff1f

def z146 : W := mkw 0x03db69207bde4808 0x701edb4903def240 0xfffff9b07ffe6c0f 0xdfffffcd83fff360

def z147 : W := mkw 0x20001012800004a1 0x0100008094000025 0x0800007f80001ff0 0x60400003fc0000ff

def z148 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd0123871831e1c6e 0x9e8091c38c18f0e3

def z149 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x8a7000707f01fc17 0x8453800383f80fe0

def z150 : W := mkw 0x20000800010a04a0 0x1100004000085025 0x00000000001e03e8 0x000000000000f01f

def z151 : W := mkw 0x05ffb7ffd200481f 0xc02ffdbffe900240 0xfdffffffe3006c02 0x7fefffffff180360

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0x798007806001e013 0xe3cc003c03000f00

def z153 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x847ff87f80000000 0x1c23ffc3fc000000

def z154 : W := mkw 0xc575f77b8c65925f 0xae2bafbbdc632c92 0xb67dfe799ce7927d 0xbdb3eff3cce73c93

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0xd010007000000000 0x6680800380000000

def z156 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xcbf001f07f007c06 0x465f800f83f803e0

def z157 : W := mkw 0x035168007bde0000 0x701a8b4003def000 0x8671f8007ffe000f 0x94338fc003fff000

def z158 : W := mkw 0x0150012052004808 0x400a800902900240 0x799007b06301ec13 0xe3cc803d83180f60

def z159 : W := mkw 0xc174c7695e65da5e 0x6e0ba63b4af32ed2 0xfffdc7f9ffe7fe7f 0xffffee3fcfff3ff3

def z160 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x718e078e60e1e001 0x6b8c703c73070f00

def z161 : W := mkw 0xc000400008648240 0x2600020000432412 0x0000000000e60268 0x0000000000073013

def z162 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xfdffffff80001ff0 0x7feffffffc0000ff

def z163 : W := mkw 0x20000800010a04a0 0x1100004000085025 0x0000000003061c64 0x00000000001830e3

def z164 : W := mkw 0x25ffbfff810a04bf 0x912ffdfffc085025 0xf5ffffff83061c64 0x7faffffffc1830e3

def z165 : W := mkw 0x25ffbfffd70b5cbf 0xd92ffdfffeb85ae5 0xffffffffff1fffff 0xfffffffffff8ffff

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000800000218 0xa880000040000010

def z167 : W := mkw 0xa0041a1a812a86a5 0x150020d0d4095435 0xf81e3e7f83ff9fff 0xffc0f1f3fc1ffcff

def z168 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0xd673f8001f1e000e 0x9eb39fc000f8f000

def z169 : W := mkw 0xc0aec6cd2cf5b356 0x2e0576366967ad9a 0xb66fc64f9cff93fd 0xbdb37e327ce7fc9f

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z171 : W := mkw 0x0000000004015800 0x0800000000200ac0 0x080000000001fc10 0x0040000000000fe0

def z172 : W := mkw 0x0000000056015800 0x4800000002b00ac0 0x020000001f001c04 0x0010000000f800e0

def z173 : W := mkw 0xc00040005e65da40 0x6e00020002f32ed2 0x0a0000007fe7fe7f 0x8050000003ff3ff3

def z174 : W := mkw 0xe00048000d6f96e0 0x3f000240006b7cb7 0x0a0000001fff9fff 0x8050000000fffcff

def z175 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0xb67df8001fe6000d 0x9db3efc000ff3000

def z176 : W := mkw 0x0000101280000001 0x0000008094000000 0xd812387f83001c16 0xfec091c3fc1800e0

def z177 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd012387f801e03e8 0x7e8091c3fc00f01f

def z178 : W := mkw 0x0024c64908440016 0x2001263248422000 0xb66dc6499ce6000d 0xbdb36e324ce73000

def z179 : W := mkw 0x248fba9f810a04a7 0x91247dd4fc085025 0xdc1ff87f831e1ffe 0xfee0ffc3fc18f0ff

def z180 : W := mkw 0x05fbb5738000001b 0x802fddab9c000000 0xf5fff87180000000 0x1fafffc38c000000

def z181 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0xf5fff9b600000000 0x5fafffcdb0000000

def z182 : W := mkw 0x01fe07ec0000001c 0x000ff03f60000000 0xf1fe07fe00000000 0x6f8ff03ff0000000

def z183 : W := mkw 0x0000000056015800 0x4800000002b00ac0 0x7b8007807f01fc17 0xe3dc003c03f80fe0

def z184 : W := mkw 0xe024d65b8c6596f7 0x2f0126b2dc632cb7 0xbe6dc67f9ce79ffd 0xfdf36e33fce73cff

def z185 : W := mkw 0x220048007bde04a0 0x7110024003def025 0x0a0000007ffe1fff 0x8050000003fff0ff

def z186 : W := mkw 0x040011b680000009 0x8020008db4000000 0x000001b600000000 0x4000000db0000000

def z187 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x41923fff80000000 0x620c91fffc000000

def z188 : W := mkw 0x0024965b80000017 0x000124b2dc000000 0xf47ffe7f80000000 0x7fa3fff3fc000000

def z189 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x499007f06301fc12 0x624c803f83180fe0

def z190 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x218c078060e1e001 0x010c603c03070f00

def z191 : W := mkw 0xc0aec6cd2cf5b356 0x2e0576366967ad9a 0xffefc7cffcfff3ff 0xffff7e3e7fe7ff9f

def z192 : W := mkw 0x05fff7ff8844001f 0xa02fffbffc422000 0xf7ffffff9ce6000d 0xffbffffffce73000

def z193 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xf7ffffff9c019015 0xffbffffffce00c80

def z194 : W := mkw 0xc024864904219256 0x0e01243248210c92 0xb46dc64980019270 0x3da36e324c000c93

def z195 : W := mkw 0x23517812db4e04a1 0x711a8bc096da7025 0x8671f8719f061c64 0x14338fc38cf830e3

def z196 : W := mkw 0xc42497ff8421925f 0x8e2124bffc210c92 0x000007ff80019270 0x6000003ffc000c93

def z197 : W := mkw 0x0000000052004800 0x4000000002900240 0x0800000063006c02 0x0040000003180360

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010007003001c04 0x04008003801800e0

def z199 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd012387f83061c64 0x7e8091c3fc1830e3

def z200 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xc7f3f8007f1e0006 0x163f9fc003f8f000

def z201 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x8012387f831e1fec 0x1c0091c3fc18f0ff

def z202 : W := mkw 0x020048005b4e0000 0x7010024002da7000 0x020000001f060004 0x0010000000f83000

def z203 : W := mkw 0xe3fffe5bffff96f7 0x7f1ffff2dffffcb7 0xfffffe7fffff9fff 0xfffffff3fffffcff

def z204 : W := mkw 0x208e1a9e810a04a5 0x110470d4f4085025 0xf99e3fff831e1ffe 0xffccf1fffc18f0ff

def z205 : W := mkw 0xc3ffe6497ef59256 0x6e1fff324bf7ac92 0x27edc6007ce18001 0x013f6e3003e70c00

def z206 : W := mkw 0x05dfb29f80000007 0x802efd94fc000000 0xf5fff80f80000000 0x1fafffc07c000000

def z207 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0x8671f8719f001c04 0x14338fc38cf800e0

def z208 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0xd41ff87f80000000 0x7ea0ffc3fc000000

def z209 : W := mkw 0x035160005a440000 0x601a8b0002d22000 0x0661c0001c000000 0x00330e0000e00000

def z210 : W := mkw 0xe5ffffff8d6f96ff 0xbf2ffffffc6b7cb7 0xffffffff9fff9fff 0xfffffffffcfffcff

def z211 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xf9923fffe31fffff 0xffcc91ffff18ffff

def z212 : W := mkw 0x04afb6df80000017 0x80257db6fc000000 0xb46ffe4f80000000 0x3da37ff27c000000

def z213 : W := mkw 0x83df628c7af4a304 0x641efb1463d7a518 0x7fefc78e7cf9e39b 0xebff7e3c73e7cf1c

def z214 : W := mkw 0x8004028c0020a304 0x0400201460010518 0x5802078e0019e39a 0xeac0103c7000cf1c

def z215 : W := mkw 0xc5ffe7ed0c65925e 0xae2fff3f68632c92 0x27edc7801ce18001 0x013f6e3c00e70c00

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0xf99007f06301fc17 0xe7cc803f83180fe0

def z217 : W := mkw 0x03fb6c407fdf1010 0x781fdb6203fef880 0xf7fffe407fff901f 0xbfbffff203fffc80

def z218 : W := mkw 0xc08ec28d28f4a346 0x260476146947a51a 0x7d8fc78fe0ffe3fb 0xfbec7e3c7f07ff1f

def z219 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x439238007ffe000f 0x821c91c003fff000

def z220 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0xc5f3f9f780000000 0x562f9fcfbc000000

def z221 : W := mkw 0x01fb256056015818 0x480fd92b02b00ac0 0xfffffff07f01fc17 0xffffffff83f80fe0

def z222 : W := mkw 0x0150000056015800 0x480a800002b00ac0 0xfbf000007f01fc17 0x87df800003f80fe0

def z223 : W := mkw 0xa0041a9e812aa7a5 0x150020d4f409553d 0xd8123fff831ffffe 0xfec091fffc18ffff

def z224 : W := mkw 0x05df33be8000000d 0x802ef99df4000000 0x719e3fbe00000000 0x6b8cf1fdf0000000

def z225 : W := mkw 0x008e028c20902104 0x0004701461048108 0x798e078e60186182 0x6bcc703c7300c30c

def z226 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0xb661c6419c079075 0xb5b30e320ce03c83

def z227 : W := mkw 0x8004420808648204 0x2400221040432410 0xb66dc6081ce7821d 0xbdb36e3040e73c10

def z228 : W := mkw 0xa5ffbfffa1baa7bf 0x952ffdfffd0dd53d 0xfdffffffe3ffffff 0xffefffffff1fffff

def z229 : W := mkw 0x0150000052000000 0x400a800002900000 0x4190000063000002 0x020c800003180000

def z230 : W := mkw 0xe024ce490d6f96f6 0x3f012672486b7cb7 0xbe6dc6499fff9fff 0xbdf36e324cfffcff

def z231 : W := mkw 0x23fb7d72ffdf5cb9 0x791fdbeb97fefae5 0xffffffffffffffff 0xffffffffffffffff

def z232 : W := mkw 0x828f6a8c29fea304 0x34147b54614ff518 0x040ff80e00fe0388 0x18207fc07007f01c

def z233 : W := mkw 0x07ffffffa9de001f 0xb03ffffffd4ef000 0xf5ffffff80fe0008 0x7faffffffc07f000

def z234 : W := mkw 0x20000800010a04a0 0x1100004000085025 0xd8123800031e1ffe 0x9ec091c00018f0ff

def z235 : W := mkw 0xc020c4410c659252 0x2e01062208632c92 0x8661c0419ce7927d 0x94330e020ce73c93

def z236 : W := mkw 0x21db3812810a04a1 0x110ed9c094085025 0xfdfff87f831e1ffe 0xffefffc3fc18f0ff

def z237 : W := mkw 0xc024d65b8c659257 0x2e0126b2dc632c92 0xf67ffe7f9ce7927d 0xffb3fff3fce73c93

def z238 : W := mkw 0xc00442080c659244 0x2e00221040632c92 0x320c06081ce7927d 0xa990603040e73c93

def z239 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x866dc0499ce6126c 0x1c336e024ce73093

def z240 : W := mkw 0x80ae07ec24b1fb1c 0x0c05703f61258fd8 0x798e07fe60f9ff9b 0xebcc703ff307cffc

def z241 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0xb66dc0419ce6106d 0x9db36e020ce73083

def z242 : W := mkw 0x0024864900000016 0x0001243248000000 0x246dc60000000000 0x01236e3000000000

def z243 : W := mkw 0xc02486cd0421b356 0x0e01243668210d9a 0x080007cf8001f3f0 0x6040003e7c000f9f

def z244 : W := mkw 0xc5fff7ff8864825f 0xa62fffbffc432412 0xf5ffffff80e60268 0x7faffffffc073013

def z245 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xa66dc6419ce79065 0x15336e320ce73c83

def z246 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xffffff807fffe01f 0xfffffffc03ffff00

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0xb46dc00000000000 0x1da36e0000000000

def z248 : W := mkw 0x820048007bfea300 0x7410024003dff518 0x0a0000007fffe39f 0x8050000003ffff1c

def z249 : W := mkw 0x01db301280000001 0x000ed98094000000 0xf5fff87f80000000 0x7fafffc3fc000000

def z250 : W := mkw 0x03fb6d607fdf5818 0x781fdb6b03fefac0 0xf7ffff807fffe00f 0x9fbffffc03ffff00

def z251 : W := mkw 0x81df228c20b0a304 0x040ef91461058518 0xfdffff8e60f9e39b 0xffeffffc7307cf1c

def z252 : W := mkw 0x85df33bea0b0a30d 0x842ef99df5058518 0x799e3fbe60f9e39b 0xebccf1fdf307cf1c

def z253 : W := mkw 0x0020056000000018 0x0001002b00000000 0x000007f000000000 0x6000003f80000000

def z254 : W := mkw 0x042497ff8401581f 0x882124bffc200ac0 0x080007ff8001fc10 0x6040003ffc000fe0

def z255 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x25efff8f80000000 0x192f7ffc7c000000

def z256 : W := mkw 0x017487690000001e 0x000ba43b48000000 0xf5fdc7f980000000 0x7fafee3fcc000000

def z257 : W := mkw 0x0000101280000001 0x0000008094000000 0xd812387f8018039a 0xfec091c3fc00c01c

def z258 : W := mkw 0x20001012800004a1 0x0100008094000025 0x0000000f800003e0 0x000000007c00001f

def z259 : W := mkw 0x20001012800004a1 0x0100008094000025 0xd812387f80001ff0 0x7ec091c3fc0000ff

def z260 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x026000001c000000 0x0013000000e00000

def z261 : W := mkw 0x01db200052000000 0x400ed90002900000 0xf7fff8007f000007 0x9fbfffc003f80000

def z262 : W := mkw 0x0000008400002100 0x0000000420000108 0x0800018600006180 0x4040000c3000030c

def z263 : W := mkw 0x028b2800219a0000 0x10145940010cd000 0x0002380000180000 0x000011c00000c000

def z264 : W := mkw 0x042095738000001b 0x802104ab9c000000 0x0000007180000000 0x000000038c000000

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x900000498006127c 0xbc8000024c003093

def z266 : W := mkw 0xc024c64908648256 0x2601263248432412 0xb46dc64980e60268 0x3da36e324c073013

def z267 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xf5ffffff80e18219 0xffaffffffc070c10

def z268 : W := mkw 0x0000101280000001 0x0000008094000000 0x0002380f80000000 0x180011c07c000000

def z269 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffffe001e013 0xffefffffff000f00

def z270 : W := mkw 0x00000800010a0000 0x1000004000085000 0x00000000031e000e 0x800000000018f000

def z271 : W := mkw 0x05fb35f6d6015819 0xc82fd9afb6b00ac0 0xfbf23ff67f01fc17 0xe7df91ffb3f80fe0

def z272 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xb5edc7c980000000 0x3daf6e3e4c000000

def z273 : W := mkw 0xc024864904219256 0x0e01243248210c92 0x300c064980e19279 0xa98060324c070c93

def z274 : W := mkw 0x03db680029de0000 0x301edb40014ef000 0xf5fff80000fe0008 0x1fafffc00007f000

def z275 : W := mkw 0x0000400008440000 0x2000020000422000 0x8661c0001c060004 0x14330e0000e03000

def z276 : W := mkw 0xc375ee495f6f9256 0x7e1baf724afb7c92 0xb67dfe499fe7927d 0xbdb3eff24cff3c93

def z277 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xf7fff8007ce00001 0x1fbfffc003e70000

def z278 : W := mkw 0xc28fea0929fe8246 0x36147f50494ff412 0x040ff80980fe0268 0x18207fc04c07f013

def z279 : W := mkw 0x03512800530a0000 0x501a894002985000 0x0010380003000000 0x000081c000180000

def z280 : W := mkw 0xc20048007fff9240 0x7e10024003fffc92 0x020000007fff927f 0x8010000003fffc93

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0xb26000001c000005 0x8593000000e00000

def z282 : W := mkw 0x0004820900000006 0x0000241048000000 0x040dc00980000000 0x18206e004c000000

def z283 : W := mkw 0x0000000020900000 0x0000000001048000 0x0000000060f8000b 0x800000000307c000

def z284 : W := mkw 0x8000000076b1fb00 0x4c00000003b58fd8 0x0a0000007ff9ff9f 0x8050000003ffcffc

def z285 : W := mkw 0x20001012800004a1 0x0100008094000025 0x5802007f80181ffa 0xeac01003fc00c0ff

def z286 : W := mkw 0x0170157280000019 0x000b80ab94000000 0xf1f23fff80000000 0x7f8f91fffc000000

def z287 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x27edc0007ffe000f 0x813f6e0003fff000

def z288 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x827000701f001c04 0x0413800380f800e0

def z289 : W := mkw 0x02016800094e0000 0x30100b40004a7000 0x0401f80000060000 0x10200fc000003000

def z290 : W := mkw 0x042497ff8000001f 0x802124bffc000000 0xd0123fff80000000 0x7e8091fffc000000

def z291 : W := mkw 0xc4aff6df8c659257 0xae257fb6fc632c92 0xb66ffe4f9ce7927d 0xbdb37ff27ce73c93

def z292 : W := mkw 0xc004c20908648246 0x2600261048432412 0x340dc60980e78279 0xb9a06e304c073c13

def z293 : W := mkw 0x03fb2d60779b5818 0x581fd96b03bcdac0 0xfbf23ff07f19fc17 0xe7df91ff83f8cfe0

def z294 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xf5fdc7f000000000 0x67afee3f80000000

def z295 : W := mkw 0xc02487690421da5e 0x0e01243b48210ed2 0x080007f98001fe70 0x6040003fcc000ff3

def z296 : W := mkw 0x008e028c00000004 0x0004701460000000 0x000e000e00000000 0x0800700070000000

def z297 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xd473f87f80000000 0x7ea39fc3fc000000

def z298 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798c078060e1e013 0xe3cc603c03070f00

def z299 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0xb66ff8001cfe000d 0x9db37fc000e7f000

def z300 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x698e078660f9e183 0x434c703c3307cf0c

def z301 : W := mkw 0x07ffefed7bde001e 0xf03fff7f6bdef000 0xf7ffff807ffe000f 0x9fbffffc03fff000

def z302 : W := mkw 0x07dffa9ffbde0007 0xf03effd4ffdef000 0xf7fff80ffffe000f 0x9fbfffc07ffff000

def z303 : W := mkw 0x20000800010a04a0 0x1100004000085025 0x5802000e031e1ffe 0xeac010007018f0ff

def z304 : W := mkw 0x25db39b6810a04a9 0x912ed9cdb4085025 0xd99239ff831e1ffe 0xfecc91cffc18f0ff

def z305 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x080e078e00f9e398 0x6840703c7007cf1c

def z306 : W := mkw 0x8004020800208204 0x0400201040010410 0xb00c064980e7927d 0xbd8060324c073c93

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000004180061064 0x140000020c003083

def z308 : W := mkw 0x008a000020900000 0x0004500001048000 0x000e000000f80008 0x080070000007c000

def z309 : W := mkw 0x008e028c00000004 0x0004701460000000 0x798e078e6001e013 0xebcc703c73000f00

def z310 : W := mkw 0x0151200000000000 0x000a890000000000 0x8471f80000000000 0x14238fc000000000

def z311 : W := mkw 0x0551313280000009 0x802a898994000000 0x0010383000000000 0x000081c180000000

def z312 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x65ffffb600000000 0x432ffffdb0000000

def z313 : W := mkw 0x008a008420902100 0x0004500421048108 0x0180018060006000 0x000c000c03000300

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0x7180078000000000 0x638c003c00000000

def z315 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x867ff8001ffe000c 0x1c33ffc000fff000

def z316 : W := mkw 0x4170c5615e45585a 0x6a0b862b0af22ac2 0x8671c0719f061c64 0x14338e038cf830e3

def z317 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x300e060e00f98399 0xa98070307007cc1c

def z318 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff8006127c 0xffaffffffc003093

def z319 : W := mkw 0xc174c6495e659256 0x6e0ba6324af32c92 0xf7fdc649ffe7927f 0xbfbfee324fff3c93

def z320 : W := mkw 0xc5ffb7ff8421925f 0x8e2ffdbffc210c92 0xf5ffffff80019270 0x7faffffffc000c93

def z321 : W := mkw 0xc0aec6cd2cf5b356 0x2e0576366967ad9a 0xb7edc7c9fce7f27d 0xbdbf6e3e4fe73f93

def z322 : W := mkw 0xe024de5b8d6f96f7 0x3f0126f2dc6b7cb7 0xb66ffe4f9cff93fd 0xbdb37ff27ce7fc9f

def z323 : W := mkw 0x07fff7fffad4001f 0xe03fffbfffd6a000 0xf7fffffffce00001 0x7fbfffffffe70000

def z324 : W := mkw 0xc174c7695e65da5e 0x6e0ba63b4af32ed2 0xfffdc7f07fe1fc17 0xe7ffee3f83ff0fe0

def z325 : W := mkw 0x0000400008440000 0x2000020000422000 0x040dc00000e60008 0x18206e0000073000

def z326 : W := mkw 0x8000000020b0a300 0x0400000001058518 0x7980078060f9e39b 0xe3cc003c0307cf1c

def z327 : W := mkw 0x20201d72850b5cb9 0x190100eb94285ae5 0xd8123fff831ffffe 0xfec091fffc18ffff

def z328 : W := mkw 0x017487695601581e 0x480ba43b4ab00ac0 0xfffdc7f9ff01fc17 0xffffee3fcff80fe0

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x300c000000e00009 0x8980600000070000

def z330 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6001ce7927d 0x81336e3000e73c93

def z331 : W := mkw 0x03db68847bde2100 0x701edb4423def108 0xfffff9867ffe618f 0xdfffffcc33fff30c

def z332 : W := mkw 0x800000000020a300 0x0400000000010518 0x080000000001e390 0x0040000000000f1c

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002000e00180388 0x080010007000c01c

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x5800000000000012 0xe2c0000000000000

def z335 : W := mkw 0x0020056004015818 0x0801002b00200ac0 0xba6007f01c01fc15 0xe5d3003f80e00fe0

def z336 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xa5fdfff180000000 0x152fefff8c000000

def z337 : W := mkw 0x228b7812a9de04a1 0x31145bc0954ef025 0xdc1ff87f83fe1ffe 0xfee0ffc3fc1ff0ff

def z338 : W := mkw 0xc5fff7ff8c65925f 0xae2fffbffc632c92 0xf7ffffff9ce18001 0x7fbffffffce70c00

def z339 : W := mkw 0x83df6a8c7bfea304 0x741efb5463dff518 0xf7fff80e7ffe038f 0x9fbfffc073fff01c

def z340 : W := mkw 0x6020dc538d4f14f3 0x3b0106e29c6a78a7 0x8671f8719f061c64 0x14338fc38cf830e3

def z341 : W := mkw 0xa08e1a9ea1baa7a5 0x150470d4f50dd53d 0x799e3fbe63f9ef9b 0xebccf1fdf31fcf7c

def z342 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0x7d8fff8fe0f9e39b 0xfbec7ffc7f07cf1c

def z343 : W := mkw 0x0404929f80000007 0x80202494fc000000 0x0000000f80000000 0x000000007c000000

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x7982078e6019e39b 0xebcc103c7300cf1c

def z345 : W := mkw 0x828e4a8c7bfea304 0x7414725463dff518 0x7b8e078e7fffe39f 0xebdc703c73ffff1c

def z346 : W := mkw 0x25db39b6810a04a9 0x912ed9cdb4085025 0x499239b603180d82 0x424c91cdb018c06c

def z347 : W := mkw 0x07fbfd73fbde001b 0xf03fdfeb9fdef000 0xf7fff871fffe000f 0x9fbfffc38ffff000

def z348 : W := mkw 0x07db79b6fbde0009 0xf03edbcdb7def000 0xf7fff9b67ffe000f 0xdfbfffcdb3fff000

def z349 : W := mkw 0x8004020800208204 0x0400201040010410 0x200c060000e18001 0x0100603000070c00

def z350 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf99e07fe63f9ff9f 0xefccf03ff31fcffc

def z351 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0xd41ff80003fe000e 0x9ea0ffc0001ff000

def z352 : W := mkw 0x21701d72d70b5cb9 0x590b80eb96b85ae5 0xfbf03ff1ff07fc77 0xf7df81ff8ff83fe3

def z353 : W := mkw 0x0000400008440000 0x2000020000422000 0x020000001ce6000d 0x8010000000e73000

def z354 : W := mkw 0x0024864904011016 0x0801243248200880 0xb66dc6499c019015 0xbdb36e324ce00c80

def z355 : W := mkw 0xc02044400c659250 0x2e01022200632c92 0xb26006401ce7927d 0xa593003200e73c93

def z356 : W := mkw 0x01701572d6015819 0x480b80ab96b00ac0 0xfbf23fffff01fc17 0xffdf91fffff80fe0

def z357 : W := mkw 0x0000101280000001 0x0000008094000000 0x8010387180000000 0x140081c38c000000

def z358 : W := mkw 0x0024864900000016 0x0001243248000000 0xb46dc6498006127c 0xbda36e324c003093

def z359 : W := mkw 0x20000800010a04a0 0x1100004000085025 0xd8100070031e1ffe 0xe6c080038018f0ff

def z360 : W := mkw 0x07db39b6f39a0009 0xd03ed9cdb79cd000 0x419239b663180002 0x420c91cdb318c000

def z361 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0x9661c0499c06127c 0xbcb30e024ce03093

def z362 : W := mkw 0x020040007ad40000 0x6010020003d6a000 0x020000007ce00001 0x0010000003e70000

def z363 : W := mkw 0x0170056004011018 0x080b802b00200880 0xf3f007f01c019015 0xe79f803f80e00c80

def z364 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x7be007807c01e013 0xe3df003c03e00f00

def z365 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6499ce19271 0x21336e324ce70c93

def z366 : W := mkw 0x00000800010a0000 0x1000004000085000 0x4012380003180002 0x020091c00018c000

def z367 : W := mkw 0x8004028c0020a304 0x0400201460010518 0x0000000e00000380 0x000000007000001c

def z368 : W := mkw 0x20001012800004a1 0x0100008094000025 0x9800007f80061ffc 0xfcc00003fc0030ff

def z369 : W := mkw 0xa004129e8020a7a5 0x05002094f401053d 0x080007ff8001fff0 0x6040003ffc000fff

def z370 : W := mkw 0x01fe07ec5601581c 0x480ff03f62b00ac0 0xfbfe07fe7f01fc17 0xefdff03ff3f80fe0

def z371 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xfffff8007ffe1fff 0x9fffffc003fff0ff

def z372 : W := mkw 0x03db2800739a0000 0x501ed940039cd000 0xf3f238007f180007 0x879f91c003f8c000

def z373 : W := mkw 0xc024ce490d6f9256 0x3e012672486b7c92 0xf67ffe499fff927f 0xbfb3fff24cfffc93

def z374 : W := mkw 0x85ffa7ed20b0a31e 0x842ffd3f69058518 0x25edc78060e1e001 0x012f6e3c03070f00

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000980060268 0x180000004c003013

def z376 : W := mkw 0x4371ec415f4f1052 0x7a1b8f620afa7882 0x8671f8419f061064 0x14338fc20cf83083

def z377 : W := mkw 0x808e129ea0b0a305 0x04047094f5058518 0xf99e3fffe0f9e39b 0xffccf1ffff07cf1c

def z378 : W := mkw 0xc0ae86cd24b1b356 0x0e05743669258d9a 0x798e07cfe0f9f3fb 0xebcc703e7f07cf9f

def z379 : W := mkw 0x0170056000000018 0x000b802b00000000 0x8070007000000000 0x0403800380000000

def z380 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x218e078e60f9e389 0x090c703c7307cf1c

def z381 : W := mkw 0x808e0a8c21baa304 0x14047054610dd518 0xf99e3f8e63ffe39f 0xffccf1fc731fff1c

def z382 : W := mkw 0x0020056004015818 0x0801002b00200ac0 0x000007800001e000 0x0000003c00000f00

def z383 : W := mkw 0x02000800739a0000 0x50100040039cd000 0x0000000063180002 0x000000000318c000

def z384 : W := mkw 0x242497ff800004bf 0x812124bffc000025 0x080007ff80001ff0 0x6040003ffc0000ff

def z385 : W := mkw 0xc3ffee497fff9256 0x7e1fff724bfffc92 0xf7fffe007fff800f 0x9fbffff003fffc00

def z386 : W := mkw 0x23517812db4e04a1 0x711a8bc096da7025 0xde73f87f9f1e1ffe 0xfef39fc3fcf8f0ff

def z387 : W := mkw 0x0170056052000018 0x400b802b02900000 0xf3f007f07f000007 0xe79f803f83f80000

def z388 : W := mkw 0x0170056000000018 0x000b802b00000000 0xf9f007f06001e013 0xe7cf803f83000f00

def z389 : W := mkw 0x028b600028d40000 0x20145b000146a000 0x040dc00000e00000 0x00206e0000070000

def z390 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xffedc7c9fce7f27f 0xffff6e3e4fe73f93

def z391 : W := mkw 0x020048007fdf5800 0x7810024003fefac0 0x0a0000007ffffc1f 0x8050000003ffffe0

def z392 : W := mkw 0x81fe07ec76b1fb1c 0x4c0ff03f63b58fd8 0xfbfc07f07fe1fc17 0xe7dfe03f83ff0fe0

def z393 : W := mkw 0x20201c52850b14b1 0x190100e2942858a5 0xfa723e7f9f1f9fff 0xffd391f3fcf8fcff

def z394 : W := mkw 0xc004c20908648246 0x2600261048432412 0xb66dc0099ce6026d 0x9db36e004ce73013

def z395 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0xf7f1f8007f060007 0x97bf8fc003f83000

def z396 : W := mkw 0xa08e1a9ea1baa7a5 0x150470d4f50dd53d 0xd81e387f83fe1ffe 0xfec0f1c3fc1ff0ff

def z397 : W := mkw 0x828f6a8c29fea304 0x34147b54614ff518 0x7d8fff8e60ffe39b 0xfbec7ffc7307ff1c

def z398 : W := mkw 0x0020044004011010 0x0801002200200880 0x826000401c001004 0x0413000200e00080

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000060000018011 0xa180003000000c00

def z400 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x2be007807f01fc17 0x815f003c03f80fe0

def z401 : W := mkw 0xc17487695621da5e 0x4e0ba43b4ab10ed2 0xfbf007f9ff01fe77 0xe7df803fcff80ff3

def z402 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x67fff8007ff80003 0x033fffc003ffc000

def z403 : W := mkw 0xc1ffe6490c659256 0x2e0fff3248632c92 0xf7fffe499ce7927d 0xbfbffff24ce73c93

def z404 : W := mkw 0x8004020820b0a304 0x0400201041058518 0x380c060860f9e39b 0xa9c060304307cf1c

def z405 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0x0661c0001c000000 0x00330e0000e00000

def z406 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f9ff07fe7f 0xffdf803fcff83ff3

def z407 : W := mkw 0x008a000020900000 0x0004500001048000 0x798e078060f9e01b 0xebcc703c0307cf00

def z408 : W := mkw 0x0020044004011010 0x0801002200200880 0xfbe007c07c01f017 0xe7df003e03e00f80

def z409 : W := mkw 0x0170056004015818 0x080b802b00200ac0 0xf9f007f00001fc10 0x67cf803f80000fe0

def z410 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xf3f007f01f001c04 0x679f803f80f800e0

def z411 : W := mkw 0x21701d72810a04b9 0x110b80eb94085025 0xf9f23fff831e1ffe 0xffcf91fffc18f0ff

def z412 : W := mkw 0x048b309680000001 0x80245984b4000000 0x0002380600000000 0x000011c030000000

def z413 : W := mkw 0x05db31b6d2004809 0xc02ed98db6900240 0x499239b663006c02 0x424c91cdb3180360

def z414 : W := mkw 0x0020844100000012 0x0001042208000000 0x8461c04180000000 0x14230e020c000000

def z415 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd812387603181d96 0xe6c091c3b018c0ec

def z416 : W := mkw 0x6020dc538d4f14f3 0x3b0106e29c6a78a7 0xde73f87f9f1e1ffe 0xfef39fc3fcf8f0ff

def z417 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x6bf007b07f01ec03 0x435f803d83f80f60

def z418 : W := mkw 0x20000800010a04a0 0x1100004000085025 0x0800000003180d82 0x004000000018c06c

def z419 : W := mkw 0x8004020800208204 0x0400201040010410 0x0000060800018210 0x2000003040000c10

def z420 : W := mkw 0x0020044004011010 0x0801002200200880 0x0000064000019010 0x2000003200000c80

def z421 : W := mkw 0x0150012052004808 0x400a800902900240 0x0180018060006000 0x000c000c03000300

def z422 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd810387183061c76 0xf6c081c38c1830e3

def z423 : W := mkw 0x03db2920739a4808 0x501ed949039cd240 0x499239b063186c02 0x424c91cd8318c360

def z424 : W := mkw 0xc00040000c659240 0x2e00020000632c92 0xb66dc0001ce7927d 0x9db36e0000e73c93

def z425 : W := mkw 0xc000000004219240 0x0e00000000210c92 0x0000000000019270 0x0000000000000c93

def z426 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xda7000701f001c16 0xe6d3800380f800e0

def z427 : W := mkw 0x0150000000000000 0x000a800000000000 0xf1f0000000000000 0x078f800000000000

def z428 : W := mkw 0xc3ffef697fffda5e 0x7e1fff7b4bfffed2 0xfffffff9fffffe7f 0xffffffffcffffff3

def z429 : W := mkw 0x228b7812a9de04a1 0x31145bc0954ef025 0x040ff80f80fe03e8 0x18207fc07c07f01f

def z430 : W := mkw 0x057497ffd601581f 0xc82ba4bffeb00ac0 0xfbf007ffff01fc17 0xe7df803ffff80fe0

def z431 : W := mkw 0x05db21a400000008 0x802ed90d20000000 0x0180018000000000 0x000c000c00000000

def z432 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0002380600180180 0x000011c03000c00c

def z433 : W := mkw 0x400040000c451040 0x2a00020000622882 0x020000001c061064 0x0010000000e03083

def z434 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6099ce78269 0x19336e304ce73c13

def z435 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x5802380f801e03fa 0xfac011c07c00f01f

def z436 : W := mkw 0x21701572d6015cb9 0x490b80ab96b00ae5 0xfbf007ffff01fff7 0xe7df803ffff80fff

def z437 : W := mkw 0x008a000020900000 0x0004500001048000 0x218c000060e00001 0x010c600003070000

def z438 : W := mkw 0xe024965b842196f7 0x0f0124b2dc210cb7 0x0800067f80019ff0 0x60400033fc000cff

def z439 : W := mkw 0x8004028c0020a304 0x0400201460010518 0x380c078e00e1e399 0xe9c0603c70070f1c

def z440 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xfe6fc64f9cff93ff 0xfff37e327ce7fc9f

def z441 : W := mkw 0x03716d605f4f5818 0x781b8b6b02fa7ac0 0x8671f8701f061c04 0x14338fc380f830e0

def z442 : W := mkw 0x05db31b6a0902109 0x802ed98db5048108 0x499239b660186182 0x424c91cdb300c30c

def z443 : W := mkw 0x008a0800219a0000 0x10045040010cd000 0xf19e380063fe000f 0x9f8cf1c0031ff000

def z444 : W := mkw 0x03fb6d607bde0018 0x701fdb6b03def000 0xf7fffff07ffe000f 0xffbfffff83fff000

def z445 : W := mkw 0x20005812894e04a1 0x310002c0944a7025 0xfe7ff87f9ffe1fff 0xfff3ffc3fcfff0ff

def z446 : W := mkw 0x015040005a440000 0x600a820002d22000 0xf7fdc0007fe6000f 0x9fbfee0003ff3000

def z447 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0xfff1fff1ff01fc17 0xf7ff8fff8ff80fe0

def z448 : W := mkw 0x05ffbfff810a001f 0x902ffdfffc085000 0xf5ffffff831e000e 0xffaffffffc18f000

def z449 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x040dc64980e79278 0x38206e324c073c93

def z450 : W := mkw 0x83df6a087bfe8204 0x741efb5043dff410 0xf7fffe087fff821f 0xbfbffff043fffc10

def z451 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x5812383e03180f9a 0xeac091c1f018c07c

def z452 : W := mkw 0x87fffffffbfea31f 0xf43fffffffdff518 0xffffffffffffe39f 0xffffffffffffff1c

def z453 : W := mkw 0x0000101280000001 0x0000008094000000 0x4012383600000000 0x420091c1b0000000

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000004980001270 0x200000024c000093

def z455 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0802380f831e1ffe 0x984011c07c18f0ff

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000003001c16 0x80400000001800e0

def z457 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd8123836031e0d8e 0xdec091c1b018f06c

def z458 : W := mkw 0x20001012800004a1 0x0100008094000025 0x0000007180001c60 0x000000038c0000e3

def z459 : W := mkw 0x4020844104011052 0x0a01042208200882 0x0000004180001060 0x000000020c000083

def z460 : W := mkw 0x00000800010a0000 0x1000004000085000 0xd0123849831e127e 0xbe8091c24c18f093

def z461 : W := mkw 0x0000000052000000 0x4000000002900000 0x020000007f000007 0x8010000003f80000

def z462 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x8810387f83061ff4 0x744081c3fc1830ff

def z463 : W := mkw 0x05fb35f680000019 0x802fd9afb4000000 0xf1f23ff600000000 0x678f91ffb0000000

def z464 : W := mkw 0xa1fe1ffef7bbffbd 0x5d0ff0fff7bddffd 0xfbfe3fffffffffff 0xffdff1ffffffffff

def z465 : W := mkw 0x01db200000000000 0x000ed90000000000 0x4192380000000000 0x020c91c000000000

def z466 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x4812387f83181ff2 0x624091c3fc18c0ff

def z467 : W := mkw 0x208a1896a19a25a1 0x110450c4b50cd12d 0xd99239ffe31e7ffe 0xfecc91cfff18f3ff

def z468 : W := mkw 0x0000400008440000 0x2000020000422000 0xb66dc0499ce6127d 0xbdb36e024ce73093

def z469 : W := mkw 0x0000101280000001 0x0000008094000000 0xd012387f8006127c 0xfe8091c3fc003093

def z470 : W := mkw 0x01fa05e476917918 0x480fd02f23b48bc8 0xfbf207f67f19fd97 0xe7df903fb3f8cfec

def z471 : W := mkw 0x07ffffffffdf581f 0xf83ffffffffefac0 0xfffffffffffffc1f 0xffffffffffffffe0

def z472 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xf7fdc0007fe00007 0x87bfee0003ff0000

def z473 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xc8123877831e1de6 0x564091c3bc18f0ef

def z474 : W := mkw 0x81de03ac72b0eb0c 0x440ef01d63958758 0x799e07be63f9ef9b 0xebccf03df31fcf7c

def z475 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xb27006701f019c15 0xa593803380f80ce0

def z476 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x298c078060f9e39b 0x814c603c0307cf1c

def z477 : W := mkw 0x85ffa7ed20b0a31e 0x842ffd3f69058518 0x7defc78e60f9e39b 0xebef7e3c7307cf1c

def z478 : W := mkw 0xc08ec28d28f4a346 0x260476146947a51a 0x040fc00f80fe03e8 0x18207e007c07f01f

def z479 : W := mkw 0x0000000056015800 0x4800000002b00ac0 0x020000007c01e001 0x0010000003e00f00

def z480 : W := mkw 0x01db2800010a0000 0x100ed94000085000 0xf5fff800031e000e 0x9fafffc00018f000

def z481 : W := mkw 0x03ffee497bde0016 0x701fff724bdef000 0xf7fffe49fffe000f 0xbfbffff24ffff000

def z482 : W := mkw 0xc024864904219256 0x0e01243248210c92 0xb26006499c019275 0xa59300324ce00c93

def z483 : W := mkw 0x008e028c20900004 0x0004701461048000 0x718e078e60f8000b 0xeb8c703c7307c000

def z484 : W := mkw 0x01700d60570b5818 0x580b806b02b85ac0 0xfbf23ff07f1ffc1f 0xffdf91ff83f8ffe0

def z485 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x718e078e00f80388 0x6b8c703c7007c01c

def z486 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xf3f007807f01e007 0x879f803c03f80f00

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0xd812007e03181f9e 0xeec09003f018c0fc

def z488 : W := mkw 0x0170056000000018 0x000b802b00000000 0x21e0078000000000 0x010f003c00000000

def z489 : W := mkw 0x00000800010a0000 0x1000004000085000 0x00023800001e0008 0x180011c00000f000

def z490 : W := mkw 0x808e028c0020a304 0x0404701460010518 0x798e078e0001e390 0x6bcc703c70000f1c

def z491 : W := mkw 0x01fa056076915818 0x480fd02b03b48ac0 0xfbfe07f07ff9fc1f 0xefdff03f83ffcfe0

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000006127c 0x8000000000003093

def z493 : W := mkw 0x0004020800000004 0x0000201040000000 0x300c060800000000 0x2980603040000000

def z494 : W := mkw 0x008a008420902100 0x0004500421048108 0x5982018e6018639a 0xeacc100c7300c31c

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x500200000018000a 0x8a8010000000c000

def z496 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6401ce19015 0xa5b36e3200e70c80

def z497 : W := mkw 0x8004020800208204 0x0400201040010410 0x780e060e00f9839b 0xebc070307007cc1c

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0xd012380000000000 0x1e8091c000000000

def z499 : W := mkw 0x0170056052004818 0x400b802b02900240 0xf9f007f063006c02 0x67cf803f83180360

def z500 : W := mkw 0x81fe07ec20b0a31c 0x040ff03f61058518 0xf9fe07fe60f9e39b 0xefcff03ff307cf1c

def z501 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x88103871831e1ffe 0x944081c38c18f0ff

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x4810003003000c02 0x4240800180180060

def z503 : W := mkw 0x0020056004015818 0x0801002b00200ac0 0x0000007000001c00 0x00000003800000e0

def z504 : W := mkw 0x03db68005b4e0000 0x701edb4002da7000 0xf7fff8001f060004 0x1fbfffc000f83000

def z505 : W := mkw 0xe0aededfadffb7f7 0x3f0576f6fd6ffdbf 0xffffffffffffffff 0xffffffffffffffff

def z506 : W := mkw 0x0150012056015808 0x480a800902b00ac0 0x4b9001b07f01fc17 0xc25c800d83f80fe0

def z507 : W := mkw 0xc0aec6cd2cf5b356 0x2e0576366967ad9a 0x27edc7807ce1e001 0x013f6e3c03e70f00

def z508 : W := mkw 0x808e028c76b1fb04 0x4c04701463b58fd8 0x7b8e078e7ff9ff9f 0xebdc703c73ffcffc

def z509 : W := mkw 0x0020056004015818 0x0801002b00200ac0 0x798007f06001fc13 0xe3cc003f83000fe0

def z510 : W := mkw 0x017045605e455818 0x680b822b02f22ac0 0xfffdc7f07fe7fc1f 0xffffee3f83ff3fe0

def z511 : W := mkw 0x03df6a8c7bde0004 0x701efb5463def000 0xf7ffff8e7ffe000f 0xffbffffc73fff000

def z512 : W := mkw 0xc0aec6cd2cf5b356 0x2e0576366967ad9a 0x7fefc78e7cf9e39b 0xebff7e3c73e7cf1c

def z513 : W := mkw 0x01db200000000000 0x000ed90000000000 0x25edc00000000000 0x012f6e0000000000

def z514 : W := mkw 0x00001812810a0001 0x100000c094085000 0xd012387f831e000e 0xfe8091c3fc18f000

def z515 : W := mkw 0x008a000020900000 0x0004500001048000 0x4182000060180002 0x020c10000300c000

def z516 : W := mkw 0x0020044056015810 0x4801002202b00ac0 0xba6006407f01fc17 0xa5d3003203f80fe0

def z517 : W := mkw 0x25ffbfff810a04bf 0x912ffdfffc085025 0xf5ffffff801e03e8 0x7faffffffc00f01f

def z518 : W := mkw 0x20000000000004a0 0x0100000000000025 0x0800000000001ff0 0x00400000000000ff

def z519 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x718e078060f9e00b 0x8b8c703c0307cf00

def z520 : W := mkw 0x03db2800739a0000 0x501ed940039cd000 0xd1923800631e000e 0x9e8c91c00318f000

def z521 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x459ff80063fe000a 0x1a2cffc0031ff000

def z522 : W := mkw 0x8004028c20b0a304 0x0400201461058518 0x0800078e60f9e39b 0xe040003c7307cf1c

def z523 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0000380180060060 0x100001c00c003003

def z524 : W := mkw 0xc424d7ff8c65925f 0xae2126bffc632c92 0xb66dc7ff9ce7927d 0xfdb36e3ffce73c93

def z525 : W := mkw 0x0020056004015818 0x0801002b00200ac0 0xd81007f00301fc16 0xe6c0803f80180fe0

def z526 : W := mkw 0xc5fff7ffde65da5f 0xee2fffbffef32ed2 0xffffffffffe7fe7f 0xffffffffffff3ff3

def z527 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x080e000e60f9e39b 0x884070007307cf1c

def z528 : W := mkw 0x802407ec0421fb1c 0x0c01203f60210fd8 0x080007fe0001ff90 0x6040003ff0000ffc

def z529 : W := mkw 0x23db7812fbde04a1 0x711edbc097def025 0xfffff8367ffe0d8f 0xdfffffc1b3fff06c

def z530 : W := mkw 0x0170044056011010 0x480b802202b00880 0xf3f006407f019017 0xa79f803203f80c80

def z531 : W := mkw 0x83db68007bfea300 0x741edb4003dff518 0xfffff8007fffe39f 0x9fffffc003ffff1c

def z532 : W := mkw 0xc17045605e65da58 0x6e0b822b02f32ed2 0xfbf007f07fe7fe7f 0xe7df803f83ff3ff3

def z533 : W := mkw 0x07ffffffdb4e001f 0xf03ffffffeda7000 0xf7ffffff9f060004 0x7fbffffffcf83000

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x7180000060000003 0x838c000003000000

def z535 : W := mkw 0x05ffa7ed5601581e 0xc82ffd3f6ab00ac0 0x27edc7807c01e001 0x013f6e3c03e00f00

def z536 : W := mkw 0x8004020800208204 0x0400201040010410 0x000c000800e00208 0x0800600040070010

def z537 : W := mkw 0xc7ffffffffff925f 0xfe3ffffffffffc92 0xf7ffffffffff927f 0xffbffffffffffc93

def z538 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0010383003000c00 0x000081c180180060

def z539 : W := mkw 0x80ae06cc24b1b314 0x0c05703661258d98 0xfbee07ce7cf9f39f 0xefdf703e73e7cf9c

def z540 : W := mkw 0xc3db68007fff9240 0x7e1edb4003fffc92 0xf7fff8007fff927f 0x9fbfffc003fffc93

def z541 : W := mkw 0x068ffa9fa9de0007 0xb0347fd4fd4ef000 0x040ff80f80fe0008 0x18207fc07c07f000

def z542 : W := mkw 0xc024c6492cf5b356 0x2e0126324967ad9a 0xbe6dc649fcfff3ff 0xbdf36e324fe7ff9f

def z543 : W := mkw 0x0771fd73db4e001b 0xf03b8feb9eda7000 0x8671f8719f060004 0x14338fc38cf83000

def z544 : W := mkw 0xc00040002cf5b340 0x2e0002000167ad9a 0x0a0000007cfff3ff 0x8050000003e7ff9f

def z545 : W := mkw 0x27fffffffbde04bf 0xf13fffffffdef025 0xfffffffffffe1fff 0xfffffffffffff0ff

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0xd010000003000006 0x8680800000180000

def z547 : W := mkw 0xc174c7695e65da5e 0x6e0ba63b4af32ed2 0xb7edc7c9fce7f27d 0xbdbf6e3e4fe73f93

def z548 : W := mkw 0x0000400008440000 0x2000020000422000 0x266dc0001ce00001 0x01336e0000e70000

def z549 : W := mkw 0x03db200072900000 0x401ed90003948000 0x0180000060000000 0x000c000003000000

def z550 : W := mkw 0xc224ce497fff9256 0x7e1126724bfffc92 0xb66dc649ffff927f 0xbdb36e324ffffc93

def z551 : W := mkw 0x4571f5738c45105b 0xaa2b8fab9c622882 0x8671f8719c061064 0x14338fc38ce03083

def z552 : W := mkw 0xe00058128d6f96e1 0x3f0002c0946b7cb7 0xda12387f9fff9fff 0xfed091c3fcfffcff

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x4802000600180182 0x424010003000c00c

def z554 : W := mkw 0x008e129e80000005 0x00047094f4000000 0xf19e3fff80000000 0x7f8cf1fffc000000

def z555 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0800007f831e1ffe 0xe0400003fc18f0ff

def z556 : W := mkw 0x8170056076b1fb18 0x4c0b802b03b58fd8 0xfbf007f07ff9ff9f 0xe7df803f83ffcffc

def z557 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0x459ff9bf80000000 0x5a2cffcdfc000000

def z558 : W := mkw 0x808e428c28f4a304 0x240472146147a518 0xffefc78e7cffe39f 0xffff7e3c73e7ff1c

def z559 : W := mkw 0xa0001812a1baa7a1 0x150000c0950dd53d 0xd812387fe3ffffff 0xfec091c3ff1fffff

def z560 : W := mkw 0x248fba9f810a04a7 0x91247dd4fc085025 0x040ff80f801e03e8 0x18207fc07c00f01f

def z561 : W := mkw 0x8024064804219214 0x0c01203240210c90 0xb26c06481ce1921d 0xad93603240e70c90

def z562 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6001ce7800d 0x9db36e3000e73c00

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0xd802004f801e13fe 0xfec010027c00f09f

def z564 : W := mkw 0xc024864904219256 0x0e01243248210c92 0x0000060000018000 0x0000003000000c00

def z565 : W := mkw 0x01df228c00000004 0x000ef91460000000 0xf5ffff8e00000000 0x7faffffc70000000

def z566 : W := mkw 0xc48ff29f88648247 0xa6247f94fc432412 0x040ff80f80e60268 0x18207fc07c073013

def z567 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0x75efc78e00000000 0x6baf7e3c70000000

def z568 : W := mkw 0x07ffe7ed7ad4001e 0xe03fff3f6bd6a000 0x27edc7807ce00001 0x013f6e3c03e70000

def z569 : W := mkw 0x01db600008440000 0x200edb0000422000 0xf7fff8001ce6000d 0x9fbfffc000e73000

def z570 : W := mkw 0x0150012052004808 0x400a800902900240 0xd99001f063007c16 0xe6cc800f831803e0

def z571 : W := mkw 0x817407ec5621fb1c 0x4c0ba03f62b10fd8 0xfbf007fe7f01ff97 0xe7df803ff3f80ffc

def z572 : W := mkw 0xc024864904219256 0x0e01243248210c92 0x900006498007927c 0xbc8000324c003c93

def z573 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x000c000000e00000 0x0000600000070000

def z574 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x4982078e6019e392 0x624c103c7300cf1c

def z575 : W := mkw 0x81fe07ec76b1fb1c 0x4c0ff03f63b58fd8 0x23ec07807ce1e001 0x011f603c03e70f00

def z576 : W := mkw 0x84ae97ffa0b0a31f 0x842574bffd058518 0x798e07ffe0f9e39b 0xebcc703fff07cf1c

def z577 : W := mkw 0x008e028c00000004 0x0004701460000000 0x218c078000000000 0x010c603c00000000

def z578 : W := mkw 0x80ae86cd20b0a316 0x0405743669058518 0xfdefc7cfe0f9e39b 0xffef7e3e7f07cf1c

def z579 : W := mkw 0x83df2a8c73baa304 0x541ef954639dd518 0x799e3f8e63f9e39b 0xebccf1fc731fcf1c

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x080007800001e010 0x6040003c00000f00

def z581 : W := mkw 0x208a1896a19a25a1 0x110450c4b50cd12d 0x499239b663186d82 0x424c91cdb318c36c

def z582 : W := mkw 0xa08e1a9ea1baa7a5 0x150470d4f50dd53d 0x000e380f80fe03e8 0x180071c07c07f01f

def z583 : W := mkw 0x0000101280000001 0x0000008094000000 0x0000007f80000000 0x60000003fc000000

def z584 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x4812383f831e0fea 0x5a4091c1fc18f07f

def z585 : W := mkw 0x020048007bde0000 0x7010024003def000 0xd21238007ffe000f 0x9e9091c003fff000

def z586 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6499ce18001 0x3db36e324ce70c00

def z587 : W := mkw 0xe004da1b896e86e7 0x370026d0dc4b7437 0x040ff80f80fe03e8 0x18207fc07c07f01f

def z588 : W := mkw 0xc004820900208246 0x0600241048010412 0x0000000980000260 0x000000004c000013

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0xd810007983061e7e 0xfec08003cc1830f3

def z590 : W := mkw 0x0150000052000000 0x400a800002900000 0x23e000007c000001 0x011f000003e00000

def z591 : W := mkw 0xe0249e5b852b96f7 0x1f0124f2dc295cb7 0xd8123e7f831f9ffe 0xfec091f3fc18fcff

def z592 : W := mkw 0x20001812d70b5ca1 0x590000c096b85ae5 0xda12387fff1fffff 0xfed091c3fff8ffff

def z593 : W := mkw 0x00ae86cd00000016 0x0005743668000000 0xf5efc7cf80000000 0x7faf7e3e7c000000

def z594 : W := mkw 0x01500800530a0000 0x500a804002985000 0xf3f238007f1e000f 0x9f9f91c003f8f000

def z595 : W := mkw 0xc004c20908648246 0x2600261048432412 0x040dc00000e00000 0x00206e0000070000

def z596 : W := mkw 0x057497ff8000001f 0x802ba4bffc000000 0xf1f007ff80000000 0x678f803ffc000000

def z597 : W := mkw 0x2020157284015cb9 0x090100ab94200ae5 0x080007ff8001fff0 0x6040003ffc000fff

def z598 : W := mkw 0x008a000020900000 0x0004500001048000 0x798e000e60f8039b 0xebcc70007307c01c

def z599 : W := mkw 0x0150000052000000 0x400a800002900000 0x827000001f000004 0x0413800000f80000

def z600 : W := mkw 0x002044400c451010 0x2801022200622880 0xb66dc6401ce7901d 0xbdb36e3200e73c80

def z601 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x25edc7ff80000000 0x612f6e3ffc000000

def z602 : W := mkw 0x0020044000000010 0x0001002200000000 0xb060064000000000 0x2583003200000000

def z603 : W := mkw 0xc004c20908648246 0x2600261048432412 0x940dc04980e6127c 0xbca06e024c073093

def z604 : W := mkw 0x03fb6d607fdf5818 0x781fdb6b03fefac0 0xf7fff8707ffe1c0f 0x9fbfffc383fff0e0

def z605 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd012380f831e03ee 0x9e8091c07c18f01f

def z606 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xf3f000707f001c07 0x879f800383f800e0

def z607 : W := mkw 0xc1fec7ed7ef5fb5e 0x6e0ff63f6bf7afda 0xffffc7ffffffffff 0xfffffe3fffffffff

def z608 : W := mkw 0x25ffbfff810a04bf 0x912ffdfffc085025 0xfdffffff83180d82 0x7feffffffc18c06c

def z609 : W := mkw 0xc174c7690c65925e 0x2e0ba63b48632c92 0xf7fdc7f99ce7927d 0xffbfee3fcce73c93

def z610 : W := mkw 0x21501932d30a4ca9 0x510a80c996985265 0xd99239ffe31e7ffe 0xfecc91cfff18f3ff

def z611 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x020006499ce7927d 0xa01000324ce73c93

def z612 : W := mkw 0xa3df7a9efbfea7a5 0x751efbd4f7dff53d 0xffffffffffffffff 0xffffffffffffffff

def z613 : W := mkw 0x07ffbffff39a001f 0xd03ffdffff9cd000 0xf5ffffffe3180002 0x7fafffffff18c000

def z614 : W := mkw 0x83df6a8c7bfea304 0x741efb5463dff518 0xf7ffff807fffe00f 0x9fbffffc03ffff00

def z615 : W := mkw 0xc2afee492dff9256 0x3e157f72496ffc92 0xb66ffe499cff927d 0xbdb37ff24ce7fc93

def z616 : W := mkw 0x00000800010a0000 0x1000004000085000 0x8010380003060004 0x140081c000183000

def z617 : W := mkw 0x042487ed0000001e 0x8021243f68000000 0x0000078000000000 0x0000003c00000000

def z618 : W := mkw 0x0000000056015800 0x4800000002b00ac0 0xda1000707f01fc17 0xe6d0800383f80fe0

def z619 : W := mkw 0xc08e428c2cf5b344 0x2e0472146167ad9a 0x7b8e078e7cfff3ff 0xebdc703c73e7ff9f

def z620 : W := mkw 0x0020044004011010 0x0801002200200880 0x226006001c018001 0x0113003000e00c00

def z621 : W := mkw 0x0024864900000016 0x0001243248000000 0x0000064980000000 0x200000324c000000

def z622 : W := mkw 0x0571a5610000001a 0x802b8d2b08000000 0x0461c00000000000 0x00230e0000000000

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000004980000000 0x3c8000024c000000

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000018039a 0x804000000000c01c

def z625 : W := mkw 0xc3dfea097bfe8246 0x761eff504bdff412 0xf7fff809fffe026f 0x9fbfffc04ffff013

def z626 : W := mkw 0x0170056000000018 0x000b802b00000000 0xf9f007f003001c16 0xe7cf803f801800e0

def z627 : W := mkw 0x00000800010a0000 0x1000004000085000 0xd8123870031e1c1e 0xfec091c38018f0e0

def z628 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x580e000e00f8039a 0xeac070007007c01c

def z629 : W := mkw 0x020048007bde0000 0x7010024003def000 0xb66dc0007ffe000f 0x9db36e0003fff000

def z630 : W := mkw 0x03db2800739a0000 0x501ed940039cd000 0xf5fff80063180002 0x1fafffc00318c000

def z631 : W := mkw 0xe024de5b8d6f96f7 0x3f0126f2dc6b7cb7 0xb67dfe799fe79e7d 0xbdb3eff3ccff3cf3

def z632 : W := mkw 0x8000000000208200 0x0400000000010410 0x0000000000e18219 0x8000000000070c10

def z633 : W := mkw 0x0020044004011010 0x0801002200200880 0xb26006499c07927d 0xbd9300324ce03c93

def z634 : W := mkw 0x05ffa7ed5601581e 0xc82ffd3f6ab00ac0 0xfffdc7f07f01fc17 0xe7ffee3f83f80fe0

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x5002000e00000000 0x6a80100070000000

def z636 : W := mkw 0x03fb65607ed55818 0x681fdb2b03f6aac0 0xfffdc7f07fe1fc17 0xe7ffee3f83ff0fe0

def z637 : W := mkw 0x20249e5b810a04b7 0x110124f2dc085025 0xfc7ffe7f831e1ffe 0xffe3fff3fc18f0ff

def z638 : W := mkw 0x23db7812fbde04a1 0x711edbc097def025 0xf7fff871fffe1c6f 0x9fbfffc38ffff0e3

def z639 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x2be007f07c01fc11 0x615f003f83e00fe0

def z640 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x8661c6499c079274 0x34330e324ce03c93

def z641 : W := mkw 0x23db3812f39a04a1 0x511ed9c0979cd025 0xd992387fe31e1ffe 0xfecc91c3ff18f0ff

def z642 : W := mkw 0x8000000020b0a300 0x0400000001058518 0x0000000060e1e001 0x0000000003070f00

def z643 : W := mkw 0x0000000020902100 0x0000000001048108 0x0800000060186182 0x004000000300c30c

def z644 : W := mkw 0x4170c5615e45585a 0x6a0b862b0af22ac2 0xfff1c7f1ff07fc77 0xf7ff8e3f8ff83fe3

def z645 : W := mkw 0x83ff6fec7ffffb1c 0x7c1ffb7f63ffffd8 0xfffffffe7fffff9f 0xfffffffff3fffffc

def z646 : W := mkw 0xc3ffe6497ef59256 0x6e1fff324bf7ac92 0xb7edc649fce7927d 0xbdbf6e324fe73c93

def z647 : W := mkw 0x21501932d30a4ca9 0x510a80c996985265 0x499239b663186d82 0x424c91cdb318c36c

def z648 : W := mkw 0x2571bd73810a04bb 0x912b8deb9c085025 0x8471f87183061c64 0x14238fc38c1830e3

def z649 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x0802387f801e1ff8 0x784011c3fc00f0ff

def z650 : W := mkw 0xc5ffe7ed0c65925e 0xae2fff3f68632c92 0xb7edc7c99ce7927d 0xbdbf6e3e4ce73c93

def z651 : W := mkw 0xc0aec6492cf59256 0x2e0576324967ac92 0xf7efc649fcff927f 0xbfbf7e324fe7fc93

def z652 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x366dc6081ce18219 0xa9b36e3040e70c10

def z653 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x8a7007f01f01fc14 0x6453803f80f80fe0

def z654 : W := mkw 0x20000800010a04a0 0x1100004000085025 0x98000049831e1ffe 0xbcc000024c18f0ff

def z655 : W := mkw 0x0000012000004808 0x0000000900000240 0x080001b000006c00 0x4040000d80000360

def z656 : W := mkw 0x008a008420902100 0x0004500421048108 0x0002000600180180 0x000010003000c00c

def z657 : W := mkw 0x03fb65607ed55818 0x681fdb2b03f6aac0 0x27edc7807ce1e001 0x013f6e3c03e70f00

def z658 : W := mkw 0x0004028c00000004 0x0000201460000000 0x0000078e00000000 0x6000003c70000000

def z659 : W := mkw 0x4024c6490c451056 0x2a01263248622882 0xb66dc6499c061064 0x3db36e324ce03083

def z660 : W := mkw 0x21501812d30a04a1 0x510a80c096985025 0xfbf2387fff1e1fff 0xffdf91c3fff8f0ff

def z661 : W := mkw 0x008a008420902100 0x0004500421048108 0x798207866019e193 0xe3cc103c3300cf0c

def z662 : W := mkw 0x0000000000000000 0x0000000000000000 0x900000000006000c 0x9c80000000003000

def z663 : W := mkw 0x01da01a472906908 0x400ed00d23948348 0x499201b663186d82 0x424c900db318c36c

def z664 : W := mkw 0x808a000020b0a300 0x0404500001058518 0x798e000060f9e39b 0x8bcc70000307cf1c

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000004000001014 0xa480000200000080

def z666 : W := mkw 0x042497ff8000001f 0x802124bffc000000 0xb46dc7ff80000000 0x7da36e3ffc000000

def z667 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x9002384f801e13fc 0xbc8011c27c00f09f

def z668 : W := mkw 0x03db7812fbde0001 0x701edbc097def000 0xf7fff87ffffe000f 0xffbfffc3fffff000

def z669 : W := mkw 0x0150012000000008 0x000a800900000000 0x419001b000000000 0x420c800d80000000

def z670 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0x77efc0007cf8000b 0x8bbf7e0003e7c000

def z671 : W := mkw 0x81fe07ec76b1fb1c 0x4c0ff03f63b58fd8 0x7bee078e7cf9e39b 0xebdf703c73e7cf1c

def z672 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x498e018e60f8638a 0x4a4c700c7307c31c

def z673 : W := mkw 0x0150000052000000 0x400a800002900000 0xfbf007807f01e017 0xe7df803c03f80f00

def z674 : W := mkw 0x008a008420902100 0x0004500421048108 0x798e018660f8618b 0xcbcc700c3307c30c

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x218007806001e001 0x010c003c03000f00

def z676 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xb3e007c07c01f015 0xa59f003e03e00f80

def z677 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x318c078860e1e219 0xa98c603c43070f10

def z678 : W := mkw 0x21701d72d70b5cb9 0x590b80eb96b85ae5 0x827038719f061c64 0x141381c38cf830e3

def z679 : W := mkw 0x8004028c0020a304 0x0400201460010518 0x7980078e6001e393 0xe3cc003c73000f1c

def z680 : W := mkw 0x0000000004011000 0x0800000000200880 0x020000001c019015 0x8010000000e00c80

def z681 : W := mkw 0x24249fff810a04bf 0x912124fffc085025 0xd8123fff831e1ffe 0xfec091fffc18f0ff

def z682 : W := mkw 0x03db2884739a2100 0x501ed944239cd108 0x4992398663186182 0x424c91cc3318c30c

def z683 : W := mkw 0x45fff7ff8c45105f 0xaa2fffbffc622882 0xf7ffffff9c061064 0x7fbffffffce03083

def z684 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0xd19239ff80000000 0x7e8c91cffc000000

def z685 : W := mkw 0x008a400028d40000 0x200452000146a000 0xf7efc0007cfe000f 0x9fbf7e0003e7f000

def z686 : W := mkw 0xc00040000c659240 0x2e00020000632c92 0x920000499ce7927d 0xbc9000024ce73c93

def z687 : W := mkw 0x43fbec417fdf1052 0x7a1fdf620bfef882 0xf7fff841fffe106f 0x9fbfffc20ffff083

def z688 : W := mkw 0x03db68007fdf5800 0x781edb4003fefac0 0xfffff8007ffffc1f 0x9fffffc003ffffe0

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800007000001c10 0x60400003800000e0

def z690 : W := mkw 0xe004da1b896e86e7 0x370026d0dc4b7437 0xdc1ff87f83fe1ffe 0xfee0ffc3fc1ff0ff

def z691 : W := mkw 0x20001012800004a1 0x0100008094000025 0x0800003600000d80 0x40400001b000006c

def z692 : W := mkw 0x208a1812a19a04a1 0x110450c0950cd025 0xf99e387fe3fe1fff 0xffccf1c3ff1ff0ff

def z693 : W := mkw 0xc024c6495e65da56 0x6e0126324af32ed2 0xbe6dc649ffe7fe7f 0xbdf36e324fff3ff3

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000006001e013 0x8040000003000f00

def z695 : W := mkw 0x8000000020b0a300 0x0400000001058518 0x5802000e60f9e39b 0xeac010007307cf1c

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x4980018060006002 0x424c000c03000300

def z697 : W := mkw 0x21700d60570b5cb8 0x590b806b02b85ae5 0xfbf007f07f1fffff 0xe7df803f83f8ffff

def z698 : W := mkw 0x01da000072900000 0x400ed00003948000 0xf3fe00007ff8000f 0x8f9ff00003ffc000

def z699 : W := mkw 0xe174df7bdf6fdeff 0x7f0ba6fbdefb7ef7 0xffffffffffffffff 0xffffffffffffffff

def z700 : W := mkw 0x03db2800739a0000 0x501ed940039cd000 0x719e380063f8000b 0x8b8cf1c0031fc000

def z701 : W := mkw 0xc174c7695e65da5e 0x6e0ba63b4af32ed2 0x27edc7807ce1e001 0x013f6e3c03e70f00

def z702 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xb7edc0007ce6000d 0x9dbf6e0003e73000

def z703 : W := mkw 0x04ae97ff8000001f 0x802574bffc000000 0x718e07ff80000000 0x6b8c703ffc000000

def z704 : W := mkw 0x83df628c7af4a304 0x641efb1463d7a518 0x27edc7807ce1e001 0x013f6e3c03e70f00

def z705 : W := mkw 0x008a008400000000 0x0004500420000000 0x4182018600000000 0x420c100c30000000

def z706 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0x758ff80060fe000b 0x9bac7fc00307f000

def z707 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xf7fff8007ffe03ef 0x9fbfffc003fff01f

def z708 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8007fe60005 0x1fbfffc003ff3000

def z709 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7fffffffc01f015 0xffbfffffffe00f80

def z710 : W := mkw 0x85ffb7ff8020a31f 0x842ffdbffc010518 0xf5ffffff8001e000 0x7faffffffc000f00

def z711 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0x65ffff8000000000 0x032ffffc00000000

def z712 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0x67fff8007ce00001 0x033fffc003e70000

def z713 : W := mkw 0x048fb29fd6015807 0xc8247d94feb00ac0 0x0e0ff80fff01fc17 0x98707fc07ff80fe0

def z714 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x867df8001fe60004 0x1433efc000ff3000

def z715 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0x040ff80f80e00000 0x18207fc07c070000

def z716 : W := mkw 0x85dfb29fa0b0a307 0x842efd94fd058518 0xfdffff8fe0f9e39b 0xffeffffc7f07cf1c

def z717 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x27edf8007ce60001 0x113f6fc003e73000

def z718 : W := mkw 0x028a480029de0000 0x30145240014ef000 0x000e000000fe0008 0x080070000007f000

def z719 : W := mkw 0x83de4a8c7bfea304 0x741ef25463dff518 0xfbfe078e7fffe39f 0xefdff03c73ffff1c

def z720 : W := mkw 0x020048007bde0000 0x7010024003def000 0x0a0000007fffe01f 0x8050000003ffff00

def z721 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x2be007f07f01fc17 0xe15f003f83f80fe0

def z722 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xfdefc78e60f9e39b 0xffef7e3c7307cf1c

def z723 : W := mkw 0x05fbb5f7a090211b 0x802fddafbd048108 0xcdf3f9f7e0186182 0x566f9fcfbf00c30c

def z724 : W := mkw 0x020048007bde0000 0x7010024003def000 0x738000007ffe000f 0x839c000003fff000

def z725 : W := mkw 0x0575b7ff8000001f 0x802badbffc000000 0xd473ffff80000000 0x7ea39ffffc000000

def z726 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078fe0ffe3fb 0xfbcc703c7f07ff1f

def z727 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xf5ffffff80e18001 0x7faffffffc070c00

def z728 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80001014 0xffaffffffc000080

def z729 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000007ff80003 0x0010000003ffc000

def z730 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f9ff01fc17 0xffdf803fcff80fe0

def z731 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0x7dffffbe60f9e39b 0xebeffffdf307cf1c

def z732 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0xfd9fffffe0f9e39b 0xffecffffff07cf1c

def z733 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffffff19ff9f 0xfffffffffff8cffc

def z734 : W := mkw 0x01db200020900000 0x000ed90001048000 0xf5fff80060180002 0x1fafffc00300c000

def z735 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fffe007fff801f 0xbfbffff003fffc00

def z736 : W := mkw 0x02ab6d602ddf5818 0x38155b6b016efac0 0x0c0ffff000fffc18 0x78607fff8007ffe0

def z737 : W := mkw 0x05ffb7ffd200481f 0xc02ffdbffe900240 0xf5ffffff83000c00 0x7faffffffc180060

def z738 : W := mkw 0x00ae96df80000017 0x000574b6fc000000 0xf5ffffff80000000 0x7faffffffc000000

def z739 : W := mkw 0x01df228c52000004 0x400ef91462900000 0xffffff8e7f01e017 0xfffffffc73f80f00

def z740 : W := mkw 0xc004c20908648246 0x2600261048432412 0x866dc0099ce6026c 0x1c336e004ce73013

def z741 : W := mkw 0x01db200072900000 0x400ed90003948000 0xf7fff8007ff8000f 0x9fbfffc003ffc000

def z742 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffffe0e1e219 0xffafffffff070f10

def z743 : W := mkw 0x0171256056015818 0x480b892b02b00ac0 0xfff1fff07f01fc17 0xf7ff8fff83f80fe0

def z744 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xfffff8007ffe0d8f 0x9fffffc003fff06c

def z745 : W := mkw 0x0024965b80000017 0x000124b2dc000000 0xb47dfe7980000000 0x3da3eff3cc000000

def z746 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xbe6dc6499cff93ff 0xbdf36e324ce7fc9f

def z747 : W := mkw 0x0151200000000000 0x000a890000000000 0xd473f80000000000 0x1ea39fc000000000

def z748 : W := mkw 0x07ffb7fff290001f 0xc03ffdbfff948000 0xf5ffffffe0000000 0x7fafffffff000000

def z749 : W := mkw 0x0571b573d200481b 0xc02b8dab9e900240 0x8471f87183000c00 0x14238fc38c180060

def z750 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0xd41ff80f80000000 0x1ea0ffc07c000000

def z751 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xf5ffffff80001c60 0x7faffffffc0000e3

def z752 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff84980000000 0x3fafffc24c000000

def z753 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe3f9ff9f 0xffefffffff1fcffc

def z754 : W := mkw 0x82044a087bfe8204 0x7410225043dff410 0x320c06087fff821f 0xa990603043fffc10

def z755 : W := mkw 0x05df33be8000000d 0x802ef99df4000000 0xf5ffffbe00000000 0x7faffffdf0000000

def z756 : W := mkw 0x05ffb77b8000001f 0x802ffdbbdc000000 0xf5fffe7980000000 0x3faffff3cc000000

def z757 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f07f01ec03 0x67df803f83f80f60

def z758 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x0471f83000000000 0x00238fc180000000

def z759 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc0499ce6126d 0x9db36e024ce73093

def z760 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0x25efff8000000000 0x192f7ffc00000000

def z761 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xabf007f07f01fc15 0x655f803f83f80fe0

def z762 : W := mkw 0x02004800094e0000 0x30100240004a7000 0x0000000000060000 0x0000000000003000

def z763 : W := mkw 0xc024c6490c65b356 0x2e01263248632d9a 0xbe6dc6499ce7f3fd 0xbdf36e324ce73f9f

def z764 : W := mkw 0x035049207bde4808 0x701a824903def240 0x4b9001b07ffe6c0f 0xc25c800d83fff360

def z765 : W := mkw 0x01dfa20900000006 0x000efd1048000000 0xf5fff80980000000 0x1fafffc04c000000

def z766 : W := mkw 0x01ffb65b80000017 0x000ffdb2dc000000 0xf5fffe7f80000000 0x7faffff3fc000000

def z767 : W := mkw 0x25ffafed010a04be 0x912ffd7f68085025 0x2dedc780031e1ffe 0x816f6e3c0018f0ff

def z768 : W := mkw 0x85ffb7fff6b1fb1f 0xcc2ffdbfffb58fd8 0xf7fffffffce1e001 0x7fbfffffffe70f00

def z769 : W := mkw 0xc42497ff8421925f 0x8e2124bffc210c92 0x000007ff80018000 0x6000003ffc000c00

def z770 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5fff87f80000000 0x1fafffc3fc000000

def z771 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf66fc6499cff927f 0xbfb37e324ce7fc93

def z772 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x67fff8007ffe000f 0x833fffc003fff000

def z773 : W := mkw 0xe024de5b8d6f96f7 0x3f0126f2dc6b7cb7 0x6e7ffe361ff98d83 0x4373fff1b0ffcc6c

def z774 : W := mkw 0x828e4a8c7bfea304 0x7414725463dff518 0x020e000e7ffe038f 0x8810700073fff01c

def z775 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffff9f01fc14 0x7ffffffffcf80fe0

def z776 : W := mkw 0xc024c7690c65da5e 0x2e01263b48632ed2 0xb66dc6799ce79e7d 0xbdb36e33cce73cf3

def z777 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xb47ffe7f80000000 0x3da3fff3fc000000

def z778 : W := mkw 0x01db200000000000 0x000ed90000000000 0xa5fdf80000000000 0x152fefc000000000

def z779 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0x7defff8fe0f9e39b 0xfbef7ffc7f07cf1c

def z780 : W := mkw 0x828e4a8c7bfea304 0x7414725463dff518 0x238c07807fffe00f 0x811c603c03ffff00

def z781 : W := mkw 0x05ffb7ffd200481f 0xc02ffdbffe900240 0xfdffffffe3007c16 0xffefffffff1803e0

def z782 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0xf5fff9bf80000000 0x5fafffcdfc000000

def z783 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd012387f831e1fec 0x7e8091c3fc18f0ff

def z784 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8007ffe001f 0xffffffc003fff000

def z785 : W := mkw 0x8004420808648204 0x2400221040432410 0xb66dc6499ce7927d 0xbdb36e324ce73c93

def z786 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0x65fff9b600000000 0x432fffcdb0000000

def z787 : W := mkw 0x05ffb7ffa090001f 0x802ffdbffd048000 0xfdffffffe0f8039b 0xffefffffff07c01c

def z788 : W := mkw 0xc004c20908648246 0x2600261048432412 0xb66dc0499ce6127d 0xbdb36e024ce73093

def z789 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040ff80600000000 0x00207fc030000000

def z790 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078660f9e18b 0xcbcc703c3307cf0c

def z791 : W := mkw 0xc424977b8421925f 0x8e2124bbdc210c92 0x0000067980019270 0x20000033cc000c93

def z792 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x8471f87183001c04 0x14238fc38c1800e0

def z793 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8307ffe0c0f 0xdfffffc183fff060

def z794 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8007ffe127f 0x9fbfffc003fff093

def z795 : W := mkw 0x84afb7ffa0b0a31f 0x84257dbffd058518 0x7d8fffffe0f9e39b 0xfbec7fffff07cf1c

def z796 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x298c078e60f9e39b 0xe14c603c7307cf1c

def z797 : W := mkw 0xa5ffb7ffa0b0a7bf 0x852ffdbffd05853d 0xfdffffffe0f9fffb 0xffefffffff07cfff

def z798 : W := mkw 0x85ffa7ed20b0a31e 0x842ffd3f69058518 0xf5ffff8060f9e00b 0x9faffffc0307cf00

def z799 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6499ce78269 0x3db36e324ce73c13

def z800 : W := mkw 0x03db200072900000 0x401ed90003948000 0xf5fff80060000000 0x1fafffc003000000

def z801 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf67ffe499ce7927d 0xbfb3fff24ce73c93

def z802 : W := mkw 0x04afb7ff8000001f 0x80257dbffc000000 0xd41fffff80000000 0x7ea0fffffc000000

def z803 : W := mkw 0x01ff27ec5601581c 0x480ff93f62b00ac0 0xfffffffe7f01fc17 0xfffffffff3f80fe0

def z804 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x841ff87f80000000 0x1c20ffc3fc000000

def z805 : W := mkw 0xe0004800096e86e0 0x37000240004b7437 0x0000000000fe03e8 0x000000000007f01f

def z806 : W := mkw 0x0151200000000000 0x000a890000000000 0xf5f1f80000000000 0x17af8fc000000000

def z807 : W := mkw 0x828e4a8c29fea304 0x34147254614ff518 0x000e000e00fe0388 0x080070007007f01c

def z808 : W := mkw 0x020048007bde0000 0x7010024003def000 0x520200007ffe000f 0x8a90100003fff000

def z809 : W := mkw 0x05dfb29f80000007 0x802efd94fc000000 0x847ff80f80000000 0x1c23ffc07c000000

def z810 : W := mkw 0x0150012056015808 0x480a800902b00ac0 0x7b9007b07f01fc17 0xe3dc803d83f80fe0

def z811 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf99e078e63f9e39f 0xefccf03c731fcf1c

def z812 : W := mkw 0x0575b77bd601581f 0xc82badbbdeb00ac0 0xfffdfff9ff01fc17 0xffffefffcff80fe0

def z813 : W := mkw 0x048bb01380000003 0x80245d809c000000 0x040ff80180000000 0x18207fc00c000000

def z814 : W := mkw 0x23db3812f39a04a1 0x511ed9c0979cd025 0x4192380663180182 0x020c91c03318c00c

def z815 : W := mkw 0xa08e1a9ea1baa7a5 0x150470d4f50dd53d 0xa19c3ff1e3e7fc65 0x150ce1ff8f1f3fe3

def z816 : W := mkw 0x01fb256076915818 0x480fd92b03b48ac0 0xfffffff07ff9fc1f 0xffffffff83ffcfe0

def z817 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x9471f87980000000 0x3ca38fc3cc000000

def z818 : W := mkw 0x02204c407fdf1010 0x7811026203fef880 0xb26006407fff901f 0xa593003203fffc80

def z819 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf99e3f8e60f9e39b 0xffccf1fc7307cf1c

def z820 : W := mkw 0x05ffb7ffd200001f 0xc02ffdbffe900000 0xf7ffffff9f000004 0x7fbffffffcf80000

def z821 : W := mkw 0x6170dd73df4f5cfb 0x7b0b86eb9efa7ae7 0x8671f8719f061c64 0x14338fc38cf830e3

def z822 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80001270 0x7faffffffc000093

def z823 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x77fff8007ff8000b 0x8bbfffc003ffc000

def z824 : W := mkw 0x85dfb29fa0b0a307 0x842efd94fd058518 0xf5fff80fe0f8038b 0x9fafffc07f07c01c

def z825 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xa66dc6419ce7927d 0x95336e320ce73c93

def z826 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xb5efffcf80000000 0x3daf7ffe7c000000

def z827 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8001ffe000c 0x1fbfffc000fff000

def z828 : W := mkw 0x0571b573d200001b 0xc02b8dab9e900000 0x8671f8719f000004 0x14338fc38cf80000

def z829 : W := mkw 0x035168007bde0000 0x701a8b4003def000 0xb67df8007ffe000f 0x9db3efc003fff000

def z830 : W := mkw 0x2200480029de04a0 0x31100240014ef025 0x0800000003fe1ffe 0x80400000001ff0ff

def z831 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0x866dc0419ce6106c 0x1c336e020ce73083

def z832 : W := mkw 0x85ffb7ffd621da1f 0xcc2ffdbffeb10ed0 0xffffffffffe1fe1f 0xffffffffffff0ff0

def z833 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0xf59fffff80000000 0x7facfffffc000000

def z834 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff87e7ffe1f9f 0xffffffc3f3fff0fc

def z835 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff84ffffe13ff 0xffffffc27ffff09f

def z836 : W := mkw 0x05dfb29f80000007 0x802efd94fc000000 0xf5ffff8f80000000 0x7faffffc7c000000

def z837 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf98e078e60ffe39f 0xffcc703c7307ff1c

def z838 : W := mkw 0x03db68847bde0000 0x701edb4423def000 0xf7fff9867ffe000f 0xdfbfffcc33fff000

def z839 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x966dc0499ce6127c 0xbcb36e024ce73093

def z840 : W := mkw 0x020048005b4e0000 0x7010024002da7000 0x020000001fe6000d 0x8010000000ff3000

def z841 : W := mkw 0x83556a8c5b6ea304 0x741aab5462db7518 0x8e71ff8e1f07e394 0x74738ffc70f83f1c

def z842 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078660f9e193 0xe3cc703c3307cf0c

def z843 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff8000006000c 0x9fafffc000003000

def z844 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xf5ffffff80019010 0x7faffffffc000c80

def z845 : W := mkw 0x008b600008440000 0x20045b0000422000 0xb66ff8001ce6000d 0x9db37fc000e73000

def z846 : W := mkw 0xc5ffb7ff8421da5f 0x8e2ffdbffc210ed2 0xfdffffff8001fe70 0x7feffffffc000ff3

def z847 : W := mkw 0x23704d607fdf5cb8 0x791b826b03fefae5 0xfbf007f07fffffff 0xe7df803f83ffffff

def z848 : W := mkw 0x05ffb7ffd200001f 0xc02ffdbffe900000 0xffffffffff001c17 0xfffffffffff800e0

def z849 : W := mkw 0x03da48007bde0000 0x701ed24003def000 0xf3fe00007ffe000f 0x8f9ff00003fff000

def z850 : W := mkw 0x0004921b80000007 0x00002490dc000000 0x040ff80f80000000 0x18207fc07c000000

def z851 : W := mkw 0x01db200000000000 0x000ed90000000000 0x847ff80000000000 0x1c23ffc000000000

def z852 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xc5fff9ff80000000 0x5e2fffcffc000000

def z853 : W := mkw 0x01db200000000000 0x000ed90000000000 0x65fff80000000000 0x032fffc000000000

def z854 : W := mkw 0x00004800094e0000 0x30000240004a7000 0xb66ff8001cfe000d 0x9db37fc000e7f000

def z855 : W := mkw 0x035048007bde0000 0x701a824003def000 0x827000007ffe000f 0x8413800003fff000

def z856 : W := mkw 0x40aac4c52cd53152 0x2a0556262966a98a 0xcfe3c1c7fc1e71e6 0x567f1e0e3fe0f38f

def z857 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x847fffff80000000 0x7c23fffffc000000

def z858 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xbe6dc7c99ce7f27d 0xfdf36e3e4ce73f93

def z859 : W := mkw 0x008b301280000001 0x0004598094000000 0xd41ff87f80000000 0x7ea0ffc3fc000000

def z860 : W := mkw 0x8571b573a0b0a31b 0x842b8dab9d058518 0x8c71f871e0f9e39b 0x94638fc38f07cf1c

def z861 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6499ce79279 0x39336e324ce73c93

def z862 : W := mkw 0x22005812fbde04a1 0x711002c097def025 0x0a00007ffffe1fff 0xe0500003fffff0ff

def z863 : W := mkw 0x8004028c20b0a304 0x0400201461058518 0x7980078e60f9e39b 0xe3cc003c7307cf1c

def z864 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8007ffe1c1f 0x9fffffc003fff0e0

def z865 : W := mkw 0x0151200052000000 0x400a890002900000 0x8671f8001f000004 0x14338fc000f80000

def z866 : W := mkw 0xc154c3295a64ca4e 0x660aa6194ad32652 0x4d9dc1b9e3e66e6a 0x5a6cee0dcf1f3373

def z867 : W := mkw 0x01db3012d2000001 0x400ed98096900000 0xfffff87fff001c17 0xffffffc3fff800e0

def z868 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80018011 0xffaffffffc000c00

def z869 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040df80180000000 0x10206fc00c000000

def z870 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f87f01fe1f 0xefdf803fc3f80ff0

def z871 : W := mkw 0xc224ce497fff9256 0x7e1126724bfffc92 0x02000649ffff927f 0xa01000324ffffc93

def z872 : W := mkw 0x0000000000000000 0x0000000000000000 0xf47ff80000000000 0x1fa3ffc000000000

def z873 : W := mkw 0x848fa28d20b0a306 0x84247d1469058518 0x7d8fc78e60f9e39b 0xebec7e3c7307cf1c

def z874 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffffff01ec03 0x7ffffffffff80f60

def z875 : W := mkw 0x01db200056015800 0x480ed90002b00ac0 0xfffff8007f01fc17 0x9fffffc003f80fe0

def z876 : W := mkw 0x008b200020900000 0x0004590001048000 0x758ff80060f8000b 0x9bac7fc00307c000

def z877 : W := mkw 0x85df33bea0b0a30d 0x842ef99df5058518 0xfdffffbe60f9e39b 0xffeffffdf307cf1c

def z878 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0x041ff83f80000000 0x1820ffc1fc000000

def z879 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff80e00000000 0x7fafffc070000000

def z880 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xfc7ff87f831e1ffe 0xffe3ffc3fc18f0ff

def z881 : W := mkw 0x01fb256056015818 0x480fd92b02b00ac0 0xf7ffff807c01e001 0x1fbffffc03e00f00

def z882 : W := mkw 0x01db301280000001 0x000ed98094000000 0xf5fff80f80000000 0x1fafffc07c000000

def z883 : W := mkw 0x020048007bde0000 0x7010024003def000 0xf67ff8007ffe000f 0x9fb3ffc003fff000

def z884 : W := mkw 0x85ffb7ff8020a31f 0x842ffdbffc010518 0xf5ffffff80000380 0x7faffffffc00001c

def z885 : W := mkw 0x008b200000000000 0x0004590000000000 0x758ff80000000000 0x1bac7fc000000000

def z886 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xfdffffffe301fc12 0x7fefffffff180fe0

def z887 : W := mkw 0x05ffb7ff8000481f 0x802ffdbffc000240 0xfdffffff80006c00 0x7feffffffc000360

def z888 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf207f07f19fc1f 0xefdf903f83f8cfe0

def z889 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff8018000a 0xffaffffffc00c000

def z890 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xfe7fc67f9fff9fff 0xfff3fe33fcfffcff

def z891 : W := mkw 0x81df228c0020a304 0x040ef91460010518 0xfdffff8e0001e390 0x7feffffc70000f1c

def z892 : W := mkw 0x0401b01380000003 0x80200d809c000000 0x0403f80f80000000 0x18201fc07c000000

def z893 : W := mkw 0x808a008420b0a300 0x0404500421058518 0x7982078660f9e39b 0xe3cc103c3307cf1c

def z894 : W := mkw 0x05ffb7ffa090211f 0x802ffdbffd048108 0xfdffffffe019e193 0xffefffffff00cf0c

def z895 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd8123fff831ffffe 0xfec091fffc18ffff

def z896 : W := mkw 0x220048005b4e04a0 0x7110024002da7025 0x0a0000001f1e1ffe 0x8050000000f8f0ff

def z897 : W := mkw 0x0551313280000009 0x802a898994000000 0x8471f83000000000 0x14238fc180000000

def z898 : W := mkw 0x0151200000000000 0x000a890000000000 0xb47df80000000000 0x1da3efc000000000

def z899 : W := mkw 0x81ffa64920b08216 0x040ffd3249058410 0xf5fffe49e0f9821b 0xbfaffff24f07cc10

def z900 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe0f9e183 0x7fefffffff07cf0c

def z901 : W := mkw 0x80ae96dfa0b0a317 0x040574b6fd058518 0xfdffffffe0f9e39b 0xffefffffff07cf1c

def z902 : W := mkw 0xc024c7690c65da5e 0x2e01263b48632ed2 0xffedc7f9fce7fe7f 0xffff6e3fcfe73ff3

def z903 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078e60fff3ff 0xebcc703c7307ff9f

def z904 : W := mkw 0x04afb6df80000017 0x80257db6fc000000 0x246ffe0f80000000 0x19237ff07c000000

def z905 : W := mkw 0x015048005b4e0000 0x700a824002da7000 0xf7fff8007ffe000f 0x9fbfffc003fff000

def z906 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0x6fffffb67f01ec03 0x437ffffdb3f80f60

def z907 : W := mkw 0x81fe07ec76b1fb1c 0x4c0ff03f63b58fd8 0x827e007e1ff81f8c 0x0c13f003f0ffc0fc

def z908 : W := mkw 0x05dbb1b78000000b 0x802edd8dbc000000 0x4593f9b780000000 0x522c9fcdbc000000

def z909 : W := mkw 0x03704d607fdf5818 0x781b826b03fefac0 0x827000707ffe1c0f 0x8413800383fff0e0

def z910 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x066ff8001cfe0008 0x18337fc000e7f000

def z911 : W := mkw 0x0624dffffbde001f 0xf03126ffffdef000 0x020007fffffe000f 0xe010003ffffff000

def z912 : W := mkw 0x05ffb7ffd200481f 0xc02ffdbffe900240 0xfdffffffe301ec13 0xffefffffff180f60

def z913 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xb7eff8007cfe000d 0x9dbf7fc003e7f000

def z914 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f07f19ff9f 0xe7df803f83f8cffc

def z915 : W := mkw 0x01db301280000001 0x000ed98094000000 0xf5fff83600000000 0x5fafffc1b0000000

def z916 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff80000e00009 0x9fafffc000070000

def z917 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x866dc0419ce61064 0x14336e020ce73083

def z918 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffffe019e39b 0xffefffffff00cf1c

def z919 : W := mkw 0x220048007fdf5ca0 0x7910024003fefae5 0x0a0000007fffffff 0x8050000003ffffff

def z920 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5ffff8000000000 0x7faffffc00000000

def z921 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6419ce7906d 0x9db36e320ce73c83

def z922 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xf81e387f83fe1fff 0xffc0f1c3fc1ff0ff

def z923 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xd471f87180000000 0x76a38fc38c000000

def z924 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffff80e00000 0x7faffffffc070000

def z925 : W := mkw 0x03db69207bde4808 0x701edb4903def240 0xfffff9f07ffe7c1f 0xffffffcf83fff3e0

def z926 : W := mkw 0x048fb29fa0902107 0x80247d94fd048108 0x040ff80f80180180 0x18207fc07c00c00c

def z927 : W := mkw 0x048b309680000001 0x80245984b4000000 0x040ff80600000000 0x18207fc030000000

def z928 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0x058ff98f80000000 0x182c7fcc7c000000

def z929 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x25fdffb000000000 0x012feffd80000000

def z930 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0x867df8001fe6000c 0x1c33efc000ff3000

def z931 : W := mkw 0xe0004800096e86e0 0x37000240004b7437 0x0800000003fe1ffe 0x80400000001ff0ff

def z932 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xa66dc6499ce79275 0x35336e324ce73c93

def z933 : W := mkw 0x05ffb7ffd200001f 0xc02ffdbffe900000 0xf5ffffffe3000002 0x7fafffffff180000

def z934 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xfffff80e7ffe1fff 0xffffffc073fff0ff

def z935 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xf5f1f87180000000 0x17af8fc38c000000

def z936 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x8812387f831e1ffe 0x9c4091c3fc18f0ff

def z937 : W := mkw 0x05db31b6a0902109 0x802ed98db5048108 0xfdfff9b660f8618b 0xdfefffcdb307c30c

def z938 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb67dc6799fe79e7d 0xbdb3ee33ccff3cf3

def z939 : W := mkw 0x0200480029de0000 0x30100240014ef000 0x020000001cfe000d 0x8010000000e7f000

def z940 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7ffffffff01fc05 0x7fbffffffff80fe0

def z941 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xb471fe7180000000 0x35a38ff38c000000

def z942 : W := mkw 0xc5db71b68c659249 0xae2edb8db4632c92 0x439239b61ce7927d 0xc21c91cdb0e73c93

def z943 : W := mkw 0x01db200000000000 0x000ed90000000000 0xfdfff87003001c16 0xffefffc3801800e0

def z944 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7ffff807fffe00f 0x9fbffffc03ffff00

def z945 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x540ff80f80000000 0x7aa07fc07c000000

def z946 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff801e13fe 0xffeffffffc00f09f

def z947 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffffe301fc17 0xffefffffff180fe0

def z948 : W := mkw 0x23db7012fad404a1 0x611edb8097d6a025 0x2fedc07ffce01ff1 0x617f6e03ffe700ff

def z949 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040ff80f80180388 0x18207fc07c00c01c

def z950 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xebf007f07f01fc07 0x475f803f83f80fe0

def z951 : W := mkw 0x81ff27ec76b1fb1c 0x4c0ff93f63b58fd8 0xfffffffe7ff9ff9f 0xfffffffff3ffcffc

def z952 : W := mkw 0x0405b29f80000007 0x80202d94fc000000 0x0401f80f80000000 0x10200fc07c000000

def z953 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e07fe60f9ff9b 0xebcc703ff307cffc

def z954 : W := mkw 0x05ffb6df80000017 0x802ffdb6fc000000 0xf5fffe4f80000000 0x3faffff27c000000

def z955 : W := mkw 0x03704d607bde0018 0x701b826b03def000 0xf3f007f07ffe000f 0xe79f803f83fff000

def z956 : W := mkw 0x05db21a400000008 0x802ed90d20000000 0xf5fff98000000000 0x1fafffcc00000000

def z957 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5fffff180000000 0x1fafffff8c000000

def z958 : W := mkw 0xe0204c400d6f96f0 0x3f010262006b7cb7 0xfa7006701fff9fff 0xe7d3803380fffcff

def z959 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0xa66dc0419ce61065 0x15336e020ce73083

def z960 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xfdffffff80181ffa 0xffeffffffc00c0ff

def z961 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x8471f87f80000000 0x74238fc3fc000000

def z962 : W := mkw 0x842497ff8421fb1f 0x8c2124bffc210fd8 0x080007ff8001ff90 0x6040003ffc000ffc

def z963 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xb67ff8001ffe000d 0x9db3ffc000fff000

def z964 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xbe6dc64f9ce793fd 0xfdf36e327ce73c9f

def z965 : W := mkw 0xc3ffae4977bb9256 0x5e1ffd724bbddc92 0x41923e49e3199272 0x220c91f24f18cc93

def z966 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xfffffff67f01fc17 0xe7ffffffb3f80fe0

def z967 : W := mkw 0x81df228c20b0a304 0x040ef91461058518 0xf5ffff8060e1e001 0x1faffffc03070f00

def z968 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x799e07be63f9ef9b 0xebccf03df31fcf7c

def z969 : W := mkw 0x0151301280000001 0x000a898094000000 0xd473f87f80000000 0x7ea39fc3fc000000

def z970 : W := mkw 0x0401b01380000003 0x80200d809c000000 0x8411f87180000000 0x14208fc38c000000

def z971 : W := mkw 0x01db200000000000 0x000ed90000000000 0x25eff80000000000 0x192f7fc000000000

def z972 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffffe0f8038b 0xffafffffff07c01c

def z973 : W := mkw 0xe024965b842196f7 0x0f0124b2dc210cb7 0xfc7ffe7f80019ff0 0x7fe3fff3fc000cff

def z974 : W := mkw 0x0551b01380000003 0x802a8d809c000000 0x8471f80180000000 0x14238fc00c000000

def z975 : W := mkw 0x0571b5738401581b 0x882b8dab9c200ac0 0x8c71fff18001fc10 0x74638fff8c000fe0

def z976 : W := mkw 0x035048007bde0000 0x701a824003def000 0x23e000007ffe000f 0x811f000003fff000

def z977 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xe7fff8007ffe0007 0x173fffc003fff000

def z978 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xe5fffff780000000 0x572fffffbc000000

def z979 : W := mkw 0x028a48007bde0000 0x7014524003def000 0x238c00007ffe000f 0x811c600003fff000

def z980 : W := mkw 0x020048007bde0000 0x7010024003def000 0x92000049fffe127f 0xbc9000024ffff093

def z981 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf66fc64f9ce7927d 0xffb37e327ce73c93

def z982 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff9807ffe600f 0xdfffffcc03fff300

def z983 : W := mkw 0x03db68007bde4800 0x701edb4003def240 0xfffff8007ffe6c0f 0x9fffffc003fff360

def z984 : W := mkw 0x03db69a47bde6908 0x701edb4d23def348 0xfffff9b67ffe6d8f 0xdfffffcdb3fff36c

def z985 : W := mkw 0x05ffb7ffd200001f 0xc02ffdbffe900000 0xffffffffff01e017 0xfffffffffff80f00

def z986 : W := mkw 0x02016800094e0000 0x30100b40004a7000 0xb66df8001ce6000d 0x9db36fc000e73000

def z987 : W := mkw 0x05fbb573d601581b 0xc82fddab9eb00ac0 0xfffffff1ff01fc17 0xffffffff8ff80fe0

def z988 : W := mkw 0x05dfa28d00000006 0x802efd1468000000 0xf5fff80000000000 0x1fafffc000000000

def z989 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040ff87f80000000 0x78207fc3fc000000

def z990 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xf7fff8007ffe1c6f 0x9fbfffc003fff0e3

def z991 : W := mkw 0x03db68847bde2100 0x701edb4423def108 0xf7fff9807ffe600f 0x9fbfffcc03fff300

def z992 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfffdc7f07f01fc17 0xffffee3f83f80fe0

def z993 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x7bf007b07f01ec13 0xe3df803d83f80f60

def z994 : W := mkw 0x0425b7ff8000001f 0x80212dbffc000000 0x0401ffff80000000 0x70200ffffc000000

def z995 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffffe0f9e389 0x7fafffffff07cf1c

def z996 : W := mkw 0x85ffb7ff8020a31f 0x842ffdbffc010518 0xfdffffff8019e39a 0xffeffffffc00cf1c

def z997 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0x45f3f9b600000000 0x422f9fcdb0000000

def z998 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x75ffffbe00000000 0x6baffffdf0000000

def z999 : W := mkw 0x028b68007bde0000 0x70145b4003def000 0xb66ff8007ffe000f 0x9db37fc003fff000

def z1000 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0xb46ff80f80000000 0x1da37fc07c000000

def z1001 : W := mkw 0x020048007bde0000 0x7010024003def000 0x0a0000007ffe039f 0x8050000003fff01c

def z1002 : W := mkw 0x05ffb7fff691581f 0xc82ffdbfffb48ac0 0xfffffffffff9fc1f 0xffffffffffffcfe0

def z1003 : W := mkw 0x0020056056015818 0x4801002b02b00ac0 0x7b8007f07f01fc17 0xe3dc003f83f80fe0

def z1004 : W := mkw 0x808e828d20b0a306 0x0404741469058518 0x7d8fc78fe0f9e39b 0xfbec7e3c7f07cf1c

def z1005 : W := mkw 0xc28e4a087fff9244 0x7e14725043fffc92 0x738e06087fff927f 0xab9c703043fffc93

def z1006 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7ffffffff001c07 0xffbffffffff800e0

def z1007 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040ff80f80060268 0x18207fc07c003013

def z1008 : W := mkw 0x002044400c451010 0x2801022200622880 0xb66dc6499ce7927d 0xbdb36e324ce73c93

def z1009 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x218e078660f9e181 0x010c703c3307cf0c

def z1010 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xf7fff8007cf8000b 0x9fbfffc003e7c000

def z1011 : W := mkw 0x8200480029fea300 0x34100240014ff518 0x0800000060ffe39b 0x804000000307ff1c

def z1012 : W := mkw 0x03704d605f4f5818 0x781b826b02fa7ac0 0xfbf007f07f07fc17 0xe7df803f83f83fe0

def z1013 : W := mkw 0x035048005b4e0000 0x701a824002da7000 0xf3f000007f060007 0x879f800003f83000

def z1014 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xc5f1f9f180000000 0x562f8fcf8c000000

def z1015 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xfdffffff80f9839b 0xffeffffffc07cc1c

def z1016 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xf7fff8007fe00007 0x9fbfffc003ff0000

def z1017 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xabf007f07f01fc17 0x855f803f83f80fe0

def z1018 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x8471fff180000000 0x74238fff8c000000

def z1019 : W := mkw 0x828e4a8c29fea304 0x34147254614ff518 0x798e078e60ffe39b 0xebcc703c7307ff1c

def z1020 : W := mkw 0x248fb29f800004a7 0x81247d94fc000025 0x0c0ff87f80001ff0 0x78607fc3fc0000ff

def z1021 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x4812387f831e1ffe 0xe24091c3fc18f0ff

def z1022 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffff9f001c16 0xfffffffffcf800e0

def z1023 : W := mkw 0xe1704d605f6fdef8 0x7f0b826b02fb7ef7 0xfbf007f07fffffff 0xe7df803f83ffffff

def z1024 : W := mkw 0x848fb29f80208207 0x84247d94fc010410 0x040ff80f80e00208 0x18207fc07c070010

def z1025 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0x847ff87f80f80388 0x1c23ffc3fc07c01c

def z1026 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xfa72387f9f1e1fff 0xffd391c3fcf8f0ff

def z1027 : W := mkw 0x01ffa6cd00000016 0x000ffd3668000000 0xf5ffffcf80000000 0x7faffffe7c000000

def z1028 : W := mkw 0x0571b5f78000001b 0x802b8dafbc000000 0x8471f9f780000000 0x54238fcfbc000000

def z1029 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0x759fffbf80000000 0x7bacfffdfc000000

def z1030 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x4982078e60f9e39b 0xe24c103c7307cf1c

def z1031 : W := mkw 0xe42497ff842196ff 0x8f2124bffc210cb7 0x080007ff80019ff0 0x6040003ffc000cff

def z1032 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6499ce79065 0x3db36e324ce73c83

def z1033 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fdf8007fe60007 0x97bfefc003ff3000

def z1034 : W := mkw 0x028a48847bde2100 0x7014524423def108 0x4b8201867ffe618f 0xc25c100c33fff30c

def z1035 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xf5fffff000000000 0x7fafffff80000000

def z1036 : W := mkw 0x05db31b6d2004809 0xc02ed98db6900240 0xfffff9b67f006c07 0xdfffffcdb3f80360

def z1037 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078e60f9e183 0x6bcc703c7307cf0c

def z1038 : W := mkw 0xc5ffb7ffd621da5f 0xce2ffdbffeb10ed2 0xffffffffff01fe77 0xfffffffffff80ff3

def z1039 : W := mkw 0x028a480029de0000 0x30145240014ef000 0x718e000060fe000b 0x8b8c70000307f000

def z1040 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6499ce6126c 0x3db36e324ce73093

def z1041 : W := mkw 0x0401b01380000003 0x80200d809c000000 0xd413f87f80000000 0x7ea09fc3fc000000

def z1042 : W := mkw 0x01db60005a440000 0x600edb0002d22000 0xf7fff8007fe6000f 0x9fbfffc003ff3000

def z1043 : W := mkw 0x0200480029de0000 0x30100240014ef000 0x0000000060fe000b 0x800000000307f000

def z1044 : W := mkw 0x0551b1338000000b 0x802a8d899c000000 0x0411f83180000000 0x10208fc18c000000

def z1045 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xfffdfff1ff01fc17 0xf7ffefff8ff80fe0

def z1046 : W := mkw 0x04afb7ff8000001f 0x80257dbffc000000 0xb46fffff80000000 0x7da37ffffc000000

def z1047 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xbe6dc6499fe79e7f 0xbdf36e324cff3cf3

def z1048 : W := mkw 0x05ffb7fff290001f 0xc02ffdbfff948000 0xf7fffffffff8000f 0xffbfffffffffc000

def z1049 : W := mkw 0x01df220800000004 0x000ef91040000000 0xf5fffe0800000000 0x3faffff040000000

def z1050 : W := mkw 0x028a48007bde0000 0x7014524003def000 0x020e00007ffe000f 0x8810700003fff000

def z1051 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x27eff8007cf80001 0x013f7fc003e7c000

def z1052 : W := mkw 0x23db3812f39a04a1 0x511ed9c0979cd025 0x4192383063180c02 0x020c91c18318c060

def z1053 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f1ff07fc77 0xf7df803f8ff83fe3

def z1054 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf7edc649fce7927f 0xbfbf6e324fe73c93

def z1055 : W := mkw 0xc42497ff8421b35f 0x8e2124bffc210d9a 0x080007ff8001f3f0 0x6040003ffc000f9f

def z1056 : W := mkw 0x05dfb29f80000007 0x802efd94fc000000 0x459ff80f80000000 0x1a2cffc07c000000

def z1057 : W := mkw 0x01db600028d40000 0x200edb000146a000 0xf7fff8007cfe000f 0x9fbfffc003e7f000

def z1058 : W := mkw 0x0000400008440000 0x2000020000422000 0xb66dc0419ce6106d 0x9db36e020ce73083

def z1059 : W := mkw 0x81df228c72b0a304 0x440ef91463958518 0xffffff8e7ff9e39f 0xfffffffc73ffcf1c

def z1060 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x940ff84f8006127c 0xbca07fc27c003093

def z1061 : W := mkw 0x8000000020b0a300 0x0400000001058518 0x7982078e60f9e39b 0xebcc103c7307cf1c

def z1062 : W := mkw 0x05fbb5738000001b 0x802fddab9c000000 0xa5fdf87180000000 0x152fefc38c000000

def z1063 : W := mkw 0x228a48007bde04a0 0x7114524003def025 0x7b8e000e7ffe1fff 0xebdc700073fff0ff

def z1064 : W := mkw 0x21701d72d70b5cb9 0x590b80eb96b85ae5 0x23e23f8ffc1fe3e9 0x191f11fc7fe0ff1f

def z1065 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0x25efff8fe0f9e389 0x192f7ffc7f07cf1c

def z1066 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xfffdc7f9ffe7fe7f 0xffffee3fcfff3ff3

def z1067 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0xfff3ffffff01fc17 0xffff9ffffff80fe0

def z1068 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xbe6dc6799ce79e7d 0xfdf36e33cce73cf3

def z1069 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xf3f007f07f01fc05 0x679f803f83f80fe0

def z1070 : W := mkw 0x04afb6df80000017 0x80257db6fc000000 0x846ff84f80000000 0x1c237fc27c000000

def z1071 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xa7fff8007ffe000d 0x1d3fffc003fff000

def z1072 : W := mkw 0xc024c6490c65da56 0x2e01263248632ed2 0xbe6dc6499ce7fe7d 0xbdf36e324ce73ff3

def z1073 : W := mkw 0xc575b77b8421925f 0x8e2badbbdc210c92 0x8471fe7980019270 0x34238ff3cc000c93

def z1074 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0x866ff8001cfe000c 0x1c337fc000e7f000

def z1075 : W := mkw 0xc42497ff8421da5f 0x8e2124bffc210ed2 0x080007ff8001fe70 0x6040003ffc000ff3

def z1076 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0xf67ff8001ffe000f 0x9fb3ffc000fff000

def z1077 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffffe0006002 0x7fefffffff000300

def z1078 : W := mkw 0x20005012884404a1 0x2100028094422025 0xbe6dc07f9ce61ffd 0xfdf36e03fce730ff

def z1079 : W := mkw 0xc5ffb7ff8421925f 0x8e2ffdbffc210c92 0xf5ffffff80018000 0x7faffffffc000c00

def z1080 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xcbf007f07f01fc16 0x665f803f83f80fe0

def z1081 : W := mkw 0x85ffa7ed20b0a31e 0x842ffd3f69058518 0xfdffff8e60f9e39b 0xffeffffc7307cf1c

def z1082 : W := mkw 0x0000101280000001 0x0000008094000000 0xf47ff87f80000000 0x7fa3ffc3fc000000

def z1083 : W := mkw 0x01ff27ec0000001c 0x000ff93f60000000 0xf5fffffe00000000 0x7faffffff0000000

def z1084 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x4b9007f07f01fc17 0xe25c803f83f80fe0

def z1085 : W := mkw 0x01ffa7695601581e 0x480ffd3b4ab00ac0 0xfffffff9ff01fc17 0xffffffffcff80fe0

def z1086 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80000218 0xffaffffffc000010

def z1087 : W := mkw 0x05dfb3bfd200480f 0xc02efd9dfe900240 0x4d9ff9bfe3006c02 0x5a6cffcdff180360

def z1088 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x066dc0099ce60268 0x18336e004ce73013

def z1089 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x459fffff80000000 0x7a2cfffffc000000

def z1090 : W := mkw 0x008f228c00000004 0x0004791460000000 0x040ff80e00000000 0x18207fc070000000

def z1091 : W := mkw 0xc42496df84219257 0x8e2124b6fc210c92 0x0000064f80019270 0x200000327c000c93

def z1092 : W := mkw 0x05ffb7ff8000211f 0x802ffdbffc000108 0xfdffffff80006180 0x7feffffffc00030c

def z1093 : W := mkw 0x05fb35f6d6015819 0xc82fd9afb6b00ac0 0xfffffff67f01fc17 0xffffffffb3f80fe0

def z1094 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x4812387f831e1ffa 0x7a4091c3fc18f0ff

def z1095 : W := mkw 0x808f228c20b0a304 0x0404791461058518 0x7d8fff8e60f9e39b 0xfbec7ffc7307cf1c

def z1096 : W := mkw 0x25ffb7ff84015cbf 0x892ffdbffc200ae5 0xfdffffff8001fff0 0x7feffffffc000fff

def z1097 : W := mkw 0x020048007bde0000 0x7010024003def000 0x5a02000e7ffe039f 0xead0100073fff01c

def z1098 : W := mkw 0x042497ff8000001f 0x802124bffc000000 0xf47fffff80000000 0x7fa3fffffc000000

def z1099 : W := mkw 0x008b301280000001 0x0004598094000000 0x040ff80f80000000 0x18207fc07c000000

def z1100 : W := mkw 0x01db200000000000 0x000ed90000000000 0xfdffff806001e013 0xffeffffc03000f00

def z1101 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xfffffffffc01fc11 0x7fffffffffe00fe0

def z1102 : W := mkw 0x0575b77b8000001f 0x802badbbdc000000 0x847df87980000000 0x1c23efc3cc000000

def z1103 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6499ce7927d 0xa1336e324ce73c93

def z1104 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffff8f80000000 0x1faffffc7c000000

def z1105 : W := mkw 0x0575b77b8000001f 0x802badbbdc000000 0xa47dfe7180000000 0x1523eff38c000000

def z1106 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0xdc1ff87f83001c16 0xfee0ffc3fc1800e0

def z1107 : W := mkw 0x2200480029de04a0 0x31100240014ef025 0x0000000000fe03e8 0x000000000007f01f

def z1108 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6099ce7927d 0x99336e304ce73c93

def z1109 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe0f8638a 0x7fefffffff07c31c

def z1110 : W := mkw 0x07db69a47bde0008 0xf03edb4d23def000 0xf7fff9807ffe000f 0x9fbfffcc03fff000

def z1111 : W := mkw 0x020048005f4f5800 0x7810024002fa7ac0 0x020000001f061c04 0x0010000000f830e0

def z1112 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000007fe60005 0x0010000003ff3000

def z1113 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xa5fdff8000000000 0x152feffc00000000

def z1114 : W := mkw 0x05ffb7ffa090211f 0x802ffdbffd048108 0xfdffffffe018639a 0xffefffffff00c31c

def z1115 : W := mkw 0x05ffb7ff8401581f 0x882ffdbffc200ac0 0xfdffffff8301fc16 0xffeffffffc180fe0

def z1116 : W := mkw 0x05ffb7ffa090001f 0x802ffdbffd048000 0xf5ffffffe0e00001 0x7fafffffff070000

def z1117 : W := mkw 0xe024de5b8d6f96f7 0x3f0126f2dc6b7cb7 0x0a00067f9fff9fff 0xe0500033fcfffcff

def z1118 : W := mkw 0x81df220800208204 0x040ef91040010410 0xf5fffe0800e18219 0xbfaffff040070c10

def z1119 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0x867ff87f9f001c04 0x1c33ffc3fcf800e0

def z1120 : W := mkw 0x0575b7ffd601581f 0xc82badbffeb00ac0 0xfff1ffffff01fc17 0xf7ff8ffffff80fe0

def z1121 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0x266ff8001cfe0009 0x19337fc000e7f000

def z1122 : W := mkw 0x0001200000000000 0x0000090000000000 0x0401f80000000000 0x10200fc000000000

def z1123 : W := mkw 0x048bb09780000003 0x80245d84bc000000 0x0403f80780000000 0x10201fc03c000000

def z1124 : W := mkw 0x85ffb7ff8020a31f 0x842ffdbffc010518 0xfdffffff80e1e399 0xffeffffffc070f1c

def z1125 : W := mkw 0x01fba44100000012 0x000fdd2208000000 0xf5fff84180000000 0x1fafffc20c000000

def z1126 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff80001c10 0x7feffffffc0000e0

def z1127 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xb7fdf8007fe6000d 0x9dbfefc003ff3000

def z1128 : W := mkw 0x21db3012800004a1 0x010ed98094000025 0xfdfff87f80001ff0 0x7fefffc3fc0000ff

def z1129 : W := mkw 0xc024c7690c65da5e 0x2e01263b48632ed2 0xfe7dc7f99fe7fe7f 0xfff3ee3fccff3ff3

def z1130 : W := mkw 0xe02496df8421b7f7 0x0f0124b6fc210dbf 0x080007ff8001fff0 0x6040003ffc000fff

def z1131 : W := mkw 0xc08e828d20b0a346 0x060474146905851a 0x798e078fe0f9e3fb 0xebcc703c7f07cf1f

def z1132 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8007fffe01f 0x9fffffc003ffff00

def z1133 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xf7ffffff9c07927d 0xffbffffffce03c93

def z1134 : W := mkw 0xc024965b84219257 0x0e0124b2dc210c92 0x0000067f80019270 0x60000033fc000c93

def z1135 : W := mkw 0x03db69207bde4808 0x701edb4903def240 0xffffffb07fffec1f 0xfffffffd83ffff60

def z1136 : W := mkw 0x808f228c20b0a304 0x0404791461058518 0x040ff80e00f80388 0x18207fc07007c01c

def z1137 : W := mkw 0x0575b77b8000001f 0x802badbbdc000000 0xf5fdfff980000000 0x7fafefffcc000000

def z1138 : W := mkw 0x0175a64900000016 0x000bad3248000000 0xb47dfe4980000000 0x3da3eff24c000000

def z1139 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xb3f007f07f01fc15 0xa59f803f83f80fe0

def z1140 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x25efff8600000000 0x012f7ffc30000000

def z1141 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xfdffffff80061ffc 0xffeffffffc0030ff

def z1142 : W := mkw 0xc20048007fffda40 0x7e10024003fffed2 0x0a0000007ffffe7f 0x8050000003fffff3

def z1143 : W := mkw 0xc024c7ed0c65fb5e 0x2e01263f68632fda 0xbe6dc7ff9ce7fffd 0xfdf36e3ffce73fff

def z1144 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8007ff80003 0x1fbfffc003ffc000

def z1145 : W := mkw 0x048fb3bf8000000f 0x80247d9dfc000000 0x040ff9bf80000000 0x58207fcdfc000000

def z1146 : W := mkw 0x020048007bde2100 0x7010024003def108 0x0a0000007ffe618f 0x8050000003fff30c

def z1147 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0x27eff8007ce00001 0x193f7fc003e70000

def z1148 : W := mkw 0x85dfb3bfa0b0a30f 0x842efd9dfd058518 0x7d9fffbfe0f9e39b 0xfbecfffdff07cf1c

def z1149 : W := mkw 0x05ffb7ffd200001f 0xc02ffdbffe900000 0xf7fffffffc000001 0x7fbfffffffe00000

def z1150 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xc5f3ffff80000000 0x762f9ffffc000000

def z1151 : W := mkw 0x0575b7ff8000001f 0x802badbffc000000 0xb47dffff80000000 0x7da3effffc000000

def z1152 : W := mkw 0x23717d72df4f5cb9 0x791b8beb96fa7ae5 0x8671f8719f061c64 0x14338fc38cf830e3

def z1153 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf67dc6499fe7927f 0xbfb3ee324cff3c93

def z1154 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xa5ffffff80000000 0x1d2ffffffc000000

def z1155 : W := mkw 0x20248e49010a04b6 0x1101247248085025 0xbc6dc649831e1ffe 0xbde36e324c18f0ff

def z1156 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0x0c0ff80fe0f9e39b 0x98607fc07f07cf1c

def z1157 : W := mkw 0x01fb256004015818 0x080fd92b00200ac0 0xfdfffff00001fc10 0x7fefffff80000fe0

def z1158 : W := mkw 0x85ffb7ff8020a31f 0x842ffdbffc010518 0xfdffffffe001e393 0xffefffffff000f1c

def z1159 : W := mkw 0x0200480029de0000 0x30100240014ef000 0x0000000003fe000e 0x80000000001ff000

def z1160 : W := mkw 0x01db212052004808 0x400ed90902900240 0xfdfff9b063006c02 0x5fefffcd83180360

def z1161 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff80060000003 0x9fafffc003000000

def z1162 : W := mkw 0x01db200000000000 0x000ed90000000000 0xc5f3f80000000000 0x162f9fc000000000

def z1163 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xd473f87180000000 0x1ea39fc38c000000

def z1164 : W := mkw 0xe00048000d6f96e0 0x3f000240006b7cb7 0x020000001cff93fd 0x8010000000e7fc9f

def z1165 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff83000006 0xffaffffffc180000

def z1166 : W := mkw 0xc004c20908648246 0x2600261048432412 0x266dc0099ce60269 0x19336e004ce73013

def z1167 : W := mkw 0x820048007ffffb00 0x7c10024003ffffd8 0x0a0000007fffff9f 0x8050000003fffffc

def z1168 : W := mkw 0xc5ffb7ff8020825f 0x862ffdbffc010412 0xf5ffffff80000260 0x7faffffffc000013

def z1169 : W := mkw 0x600048000d4f14e0 0x3b000240006a78a7 0x020000001f061c64 0x0010000000f830e3

def z1170 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf23ff07f01fc17 0xffdf91ff83f80fe0

def z1171 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e078e63f9ff9f 0xebcc703c731fcffc

def z1172 : W := mkw 0x01db208400000000 0x000ed90420000000 0xf5fff98600000000 0x5fafffcc30000000

def z1173 : W := mkw 0x85ffb7fff6b1fb1f 0xcc2ffdbfffb58fd8 0xfffffffffcf9e39b 0xffffffffffe7cf1c

def z1174 : W := mkw 0x04afb6df80000017 0x80257db6fc000000 0xf47ffe7f80000000 0x7fa3fff3fc000000

def z1175 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff80180182 0x7feffffffc00c00c

def z1176 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6099ce7826d 0x9db36e304ce73c13

def z1177 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf67dc6799ce7927d 0xffb3ee33cce73c93

def z1178 : W := mkw 0x2571b573800004bb 0x812b8dab9c000025 0x8c71f87f80001ff0 0x74638fc3fc0000ff

def z1179 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xc812387f831e1ff6 0x764091c3fc18f0ff

def z1180 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xbe6dc649fce7f27f 0xbdf36e324fe73f93

def z1181 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x6bf007b07f01fc17 0xc35f803d83f80fe0

def z1182 : W := mkw 0x235048007bde04a0 0x711a824003def025 0xfbf000707ffe1fff 0xe7df800383fff0ff

def z1183 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0xdc1ff87f80f8039a 0xfee0ffc3fc07c01c

def z1184 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xfffff8707ffe1fff 0xffffffc383fff0ff

def z1185 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf7fff8001c000005 0x9fbfffc000e00000

def z1186 : W := mkw 0x0571b573d200481b 0xc02b8dab9e900240 0xcdf1f9f1e3006c02 0x566f8fcf8f180360

def z1187 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f07f07fe7f 0xe7df803f83f83ff3

def z1188 : W := mkw 0x03fa4d607fdf5818 0x781fd26b03fefac0 0xfbfe07f07ffffc1f 0xefdff03f83ffffe0

def z1189 : W := mkw 0x00004800094e0000 0x30000240004a7000 0x020000001ffe000f 0x8010000000fff000

def z1190 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xc473f87780000000 0x56239fc3bc000000

def z1191 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xffffffff9f019c17 0xfffffffffcf80ce0

def z1192 : W := mkw 0xc024c6cd0c65b356 0x2e01263668632d9a 0xb66dc7c99ce7f27d 0xbdb36e3e4ce73f93

def z1193 : W := mkw 0xc5ffb7ff8421925f 0x8e2ffdbffc210c92 0xf5ffffff8007927c 0xffaffffffc003c93

def z1194 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x8812387f831e1ffc 0x7c4091c3fc18f0ff

def z1195 : W := mkw 0x03db69207bde0008 0x701edb4903def000 0xf7fff9b07ffe000f 0xdfbfffcd83fff000

def z1196 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xf5ffff8e00000000 0x7faffffc70000000

def z1197 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xa5fdfff1e0e1e001 0x152fefff8f070f00

def z1198 : W := mkw 0x03db69207bde4808 0x701edb4903def240 0xf7fff8307ffe0c0f 0x9fbfffc183fff060

def z1199 : W := mkw 0x05db313280000009 0x802ed98994000000 0xf5fff83000000000 0x1fafffc180000000

def z1200 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7ffffff9f019c15 0xffbffffffcf80ce0

def z1201 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0xd59ff9ff80000000 0x7eacffcffc000000

def z1202 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe0e1e013 0xffefffffff070f00

def z1203 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xf3f007f07f01fc07 0x879f803f83f80fe0

def z1204 : W := mkw 0xc004c20908648246 0x2600261048432412 0xb66dc6099ce7827d 0xbdb36e304ce73c13

def z1205 : W := mkw 0x4571b5738401105b 0x8a2b8dab9c200882 0x8471f87180001060 0x14238fc38c000083

def z1206 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007fe7f01ff97 0xe7df803ff3f80ffc

def z1207 : W := mkw 0x05ffb7ffd200481f 0xc02ffdbffe900240 0xf5ffffffe0006000 0x7fafffffff000300

def z1208 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffff80f98399 0xffaffffffc07cc1c

def z1209 : W := mkw 0xc424c7ed0c65925e 0xae21263f68632c92 0xb66dc7c99ce7927d 0xbdb36e3e4ce73c93

def z1210 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0xb66dc0499ce6127d 0xbdb36e024ce73093

def z1211 : W := mkw 0x020048005b4e0000 0x7010024002da7000 0x020000007f060007 0x8010000003f83000

def z1212 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f9ff01fe77 0xe7df803fcff80ff3

def z1213 : W := mkw 0x008b200000000000 0x0004590000000000 0xb46ff80000000000 0x1da37fc000000000

def z1214 : W := mkw 0x020048007bde0000 0x7010024003def000 0xda1000707ffe1c1f 0xe6d0800383fff0e0

def z1215 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xd67ff8001ffe000e 0x9eb3ffc000fff000

def z1216 : W := mkw 0x05ffb7fff691791f 0xc82ffdbfffb48bc8 0xffffffffff19fd97 0xfffffffffff8cfec

def z1217 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x77eff8007cfe000b 0x9bbf7fc003e7f000

def z1218 : W := mkw 0x04afb6df80000017 0x80257db6fc000000 0xf5efffcf80000000 0x7faf7ffe7c000000

def z1219 : W := mkw 0x848fb29fa0b0a307 0x84247d94fd058518 0x258fff8fe0e1e001 0x192c7ffc7f070f00

def z1220 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x25edff8180000000 0x112f6ffc0c000000

def z1221 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xf5ffffff80e00208 0x7faffffffc070010

def z1222 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xc812387f831e1fee 0x5e4091c3fc18f0ff

def z1223 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x866dc0499ce7927d 0x9c336e024ce73c93

def z1224 : W := mkw 0x008a000020900000 0x0004500001048000 0x798e078e60f9e39b 0xebcc703c7307cf1c

def z1225 : W := mkw 0x0421b45380000013 0x80210da29c000000 0x8461f84180000000 0x14230fc20c000000

def z1226 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xffffff8e7fffe39f 0xfffffffc73ffff1c

def z1227 : W := mkw 0x220048007bde04a0 0x7110024003def025 0x020000007ffe03ef 0x8010000003fff01f

def z1228 : W := mkw 0x0000400008440000 0x2000020000422000 0xf67ff8001ce6000d 0x9fb3ffc000e73000

def z1229 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0xf7fdf8007fe6000f 0x9fbfefc003ff3000

def z1230 : W := mkw 0x01db3012a0900001 0x000ed98095048000 0xfdfff87fe0f8039b 0xffefffc3ff07c01c

def z1231 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66dc6419ce79075 0xb5b36e320ce73c83

def z1232 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x718e078e60f9e38b 0x8b8c703c7307cf1c

def z1233 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000007cfe0009 0x0010000003e7f000

def z1234 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x758ff80f80000000 0x1bac7fc07c000000

def z1235 : W := mkw 0x03db68005b4e0000 0x701edb4002da7000 0xf7fff8001fe6000d 0x9fbfffc000ff3000

def z1236 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x340ffe0f80000000 0x39a07ff07c000000

def z1237 : W := mkw 0x0024965b84011017 0x080124b2dc200880 0xfe7ffe7f9f019c17 0xfff3fff3fcf80ce0

def z1238 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffffe001e001 0x7fafffffff000f00

def z1239 : W := mkw 0xc1ffa64904219256 0x0e0ffd3248210c92 0xf5fffe4980019270 0x3faffff24c000c93

def z1240 : W := mkw 0x81df329ea0b0a305 0x040ef994f5058518 0xfdffffffe0f9e39b 0xffefffffff07cf1c

def z1241 : W := mkw 0x05fbb5738000001b 0x802fddab9c000000 0xf5fff87f80000000 0x7fafffc3fc000000

def z1242 : W := mkw 0x0171a44100000012 0x000b8d2208000000 0x8471f84180000000 0x14238fc20c000000

def z1243 : W := mkw 0x420048007fdf1040 0x7a10024003fef882 0x020000007ffe106f 0x8010000003fff083

def z1244 : W := mkw 0x028e4a8c7bde0004 0x7014725463def000 0x738e078e7ffe000f 0xeb9c703c73fff000

def z1245 : W := mkw 0x04afb7ff8000001f 0x80257dbffc000000 0x040ff87f80000000 0x18207fc3fc000000

def z1246 : W := mkw 0xc5ffb7ff8421925f 0x8e2ffdbffc210c92 0xf5ffffff80e19279 0xffaffffffc070c93

def z1247 : W := mkw 0x8024965b80208217 0x040124b2dc010410 0xfc7ffe7f80f9839b 0xffe3fff3fc07cc1c

def z1248 : W := mkw 0xc024c6cd0c65b356 0x2e01263668632d9a 0xfe6fc7cf9cfff3ff 0xfff37e3e7ce7ff9f

def z1249 : W := mkw 0x0171256000000018 0x000b892b00000000 0xf5f1fff000000000 0x77af8fff80000000

def z1250 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff83181f9e 0xffeffffffc18c0fc

def z1251 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x046ff80f80000000 0x18237fc07c000000

def z1252 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x27fdf8007fe00001 0x013fefc003ff0000

def z1253 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff8001e010 0x7feffffffc000f00

def z1254 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xfdffffff83001ff6 0xffeffffffc1800ff

def z1255 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7ffffffff01e007 0xffbffffffff80f00

def z1256 : W := mkw 0x0151200052000000 0x400a890002900000 0xf7f1f8007f000007 0x97bf8fc003f80000

def z1257 : W := mkw 0x0174977bd601581f 0x480ba4bbdeb00ac0 0xffffffffff01fc17 0xfffffffffff80fe0

def z1258 : W := mkw 0x05dbb01380000003 0x802edd809c000000 0xf5fff80180000000 0x1fafffc00c000000

def z1259 : W := mkw 0x04afb7ff8401581f 0x88257dbffc200ac0 0x0c0fffff8001fc10 0x78607ffffc000fe0

def z1260 : W := mkw 0xc200480029fe8240 0x36100240014ff412 0x0000000000fe0268 0x000000000007f013

def z1261 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xdc71f87183001c16 0xf6e38fc38c1800e0

def z1262 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff8000018000a 0x9fafffc00000c000

def z1263 : W := mkw 0xc00048000d6f9240 0x3e000240006b7c92 0x020000001fff927f 0x8010000000fffc93

def z1264 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x441ff83f80000000 0x5a20ffc1fc000000

def z1265 : W := mkw 0x220048007bde04a0 0x7110024003def025 0x0a0000007ffe0d8f 0x8050000003fff06c

def z1266 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8707ffe000f 0xffbfffc383fff000

def z1267 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80061064 0x7faffffffc003083

def z1268 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff80003000006 0x9fafffc000180000

def z1269 : W := mkw 0xa28f7a9ea9fea7a5 0x35147bd4f54ff53d 0x040ff80f80fe03e8 0x18207fc07c07f01f

def z1270 : W := mkw 0x4020c4410c451052 0x2a01062208622882 0xb66dc6419ce7907d 0xbdb36e320ce73c83

def z1271 : W := mkw 0x05fbb5738000001b 0x802fddab9c000000 0x847ff87180000000 0x1c23ffc38c000000

def z1272 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xfdf1fff1e001e013 0xf7ef8fff8f000f00

def z1273 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xfe6dc6499ce7927f 0xfff36e324ce73c93

def z1274 : W := mkw 0x017085615601581a 0x480b842b0ab00ac0 0xfff1c7f1ff01fc17 0xf7ff8e3f8ff80fe0

def z1275 : W := mkw 0x05ffb7ff8401581f 0x882ffdbffc200ac0 0xf5ffffff80001c00 0x7faffffffc0000e0

def z1276 : W := mkw 0x0575b77b8000001f 0x802badbbdc000000 0x8471fe7980000000 0x34238ff3cc000000

def z1277 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5fffff600000000 0x67afffffb0000000

def z1278 : W := mkw 0x03db68847bde2100 0x701edb4423def108 0xfffff98e7ffe639f 0xffffffcc73fff31c

def z1279 : W := mkw 0x04afb7ff8000001f 0x80257dbffc000000 0x758fffff80000000 0x7bac7ffffc000000

def z1280 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff879fffe1e7f 0xffffffc3cffff0f3

def z1281 : W := mkw 0xc024c6cd0c65b356 0x2e01263668632d9a 0xb66dc64f9ce793fd 0xbdb36e327ce73c9f

def z1282 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff80e7ffe038f 0x9fbfffc073fff01c

def z1283 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x75efff8f80000000 0x7baf7ffc7c000000

def z1284 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x65ffffff80000000 0x632ffffffc000000

def z1285 : W := mkw 0x05dfb29f80000007 0x802efd94fc000000 0x25eff80f80000000 0x192f7fc07c000000

def z1286 : W := mkw 0x828e4a8c7ffffb04 0x7c14725463ffffd8 0x7b8e078e7fffff9f 0xebdc703c73fffffc

def z1287 : W := mkw 0x0575b7ffd601581f 0xc82badbffeb00ac0 0x8e71ffff9f01fc14 0x74738ffffcf80fe0

def z1288 : W := mkw 0x05fbb5f7d601581b 0xc82fddafbeb00ac0 0xfff3fff7ff01fc17 0xf7ff9fffbff80fe0

def z1289 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0xa7f1fff1fc01e001 0x153f8fff8fe00f00

def z1290 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x23f007b07f01ec01 0x011f803d83f80f60

def z1291 : W := mkw 0x84afb7ffa0b0a31f 0x84257dbffd058518 0x0c0fffff80f9e398 0x78607ffffc07cf1c

def z1292 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffffff07fe7f 0xfffffffffff83ff3

def z1293 : W := mkw 0x00004800094e0000 0x30000240004a7000 0xb67df8001fe6000d 0x9db3efc000ff3000

def z1294 : W := mkw 0x0575b77b8000001f 0x802badbbdc000000 0xf47ffe7f80000000 0x7fa3fff3fc000000

def z1295 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf207fe7f01fc17 0xefdf903ff3f80fe0

def z1296 : W := mkw 0x8004020800208204 0x0400201040010410 0x798e078e60f9e39b 0xebcc703c7307cf1c

def z1297 : W := mkw 0x84afb6dfa0b0a317 0x84257db6fd058518 0xfdefffcfe0f9e39b 0xffef7ffe7f07cf1c

def z1298 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x698e078660f9e39b 0xc34c703c3307cf1c

def z1299 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x038000007ffe000f 0x801c000003fff000

def z1300 : W := mkw 0x01fb256000000018 0x000fd92b00000000 0xf5fff87000000000 0x1fafffc380000000

def z1301 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe0fff3ff 0xffefffffff07ff9f

def z1302 : W := mkw 0x81df228c20b0a304 0x040ef91461058518 0xf5fff80e00f80388 0x1fafffc07007c01c

def z1303 : W := mkw 0x01db200000000000 0x000ed90000000000 0x459ff80000000000 0x1a2cffc000000000

def z1304 : W := mkw 0x0171256000000018 0x000b892b00000000 0x8471f87000000000 0x14238fc380000000

def z1305 : W := mkw 0x05fbb5738000001b 0x802fddab9c000000 0xf5fffff180000000 0x7fafffff8c000000

def z1306 : W := mkw 0x01db6800094e0000 0x300edb40004a7000 0xf7fff8001ffe000f 0x9fbfffc000fff000

def z1307 : W := mkw 0x035048007bde0000 0x701a824003def000 0x439000007ffe000f 0x821c800003fff000

def z1308 : W := mkw 0x04afb6df80000017 0x80257db6fc000000 0x040ffe4f80000000 0x38207ff27c000000

def z1309 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xa5f1fff180000000 0x152f8fff8c000000

def z1310 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff83061e7e 0xffeffffffc1830f3

def z1311 : W := mkw 0x020048005b4e0000 0x7010024002da7000 0x020000001f1e000e 0x8010000000f8f000

def z1312 : W := mkw 0x0024864900000016 0x0001243248000000 0xf47ffe4980000000 0x3fa3fff24c000000

def z1313 : W := mkw 0x0571a5610000001a 0x802b8d2b08000000 0x8471f80000000000 0x14238fc000000000

def z1314 : W := mkw 0x01db200020900000 0x000ed90001048000 0xf5fff80060e00001 0x1fafffc003070000

def z1315 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x458ff98f80000000 0x5a2c7fcc7c000000

def z1316 : W := mkw 0xe024977b8421deff 0x0f0124bbdc210ef7 0x080007ff8001fff0 0x6040003ffc000fff

def z1317 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xc7fff8007ffe000e 0x1e3fffc003fff000

def z1318 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000007ffe127f 0x8010000003fff093

def z1319 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xf7ffffff9c000000 0x7fbffffffce00000

def z1320 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffff80f8039a 0xffeffffffc07c01c

def z1321 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0x6bf007f07f01fc13 0x635f803f83f80fe0

def z1322 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x040fff8f80000000 0x78207ffc7c000000

def z1323 : W := mkw 0x05ffb7ffa090211f 0x802ffdbffd048108 0xfdffffffe0f8618b 0xffefffffff07c30c

def z1324 : W := mkw 0xe08eda9fa9fea7e7 0x370476d4fd4ff53f 0x040ff80f80fe03e8 0x18207fc07c07f01f

def z1325 : W := mkw 0x05ffb7ffa090001f 0x802ffdbffd048000 0xf5ffffff80f80008 0x7faffffffc07c000

def z1326 : W := mkw 0x0575b77bd601581f 0xc82badbbdeb00ac0 0xb67dfe799f019c15 0xbdb3eff3ccf80ce0

def z1327 : W := mkw 0x01fb3572d6015819 0x480fd9ab96b00ac0 0xffffffffff01fc17 0xfffffffffff80fe0

def z1328 : W := mkw 0x028a48007fdf5800 0x7814524003fefac0 0x7b8e07807ffffc1f 0xebdc703c03ffffe0

def z1329 : W := mkw 0x020048007bde0000 0x7010024003def000 0xb26000007ffe000f 0x8593000003fff000

def z1330 : W := mkw 0xe00048000d6f96e0 0x3f000240006b7cb7 0x020000001fe79e7d 0x8010000000ff3cf3

def z1331 : W := mkw 0x05ffb7ff8401581f 0x882ffdbffc200ac0 0xffffffff9c01fc15 0xfffffffffce00fe0

def z1332 : W := mkw 0xe5ffb7ff842196ff 0x8f2ffdbffc210cb7 0xfdffffff80019ff0 0x7feffffffc000cff

def z1333 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x847df87180000000 0x1423efc38c000000

def z1334 : W := mkw 0x008a480029de0000 0x30045240014ef000 0xf7fff8007ffe000f 0x9fbfffc003fff000

def z1335 : W := mkw 0x01df228c00000004 0x000ef91460000000 0xf5ffff8000000000 0x1faffffc00000000

def z1336 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x25efffff80000000 0x792f7ffffc000000

def z1337 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff8498006127c 0xbfafffc24c003093

def z1338 : W := mkw 0xc00050128c659241 0x2e00028094632c92 0xd212387f9ce7927d 0xfe9091c3fce73c93

def z1339 : W := mkw 0x0020044004011010 0x0801002200200880 0xfbf007f07f01fc17 0xe7df803f83f80fe0

def z1340 : W := mkw 0x03db680029de0000 0x301edb40014ef000 0xf7fff8001cfe000d 0x9fbfffc000e7f000

def z1341 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xf992387fe31e1fff 0xffcc91c3ff18f0ff

def z1342 : W := mkw 0x85ffb7ff8421fb1f 0x8c2ffdbffc210fd8 0xfdffffff8001ff90 0x7feffffffc000ffc

def z1343 : W := mkw 0x0150012052004808 0x400a800902900240 0xfbf007b07f01ec17 0xe7df803d83f80f60

def z1344 : W := mkw 0x0000000056015800 0x4800000002b00ac0 0xfb9007f07f01fc17 0xe7dc803f83f80fe0

def z1345 : W := mkw 0xe08e4a8c2dffb7e4 0x3f047254616ffdbf 0x7b8e078e7fffffff 0xebdc703c73ffffff

def z1346 : W := mkw 0x048fb29fa0902107 0x80247d94fd048108 0x4d8ff98fe0186182 0x5a6c7fcc7f00c30c

def z1347 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf207f67f19fd97 0xe7df903fb3f8cfec

def z1348 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0xde73f87f9f001c16 0xfef39fc3fcf800e0

def z1349 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffff80f9e398 0x7feffffffc07cf1c

def z1350 : W := mkw 0x25ffb7ffd6015cbf 0xc92ffdbffeb00ae5 0xffffffffff01fff7 0xfffffffffff80fff

def z1351 : W := mkw 0x048fa28d00000006 0x80247d1468000000 0x040ff80000000000 0x18207fc000000000

def z1352 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x298e078e60f9e39b 0x894c703c7307cf1c

def z1353 : W := mkw 0x0425b65b80000017 0x80212db2dc000000 0xb46dfe4980000000 0x3da36ff24c000000

def z1354 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8007ff80007 0x87bfffc003ffc000

def z1355 : W := mkw 0x0024c64908440016 0x2001263248422000 0xb66dc6499ce6127d 0xbdb36e324ce73093

def z1356 : W := mkw 0xc0248e49052b9256 0x1e01247248295c92 0xd0123e49831f927e 0xbe8091f24c18fc93

def z1357 : W := mkw 0xc5ffb7ff8421b35f 0x8e2ffdbffc210d9a 0xfdffffff8001f3f0 0x7feffffffc000f9f

def z1358 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xf7ffffff9c001004 0x7fbffffffce00080

def z1359 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x8473f87f80000000 0x1c239fc3fc000000

def z1360 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000001ffe000c 0x0010000000fff000

def z1361 : W := mkw 0x020048007bde0000 0x7010024003def000 0x320c00007ffe000f 0x8990600003fff000

def z1362 : W := mkw 0x028a48007bde0000 0x7014524003def000 0x438200007ffe000f 0x821c100003fff000

def z1363 : W := mkw 0x02204d607fdf5818 0x7811026b03fefac0 0x0a0007f07ffffc1f 0xe050003f83ffffe0

def z1364 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff849fffe000f 0xbfbfffc24ffff000

def z1365 : W := mkw 0x600048000d4f14e0 0x3b000240006a78a7 0x0a0000001f1e1ffe 0x8050000000f8f0ff

def z1366 : W := mkw 0x83704d607ffffb18 0x7c1b826b03ffffd8 0xfbf007f07fffff9f 0xe7df803f83fffffc

def z1367 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5fdfff180000000 0x77afefff8c000000

def z1368 : W := mkw 0xc28e4a8c7fffb344 0x7e14725463fffd9a 0x7b8e078e7ffff3ff 0xebdc703c73ffff9f

def z1369 : W := mkw 0x01ffa7690000001e 0x000ffd3b48000000 0xf5fffff980000000 0x7fafffffcc000000

def z1370 : W := mkw 0xc20048007fff9240 0x7e10024003fffc92 0x020000007fff800f 0x8010000003fffc00

def z1371 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xa7fdfff1ff01fc05 0x153fefff8ff80fe0

def z1372 : W := mkw 0x05db309680000001 0x802ed984b4000000 0xf5fff80600000000 0x1fafffc030000000

def z1373 : W := mkw 0xc024c6cd0c659256 0x2e01263668632c92 0xb66dc7cf9ce7927d 0xfdb36e3e7ce73c93

def z1374 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf7ffffff9c000005 0xffbffffffce00000

def z1375 : W := mkw 0x03db69207bde4808 0x701edb4903def240 0xf7fff9807ffe600f 0x9fbfffcc03fff300

def z1376 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0xf7eff8007cfe000f 0x9fbf7fc003e7f000

def z1377 : W := mkw 0x01db600008440000 0x200edb0000422000 0xf7fff8001ce00001 0x1fbfffc000e70000

def z1378 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x318e078e60f9e399 0xa98c703c7307cf1c

def z1379 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xa7fdf8007ffe000f 0x953fefc003fff000

def z1380 : W := mkw 0xc004c2090c659246 0x2e00261048632c92 0xb66dc0099ce7927d 0x9db36e004ce73c93

def z1381 : W := mkw 0x05dfb3bf8000000f 0x802efd9dfc000000 0x459ff9b600000000 0x422cffcdb0000000

def z1382 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb66fc64f9cff93fd 0xbdb37e327ce7fc9f

def z1383 : W := mkw 0x0571b5738401101b 0x882b8dab9c200880 0xb671fe719c019015 0xb5b38ff38ce00c80

def z1384 : W := mkw 0x020048007fdf5800 0x7810024003fefac0 0x020000007ffe1c0f 0x8010000003fff0e0

def z1385 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xf5f3ffff80000000 0x7faf9ffffc000000

def z1386 : W := mkw 0x020048007bde0000 0x7010024003def000 0x0a0000007ffe1c1f 0x8050000003fff0e0

def z1387 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8067ffe018f 0xdfffffc033fff00c

def z1388 : W := mkw 0x05fbb5f7d601581b 0xc82fddafbeb00ac0 0xcff3f9f7ff007c06 0x567f9fcfbff803e0

def z1389 : W := mkw 0x848fb29f8020a307 0x84247d94fc010518 0x0c0fff8f8001e390 0x78607ffc7c000f1c

def z1390 : W := mkw 0x85ffb7fff2b0eb1f 0xc42ffdbfff958758 0xfdffffffe3f9ef9b 0xffefffffff1fcf7c

def z1391 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffff8007ffe039f 0x9fffffc003fff01c

def z1392 : W := mkw 0x01fb256020900018 0x000fd92b01048000 0xfdfffff060f9e01b 0xffefffff8307cf00

def z1393 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0xf5fff9ff80000000 0x7fafffcffc000000

def z1394 : W := mkw 0x03db68847bde2100 0x701edb4423def108 0xf7fff8067ffe018f 0x9fbfffc033fff00c

def z1395 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x8471f87180061064 0x14238fc38c003083

def z1396 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf99e07fe60f9e39b 0xefccf03ff307cf1c

def z1397 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xd47ff87f80000000 0x7ea3ffc3fc000000

def z1398 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x0461f80180000000 0x10230fc00c000000

def z1399 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x940ff84f80000000 0x3ca07fc27c000000

def z1400 : W := mkw 0x0575b7ff8000001f 0x802badbffc000000 0x8471f87f80000000 0x14238fc3fc000000

def z1401 : W := mkw 0xc024c6cd0c65b356 0x2e01263668632d9a 0xffedc7cffce7f3ff 0xffff6e3e7fe73f9f

def z1402 : W := mkw 0x008b200020900000 0x0004590001048000 0x040ff80000f80008 0x18207fc00007c000

def z1403 : W := mkw 0x0571b5738401581b 0x882b8dab9c200ac0 0x8471f87180001c00 0x14238fc38c0000e0

def z1404 : W := mkw 0x01df228c00000004 0x000ef91460000000 0xf5fff80e00000000 0x1fafffc070000000

def z1405 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xf5ffffff80e7927d 0xffaffffffc073c93

def z1406 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xf5ffffff800003e0 0x7faffffffc00001f

def z1407 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x366dc6099ce78279 0xb9b36e304ce73c13

def z1408 : W := mkw 0x84afb6dfa0b0a317 0x84257db6fd058518 0xb46ffe4f80f98399 0xbda37ff27c07cc1c

def z1409 : W := mkw 0x0421b5738000001b 0x80210dab9c000000 0x0401f87180000000 0x10200fc38c000000

def z1410 : W := mkw 0x0000400008440000 0x2000020000422000 0xb66dc0099ce6026d 0x9db36e004ce73013

def z1411 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff8006000c 0xffaffffffc003000

def z1412 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80e00009 0xffaffffffc070000

def z1413 : W := mkw 0x020048005f4f5800 0x7810024002fa7ac0 0x0a0000007f07fc17 0x8050000003f83fe0

def z1414 : W := mkw 0x05fb35f680000019 0x802fd9afb4000000 0xf5fffff600000000 0x7fafffffb0000000

def z1415 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0x6dffffb660f9e183 0x436ffffdb307cf0c

def z1416 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0x85f1f9f180000000 0x142f8fcf8c000000

def z1417 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xa66dc6499ce7926d 0x1d336e324ce73c93

def z1418 : W := mkw 0x85ffb7ffa4b1fb1f 0x8c2ffdbffd258fd8 0xfdffffffe0f9ff9b 0xffefffffff07cffc

def z1419 : W := mkw 0x028b680029de0000 0x30145b40014ef000 0xf67ff8001ffe000f 0x9fb3ffc000fff000

def z1420 : W := mkw 0x05fbb573d601581b 0xc82fddab9eb00ac0 0xf7fff871ff001c07 0x9fbfffc38ff800e0

def z1421 : W := mkw 0x03704d607fdf5818 0x781b826b03fefac0 0x23e007807fffe00f 0x811f003c03ffff00

def z1422 : W := mkw 0x01db200020900000 0x000ed90001048000 0xf5fff80000f80008 0x1fafffc00007c000

def z1423 : W := mkw 0xc5ffb7ffa4b1b35f 0x8e2ffdbffd258d9a 0xfdffffffe0f9f3fb 0xffefffffff07cf9f

def z1424 : W := mkw 0x20001812810a04a1 0x110000c094085025 0x9012387f831e1ffc 0xbc8091c3fc18f0ff

def z1425 : W := mkw 0x83fe4fec7ffffb1c 0x7c1ff27f63ffffd8 0xfbfe07fe7fffff9f 0xefdff03ff3fffffc

def z1426 : W := mkw 0x85ffb7ffd621fb1f 0xcc2ffdbffeb10fd8 0xffffffffff01ff97 0xfffffffffff80ffc

def z1427 : W := mkw 0x45ffb7ff8401105f 0x8a2ffdbffc200882 0xf5ffffff80001060 0x7faffffffc000083

def z1428 : W := mkw 0x820048007bfe8200 0x7410024003dff410 0x020000007fff821f 0x8010000003fffc10

def z1429 : W := mkw 0x85ffb7fff2b0a31f 0xc42ffdbfff958518 0xfffffffffff9e39f 0xffffffffffffcf1c

def z1430 : W := mkw 0x05dfb29fd2000007 0xc02efd94fe900000 0xf7fff80fff000007 0x9fbfffc07ff80000

def z1431 : W := mkw 0x05dfb29f80000007 0x802efd94fc000000 0xf5fff87f80000000 0x7fafffc3fc000000

def z1432 : W := mkw 0x01fb256000000018 0x000fd92b00000000 0xf5ffff8000000000 0x1faffffc00000000

def z1433 : W := mkw 0x27db39b6f39a04a9 0xd13ed9cdb79cd025 0x499239b663180d82 0x424c91cdb318c06c

def z1434 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0xf5fff9f780000000 0x5fafffcfbc000000

def z1435 : W := mkw 0x0575b7ff8000001f 0x802badbffc000000 0xf5f1ffff80000000 0x77af8ffffc000000

def z1436 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf98e07cfe0f9e39b 0xffcc703e7f07cf1c

def z1437 : W := mkw 0x05ffb7ffa090211f 0x802ffdbffd048108 0xf5ffffffe0006000 0x7fafffffff000300

def z1438 : W := mkw 0xc4afb6df84219257 0x8e257db6fc210c92 0x040ffe4f80019270 0x38207ff27c000c93

def z1439 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd99239ffe31e7ffe 0xfecc91cfff18f3ff

def z1440 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xa7fdf8007ce00001 0x153fefc003e70000

def z1441 : W := mkw 0x0405b21b80000007 0x80202d90dc000000 0x040df80980000000 0x18206fc04c000000

def z1442 : W := mkw 0x01db212000000008 0x000ed90900000000 0xf5fff9b000000000 0x5fafffcd80000000

def z1443 : W := mkw 0x020048007bde4800 0x7010024003def240 0x0a0000007ffe6c0f 0x8050000003fff360

def z1444 : W := mkw 0x25ffb7ff800004bf 0x812ffdbffc000025 0xfdffffff80000d80 0x7feffffffc00006c

def z1445 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x867ff8007ffe000f 0x9c33ffc003fff000

def z1446 : W := mkw 0x81ffa6cd20b0a316 0x040ffd3669058518 0xfdffffcfe0f9e39b 0xffeffffe7f07cf1c

def z1447 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0x8671f8719c000000 0x14338fc38ce00000

def z1448 : W := mkw 0x2571b573800004bb 0x812b8dab9c000025 0x8471f87180001c60 0x14238fc38c0000e3

def z1449 : W := mkw 0x0020945380000013 0x000104a29c000000 0x8471f87180000000 0x14238fc38c000000

def z1450 : W := mkw 0x20004800094e04a0 0x31000240004a7025 0x0a0000001ffe1fff 0x8050000000fff0ff

def z1451 : W := mkw 0x020048007bde0000 0x7010024003def000 0x0000000063fe000a 0x00000000031ff000

def z1452 : W := mkw 0xc20048007bfe8240 0x7610024003dff412 0x020000007ffe026f 0x8010000003fff013

def z1453 : W := mkw 0x05ffa7ed0000001e 0x802ffd3f68000000 0xf5ffffc980000000 0x3faffffe4c000000

def z1454 : W := mkw 0x85ffb7ffa4b1b31f 0x8c2ffdbffd258d98 0xfffffffffcf9f39f 0xffffffffffe7cf9c

def z1455 : W := mkw 0xa20048007bfea7a0 0x7510024003dff53d 0x0a0000007fffffff 0x8050000003ffffff

def z1456 : W := mkw 0x008a008420902100 0x0004500421048108 0x798e078660f9e19b 0xebcc703c3307cf0c

def z1457 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd012387f831e1fee 0x9e8091c3fc18f0ff

def z1458 : W := mkw 0x048fb29fa0900007 0x80247d94fd048000 0x758ff80fe0f8000b 0x9bac7fc07f07c000

def z1459 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8407ffe101f 0xbfbfffc203fff080

def z1460 : W := mkw 0x0571a5615601581a 0xc82b8d2b0ab00ac0 0xfff1c7f07f01fc17 0xe7ff8e3f83f80fe0

def z1461 : W := mkw 0x008f228c00000004 0x0004791460000000 0x758fff8e00000000 0x7bac7ffc70000000

def z1462 : W := mkw 0x85ffb7fff6b1fb1f 0xcc2ffdbfffb58fd8 0xffffffffffe1fc17 0xffffffffffff0fe0

def z1463 : W := mkw 0xe024965b842196f7 0x0f0124b2dc210cb7 0x0000064f800193f0 0x200000327c000c9f

def z1464 : W := mkw 0x01db208420902100 0x000ed90421048108 0xfdfff98660186182 0x5fefffcc3300c30c

def z1465 : W := mkw 0x03db68847bde2100 0x701edb4423def108 0xffffff867fffe19f 0xfffffffc33ffff0c

def z1466 : W := mkw 0xa28e4a8c7bfea7a4 0x7514725463dff53d 0x7b8e078e7fffffff 0xebdc703c73ffffff

def z1467 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8707ffe1c0f 0x9fbfffc383fff0e0

def z1468 : W := mkw 0x0575b7ff8000001f 0x802badbffc000000 0x8471fff180000000 0x14238fff8c000000

def z1469 : W := mkw 0x820048007bfea300 0x7410024003dff518 0x020000007fffe00f 0x8010000003ffff00

def z1470 : W := mkw 0xc20048005f6f9240 0x7e10024002fb7c92 0x020000001fe7927d 0x8010000000ff3c93

def z1471 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff841fffe106f 0x9fbfffc20ffff083

def z1472 : W := mkw 0x05fbb573a090001b 0x802fddab9d048000 0xf5fff871e0f8000b 0x9fafffc38f07c000

def z1473 : W := mkw 0x01db200052000000 0x400ed90002900000 0xf7fff8007c000001 0x1fbfffc003e00000

def z1474 : W := mkw 0x81db200020b0a300 0x040ed90001058518 0xfdfff80060f9e39b 0x9fefffc00307cf1c

def z1475 : W := mkw 0xc3704d607fffda58 0x7e1b826b03fffed2 0xfbf007f07ffffe7f 0xe7df803f83fffff3

def z1476 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff80e7ffe000f 0xffbfffc073fff000

def z1477 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf207ffff1fffff 0xffdf903ffff8ffff

def z1478 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xf7ffffff9c018001 0x7fbffffffce00c00

def z1479 : W := mkw 0xe00048005f6fdee0 0x7f00024002fb7ef7 0x0a0000007fffffff 0x8050000003ffffff

def z1480 : W := mkw 0x0571b5738401101b 0x882b8dab9c200880 0x8671f8719c001004 0x14338fc38ce00080

def z1481 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x266dc6019ce78061 0x11336e300ce73c03

def z1482 : W := mkw 0x248fb29f800004a7 0x81247d94fc000025 0x040ff80f800003e0 0x18207fc07c00001f

def z1483 : W := mkw 0x0150000052000000 0x400a800002900000 0xfbf007f07f01fc17 0xe7df803f83f80fe0

def z1484 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x67fff8007ffe000b 0x1b3fffc003fff000

def z1485 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff80000390 0x7feffffffc00001c

def z1486 : W := mkw 0xc024c7690c65925e 0x2e01263b48632c92 0xb66dc7f99ce7927d 0xfdb36e3fcce73c93

def z1487 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x698e078e60f9e38b 0x4b4c703c7307cf1c

def z1488 : W := mkw 0x420048005f4f1040 0x7a10024002fa7882 0x020000001f061064 0x0010000000f83083

def z1489 : W := mkw 0xc024c7690c65da5e 0x2e01263b48632ed2 0xb66dc7c99ce7f27d 0xbdb36e3e4ce73f93

def z1490 : W := mkw 0x05ffb7ffd601101f 0xc82ffdbffeb00880 0xf7ffffffff019017 0xffbffffffff80c80

def z1491 : W := mkw 0xe0044a080d6f96e4 0x3f002250406b7cb7 0x7a0e060e1fff9fff 0xebd0703070fffcff

def z1492 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x258fff8f80000000 0x192c7ffc7c000000

def z1493 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0x866dc6499ce7927c 0x3c336e324ce73c93

def z1494 : W := mkw 0x01df329e80000005 0x000ef994f4000000 0xf5ffffff80000000 0x7faffffffc000000

def z1495 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe019e392 0x7fefffffff00cf1c

def z1496 : W := mkw 0x4024c6490c451056 0x2a01263248622882 0xb66dc6499ce6106d 0xbdb36e324ce73083

def z1497 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x798e07cfe0f9f3fb 0xebcc703e7f07cf9f

def z1498 : W := mkw 0x0151600008440000 0x200a8b0000422000 0xb67df8001ce6000d 0x9db3efc000e73000

def z1499 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xfdffffffe0e1e391 0x7fefffffff070f1c

def z1500 : W := mkw 0x220048007bde04a0 0x7110024003def025 0x020000007ffe1c6f 0x8010000003fff0e3

def z1501 : W := mkw 0xc024c64908648256 0x2601263248432412 0xb66dc6499ce6026d 0xbdb36e324ce73013

def z1502 : W := mkw 0x01ffa64956011016 0x480ffd324ab00880 0xf7fffe49ff019017 0xbfbffff24ff80c80

def z1503 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xffefc7cffcfff3ff 0xffff7e3e7fe7ff9f

def z1504 : W := mkw 0x035168005b4e0000 0x701a8b4002da7000 0xa67df8001fe60005 0x1533efc000ff3000

def z1505 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xfbee078e7cf9e39f 0xefdf703c73e7cf1c

def z1506 : W := mkw 0x03db60007ad40000 0x601edb0003d6a000 0xf7fff8007ce6000d 0x9fbfffc003e73000

def z1507 : W := mkw 0xc5ffb7ff8421925f 0x8e2ffdbffc210c92 0xf7ffffff9c019275 0xffbffffffce00c93

def z1508 : W := mkw 0x82044a8c7bfea304 0x7410225463dff518 0x0a00078e7fffe39f 0xe050003c73ffff1c

def z1509 : W := mkw 0x05ffa7ed5601581e 0xc82ffd3f6ab00ac0 0xfffffff07f01fc17 0xffffffff83f80fe0

def z1510 : W := mkw 0x05ffb7ffa090001f 0x802ffdbffd048000 0xf5ffffffe0180002 0x7fafffffff00c000

def z1511 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0x9471f8798006127c 0xbca38fc3cc003093

def z1512 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xffffffffff007c06 0x7ffffffffff803e0

def z1513 : W := mkw 0x01fb244000000010 0x000fd92200000000 0xf5fffe4000000000 0x3faffff200000000

def z1514 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7ffff807ffe000f 0xffbffffc03fff000

def z1515 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x718e078e60f9e389 0x6b8c703c7307cf1c

def z1516 : W := mkw 0x01fb256056015818 0x480fd92b02b00ac0 0xf7fff8701f001c04 0x1fbfffc380f800e0

def z1517 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf99e07ffe3ffffff 0xffccf03fff1fffff

def z1518 : W := mkw 0x020048007fdf5800 0x7810024003fefac0 0x020000007fffe00f 0x8010000003ffff00

def z1519 : W := mkw 0x0004921b80000007 0x00002490dc000000 0xd41ff87f80000000 0x7ea0ffc3fc000000

def z1520 : W := mkw 0x0171256056015818 0x480b892b02b00ac0 0x8671f8701f001c04 0x14338fc380f800e0

def z1521 : W := mkw 0x01ffa64900000016 0x000ffd3248000000 0xf5fffe0000000000 0x1faffff000000000

def z1522 : W := mkw 0x020048007fdf1000 0x7810024003fef880 0x020000007fff901f 0x8010000003fffc80

def z1523 : W := mkw 0x020048007bde0000 0x7010024003def000 0x920000007ffe000f 0x9c90000003fff000

def z1524 : W := mkw 0x4000c00108440042 0x2200060008422002 0xb66dc0019ce6006d 0x9db36e000ce73003

def z1525 : W := mkw 0x05ffb7ff8401581f 0x882ffdbffc200ac0 0xf5ffffff8001e000 0x7faffffffc000f00

def z1526 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xf7edc7c99ce7927d 0xffbf6e3e4ce73c93

def z1527 : W := mkw 0x05ffb7ffa090211f 0x802ffdbffd048108 0xf5ffffff80180180 0x7faffffffc00c00c

def z1528 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xfffffff07ffffc1f 0xffffffff83ffffe0

def z1529 : W := mkw 0x0174977b8000001f 0x000ba4bbdc000000 0xf5ffffff80000000 0x7faffffffc000000

def z1530 : W := mkw 0x05ffb7ffd200481f 0xc02ffdbffe900240 0xffffffffff006c07 0xfffffffffff80360

def z1531 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x5c0ff80f8018039a 0xfae07fc07c00c01c

def z1532 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xb5fdfff980000000 0x3dafefffcc000000

def z1533 : W := mkw 0x00afa64900000016 0x00057d3248000000 0xb46ffe4980000000 0x3da37ff24c000000

def z1534 : W := mkw 0x020048007bde0000 0x7010024003def000 0xd21000007ffe000f 0x8690800003fff000

def z1535 : W := mkw 0x03db68007bde2100 0x701edb4003def108 0xfffff8007ffe618f 0x9fffffc003fff30c

def z1536 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x498e078e60f9e39a 0x6a4c703c7307cf1c

def z1537 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff83000c02 0x7feffffffc180060

def z1538 : W := mkw 0xc00040000c659240 0x2e00020000632c92 0xb66dc0499ce7927d 0xbdb36e024ce73c93

def z1539 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007b07f01ec07 0xc7df803d83f80f60

def z1540 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x698e078e60f9e393 0x634c703c7307cf1c

def z1541 : W := mkw 0x8200480029fea300 0x34100240014ff518 0x0000000000fe0388 0x000000000007f01c

def z1542 : W := mkw 0x23db3932f39a4ca9 0x511ed9c9979cd265 0x499239b663186d82 0x424c91cdb318c36c

def z1543 : W := mkw 0xc024c6490c659256 0x2e01263248632c92 0xb7edc7c9fce7f27d 0xbdbf6e3e4fe73f93

def z1544 : W := mkw 0x01db200000000000 0x000ed90000000000 0xfdfff80e0018039a 0xffefffc07000c01c

def z1545 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80180388 0x7faffffffc00c01c

def z1546 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xa5fdffff80000000 0x752feffffc000000

def z1547 : W := mkw 0x03704d605f4f5818 0x781b826b02fa7ac0 0x827000701f061c04 0x0413800380f830e0

def z1548 : W := mkw 0x008fa20900000006 0x00047d1048000000 0x040ff80980000000 0x18207fc04c000000

def z1549 : W := mkw 0x8575b7ff8020a31f 0x842badbffc010518 0x8c71ffff8001e390 0x74638ffffc000f1c

def z1550 : W := mkw 0x05ffb7ff8401581f 0x882ffdbffc200ac0 0xfdffffffe001fc13 0xffefffffff000fe0

def z1551 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xf9923fff831e1ffe 0xffcc91fffc18f0ff

def z1552 : W := mkw 0x0571b573d601581b 0xc82b8dab9eb00ac0 0x8e71f871ff01fc17 0x94738fc38ff80fe0

def z1553 : W := mkw 0x85ffb7ff8421921f 0x8c2ffdbffc210c90 0xf7ffffff9ce1921d 0xffbffffffce70c90

def z1554 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0x27eff8007ffe000f 0x993f7fc003fff000

def z1555 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0xc5f3f9b600000000 0x562f9fcdb0000000

def z1556 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xb47df87180000000 0x1da3efc38c000000

def z1557 : W := mkw 0x05fbb5738000001b 0x802fddab9c000000 0xc5f3f87180000000 0x162f9fc38c000000

def z1558 : W := mkw 0xe024965b842196f7 0x0f0124b2dc210cb7 0x0000067980019e70 0x20000033cc000cf3

def z1559 : W := mkw 0x85ffb7ffa0b0821f 0x842ffdbffd058410 0xf5ffffffe0f9821b 0xffafffffff07cc10

def z1560 : W := mkw 0x01db200052000000 0x400ed90002900000 0xf5fff80063000002 0x1fafffc003180000

def z1561 : W := mkw 0x008b200000000000 0x0004590000000000 0xd41ff80000000000 0x1ea0ffc000000000

def z1562 : W := mkw 0xc020c4410c659252 0x2e01062208632c92 0xb66dc0419ce7927d 0x9db36e020ce73c93

def z1563 : W := mkw 0x048fb29f80000007 0x80247d94fc000000 0x7d8fff8fe001e013 0xfbec7ffc7f000f00

def z1564 : W := mkw 0x05ffb7fff290691f 0xc02ffdbfff948348 0xfdffffffe3186d82 0x7fefffffff18c36c

def z1565 : W := mkw 0x417085615601585a 0x4a0b842b0ab00ac2 0xfbf007f1ff01fc77 0xe7df803f8ff80fe3

def z1566 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0x8473f87780000000 0x14239fc3bc000000

def z1567 : W := mkw 0x848fb29f80208207 0x84247d94fc010410 0x340ffe0f80e18219 0xb9a07ff07c070c10

def z1568 : W := mkw 0x0571b573d200001b 0xc02b8dab9e900000 0xf7f1f871ff000007 0x97bf8fc38ff80000

def z1569 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff83001c04 0x7faffffffc1800e0

def z1570 : W := mkw 0x04afb7ff8000001f 0x80257dbffc000000 0x040fff8f80000000 0x18207ffc7c000000

def z1571 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0x27efff8ffc01e001 0x193f7ffc7fe00f00

def z1572 : W := mkw 0x23db68007bde04a0 0x711edb4003def025 0xfffff849fffe1fff 0xbfffffc24ffff0ff

def z1573 : W := mkw 0x835048007bfea300 0x741a824003dff518 0xfbf007807fffe39f 0xe7df803c03ffff1c

def z1574 : W := mkw 0x8575b77b8020821f 0x842badbbdc010410 0xb47dfe7980e18219 0xbda3eff3cc070c10

def z1575 : W := mkw 0x01db200052000000 0x400ed90002900000 0xf7fff8001f000004 0x1fbfffc000f80000

def z1576 : W := mkw 0x01db200000000000 0x000ed90000000000 0xf5fff87000000000 0x7fafffc380000000

def z1577 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xf8123e7f831f9fff 0xffc091f3fc18fcff

def z1578 : W := mkw 0x01fb244004011010 0x080fd92200200880 0xf7fffe401c019015 0xbfbffff200e00c80

def z1579 : W := mkw 0x20001812810a04a1 0x110000c094085025 0xd812387fe31fffff 0xfec091c3ff18ffff

def z1580 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbfc07f07fe1fc1f 0xefdfe03f83ff0fe0

def z1581 : W := mkw 0x020048007bde0000 0x7010024003def000 0x020000007f1e0006 0x0010000003f8f000

def z1582 : W := mkw 0x23db3896f39a25a1 0x511ed9c4b79cd12d 0x499239b663186d82 0x424c91cdb318c36c

def z1583 : W := mkw 0x01db301280000001 0x000ed98094000000 0xf5fff87180000000 0x1fafffc38c000000

def z1584 : W := mkw 0x81ff27ec20b0a31c 0x040ff93f61058518 0xfdfffffe60f9e39b 0xffeffffff307cf1c

def z1585 : W := mkw 0x01fb357280000019 0x000fd9ab94000000 0xf5ffffff80000000 0x7faffffffc000000

def z1586 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0xf98e07ce60f9f39f 0xefcc703e7307cf9c

def z1587 : W := mkw 0x05ffb7ffd601581f 0xc82ffdbffeb00ac0 0xfffffffffc01e013 0xffffffffffe00f00

def z1588 : W := mkw 0x05ffb7ffa090001f 0x802ffdbffd048000 0xfdffffffe0f9e01b 0xffefffffff07cf00

def z1589 : W := mkw 0x04afb6df84011017 0x88257db6fc200880 0xb66ffe4f9c019015 0xbdb37ff27ce00c80

def z1590 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8087ffe021f 0xbfbfffc043fff010

def z1591 : W := mkw 0x05fba5610000001a 0x802fdd2b08000000 0xf5fff80000000000 0x1fafffc000000000

def z1592 : W := mkw 0x020048007bde0000 0x7010024003def000 0x7b8007807fffe01f 0xe3dc003c03ffff00

def z1593 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xfdffffffe0e1e21b 0xffefffffff070f10

def z1594 : W := mkw 0x0151301280000001 0x000a898094000000 0x8471f87180000000 0x14238fc38c000000

def z1595 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffb600000000 0x5faffffdb0000000

def z1596 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffffe0000003 0xffafffffff000000

def z1597 : W := mkw 0x85ffb7ffa0b0a31f 0x842ffdbffd058518 0xf5ffffffe0f9e00b 0xffafffffff07cf00

def z1598 : W := mkw 0x85ffb7ff8020821f 0x842ffdbffc010410 0xf5ffffff80018210 0x7faffffffc000c10

def z1599 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0xd5f3f9ff80000000 0x7eaf9fcffc000000

def z1600 : W := mkw 0x05fbb5f78000001b 0x802fddafbc000000 0xf5f3fff780000000 0x77af9fffbc000000

def z1601 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0x65ffffbf80000000 0x5b2ffffdfc000000

def z1602 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff809fffe026f 0x9fbfffc04ffff013

def z1603 : W := mkw 0x848fb29f8020a307 0x84247d94fc010518 0x040ff80f80000380 0x18207fc07c00001c

def z1604 : W := mkw 0x0020945380000013 0x000104a29c000000 0xd473f87f80000000 0x7ea39fc3fc000000

def z1605 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xf5ffffff80060268 0x7faffffffc003013

def z1606 : W := mkw 0xc20048002dff9240 0x3e100240016ffc92 0x020000001cff927d 0x8010000000e7fc93

def z1607 : W := mkw 0x05ffa7ed5601581e 0xc82ffd3f6ab00ac0 0xf7ffff807f01e007 0x9fbffffc03f80f00

def z1608 : W := mkw 0xe00048002dffb7e0 0x3f000240016ffdbf 0x0a0000007fffffff 0x8050000003ffffff

def z1609 : W := mkw 0xe20048007fff96e0 0x7f10024003fffcb7 0x0a0000007fff9fff 0x8050000003fffcff

def z1610 : W := mkw 0xc3704c407fff9250 0x7e1b826203fffc92 0xf3f006407fff927f 0xa79f803203fffc93

def z1611 : W := mkw 0x05ffb7ff8000001f 0x802ffdbffc000000 0xfdffffff80000012 0xffeffffffc000000

def z1612 : W := mkw 0x220048005b4e04a0 0x7110024002da7025 0x020000001f061c64 0x0010000000f830e3

def z1613 : W := mkw 0xc48fb29f80208247 0x86247d94fc010412 0x040ff80f80000260 0x18207fc07c000013

def z1614 : W := mkw 0x035048005b4e0000 0x701a824002da7000 0x827000001f060004 0x0413800000f83000

def z1615 : W := mkw 0x85dfb3bfa0b0a30f 0x842efd9dfd058518 0x4d9ff9bfe0f8638a 0x5a6cffcdff07c31c

def z1616 : W := mkw 0x808e028c20b0a304 0x0404701461058518 0x298e078e60f9e399 0x694c703c7307cf1c

def z1617 : W := mkw 0x0571b5738000001b 0x802b8dab9c000000 0xdc73f87f8018039a 0xfee39fc3fc00c01c

def z1618 : W := mkw 0x0024965b80000017 0x000124b2dc000000 0xb46ffe4f80000000 0x3da37ff27c000000

def z1619 : W := mkw 0x048fb29fa0900007 0x80247d94fd048000 0x040ff80f80f80008 0x18207fc07c07c000

def z1620 : W := mkw 0x820048007bfea300 0x7410024003dff518 0x020000007ffe038f 0x8010000003fff01c

def z1621 : W := mkw 0x0170056056015818 0x480b802b02b00ac0 0xfbf007f07f07fc1f 0xffdf803f83f83fe0

def z1622 : W := mkw 0x05ffb7ff8401101f 0x882ffdbffc200880 0xfffffffffc01f017 0xffffffffffe00f80

def z1623 : W := mkw 0x05db31b680000009 0x802ed98db4000000 0x459ff9b600000000 0x5a2cffcdb0000000

def z1624 : W := mkw 0x03db68007bde0000 0x701edb4003def000 0xf7fff8007cfe0009 0x1fbfffc003e7f000

def z1625 : W := mkw 0xa5ffb7ff8020a7bf 0x852ffdbffc01053d 0xfdffffff8001fff0 0x7feffffffc000fff

def z1626 : W := mkw 0xc20048007fffb340 0x7e10024003fffd9a 0x0a0000007ffff3ff 0x8050000003ffff9f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z3,z4,z6]),(0,[z8,z0,z1,z9,z10,z4,z6]),(0,[z11,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z12,z4,z13,z6]),(0,[z14,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z15,z3,z4,z6]),(0,[z0,z16,z1,z3,z4,z17,z6]),(0,[z0,z1,z2,z3,z18,z4,z6]),(0,[z19,z0,z20,z1,z3,z4,z6]),(0,[z0,z21,z1,z3,z4,z6,z22])],[(0,[z0,z1,z9,z3,z23,z4,z6])],[(0,[z24,z0,z1,z25,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z26,z6]),(0,[z27,z0,z16,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z28]),(0,[z0,z1,z9,z29,z3,z4,z6]),(0,[z30,z31,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z32,z6])],[(0,[z33,z0,z34,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z35,z6]),(0,[z36,z0,z1,z9,z3,z4,z37]),(1,[z38,z0,z9,z3,z4,z6])],[(0,[z0,z20,z1,z3,z4,z39,z6])],[(1,[z0,z1,z40,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z41,z6]),(1,[z0,z42,z3,z10,z4,z6]),(0,[z30,z0,z43,z9,z3,z4,z6])],[(0,[z0,z1,z44,z40,z3,z4,z6]),(0,[z0,z42,z20,z9,z3,z4,z6]),(0,[z45,z0,z20,z1,z3,z4,z6]),(0,[z0,z46,z1,z9,z3,z4,z6]),(0,[z47,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z48,z6])],[(0,[z0,z1,z3,z18,z4,z49,z6]),(0,[z0,z1,z9,z3,z4,z6,z50])],[(0,[z33,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z51,z3,z52,z4,z6]),(0,[z0,z1,z9,z3,z53,z4,z6]),(1,[z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z9,z3,z54,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z55])],[(0,[z0,z1,z51,z3,z56,z4,z6]),(0,[z0,z1,z40,z3,z4,z6,z37]),(0,[z57,z0,z1,z9,z3,z4,z6]),(1,[z0,z1,z58,z3,z4,z6]),(0,[z59,z0,z1,z9,z3,z4,z41]),(0,[z0,z60,z9,z3,z12,z4,z6])],[],[(0,[z0,z1,z2,z9,z3,z61,z6])],[(0,[z62,z0,z1,z40,z3,z4,z6]),(1,[z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z0,z1,z9,z3,z4,z63,z6])],[(0,[z0,z1,z9,z64,z3,z4,z6]),(0,[z0,z1,z65,z3,z4,z17,z6])],[(1,[z0,z66,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z67,z4,z6]),(1,[z0,z68,z1,z3,z4,z6]),(0,[z0,z1,z69,z3,z4,z39,z6])]],
   [[(0,[z0,z70,z16,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z71,z6]),(0,[z0,z1,z40,z3,z4,z72,z6])],[(0,[z0,z73,z74,z9,z3,z4,z6]),(0,[z0,z75,z9,z3,z4,z76,z6]),(0,[z0,z1,z77,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z78,z4,z6])],[],[(0,[z33,z0,z79,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z80,z4,z6]),(0,[z0,z81,z1,z2,z3,z4,z6])],[(0,[z0,z1,z82,z3,z4,z17,z6]),(0,[z36,z0,z1,z2,z3,z4,z6])],[(0,[z33,z0,z1,z83,z3,z4,z6]),(0,[z19,z0,z1,z9,z3,z84,z4]),(0,[z0,z1,z3,z4,z17,z6,z85]),(0,[z0,z1,z86,z9,z3,z4,z6])],[(0,[z0,z1,z9,z87,z3,z4,z6]),(0,[z88,z0,z42,z1,z3,z4,z6]),(1,[z0,z1,z9,z3,z89,z4])],[(0,[z0,z1,z90,z40,z3,z4,z6]),(1,[z0,z1,z91,z3,z4,z6])],[(0,[z0,z1,z9,z92,z3,z4,z6]),(0,[z0,z1,z9,z3,z93,z4,z6]),(0,[z36,z0,z1,z94,z3,z4,z6]),(0,[z0,z1,z9,z95,z3,z4,z6]),(1,[z0,z1,z9,z82,z4,z72])],[(0,[z59,z0,z1,z40,z3,z4,z6]),(0,[z96,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z9,z3,z4,z6]),(0,[z97,z1,z40,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z89,z10,z4])],[(0,[z98,z0,z1,z9,z3,z4,z99]),(0,[z0,z1,z3,z4,z17,z100,z6])],[(0,[z101,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z102,z9,z3,z4,z6]),(0,[z103,z0,z1,z9,z3,z4,z6]),(0,[z30,z0,z1,z104,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z105,z6])],[(0,[z0,z1,z106,z40,z3,z4,z6]),(0,[z0,z107,z1,z9,z3,z4,z6]),(0,[z108,z0,z1,z109,z3,z4,z6]),(0,[z110,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z111,z6]),(0,[z0,z1,z3,z4,z17,z39,z6]),(0,[z0,z1,z9,z3,z4,z112,z6]),(0,[z113,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z114,z4,z6])],[(0,[z0,z1,z9,z3,z115,z4,z6]),(0,[z0,z1,z9,z3,z116,z4,z6]),(0,[z0,z1,z2,z117,z3,z4,z6])],[(1,[z0,z1,z118,z3,z4,z6]),(0,[z119,z1,z9,z3,z120,z4,z6]),(0,[z59,z119,z1,z9,z3,z4,z6]),(1,[z0,z1,z121,z3,z4,z6])]],
   [[(0,[z0,z1,z40,z3,z4,z6,z22])],[(0,[z0,z20,z1,z122,z3,z4,z6]),(1,[z0,z1,z9,z3,z4,z123]),(0,[z0,z1,z9,z3,z61,z4,z6]),(0,[z0,z1,z3,z124,z4,z17,z6])],[(1,[z24,z106,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z125])],[(0,[z101,z0,z42,z1,z3,z4,z6]),(0,[z0,z126,z1,z9,z3,z4,z6])],[(0,[z0,z127,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z94,z3,z4,z6]),(0,[z0,z1,z9,z128,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z129]),(1,[z57,z1,z9,z122,z4,z6])],[(0,[z0,z1,z2,z3,z130,z4,z6]),(0,[z0,z1,z9,z3,z4,z131,z6]),(1,[z0,z132,z9,z3,z4,z6])],[(0,[z0,z75,z73,z9,z3,z4,z6]),(0,[z133,z0,z1,z9,z3,z4,z6]),(0,[z134,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z135,z3,z18,z4,z6]),(0,[z0,z1,z9,z3,z136,z4,z6]),(0,[z0,z9,z3,z4,z137,z76,z6]),(0,[z0,z1,z9,z138,z3,z4,z6])],[(0,[z0,z106,z9,z3,z4,z76,z6]),(0,[z0,z42,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z139,z4,z6])],[(0,[z0,z1,z9,z3,z84,z4,z55])],[(0,[z0,z1,z40,z3,z84,z4,z6]),(0,[z0,z1,z9,z3,z4,z140,z6]),(0,[z0,z1,z9,z3,z84,z4,z72])],[(0,[z19,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z84,z4,z41]),(0,[z0,z42,z1,z3,z114,z4,z6]),(0,[z141,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z142,z4,z6])],[(1,[z62,z1,z51,z3,z4,z6]),(0,[z143,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z41,z55]),(0,[z0,z1,z3,z4,z144,z17,z6])],[(0,[z0,z1,z9,z3,z4,z145,z6]),(1,[z0,z146,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z41,z72]),(0,[z0,z42,z1,z2,z3,z4,z6]),(0,[z0,z1,z147,z3,z4,z17,z6]),(0,[z0,z1,z9,z148,z3,z4,z6]),(0,[z149,z0,z1,z9,z3,z4,z6])]],
   [[(0,[z0,z1,z51,z150,z3,z4,z6]),(0,[z0,z42,z1,z3,z61,z4,z6])],[(0,[z0,z1,z9,z151,z3,z4,z6])],[(0,[z45,z0,z1,z51,z3,z4,z6]),(0,[z152,z0,z1,z153,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z154])],[(0,[z155,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z100,z6]),(0,[z0,z42,z1,z94,z3,z4,z6]),(0,[z0,z1,z9,z147,z3,z4,z6]),(0,[z156,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z137,z6]),(0,[z0,z157,z1,z9,z3,z4,z6]),(0,[z158,z0,z1,z9,z3,z4,z6])],[(0,[z19,z0,z1,z9,z3,z4,z159]),(0,[z0,z1,z9,z3,z160,z4,z6])],[(0,[z0,z1,z51,z3,z4,z161,z6]),(0,[z0,z73,z1,z40,z3,z4,z6]),(1,[z59,z1,z9,z3,z4,z159]),(0,[z0,z1,z147,z3,z162,z4,z6]),(0,[z0,z1,z163,z3,z4,z17,z6]),(0,[z101,z0,z1,z9,z3,z114,z6])],[(0,[z0,z1,z135,z9,z3,z4,z6]),(0,[z30,z0,z20,z1,z3,z4,z6]),(1,[z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z164,z4,z6])],[],[(0,[z0,z1,z51,z3,z165,z4,z6]),(0,[z0,z1,z9,z122,z4,z131,z6])],[(0,[z166,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z167,z6])],[(0,[z0,z1,z65,z51,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z7,z3,z4,z6]),(0,[z0,z9,z3,z10,z4,z137,z6]),(0,[z0,z168,z1,z9,z3,z4,z6])],[(0,[z0,z20,z1,z3,z18,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z169])],[(0,[z170,z0,z1,z9,z3,z4,z6])],[(0,[z171,z0,z1,z9,z3,z4,z6]),(0,[z62,z0,z1,z3,z4,z17,z6]),(0,[z172,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z173,z6]),(1,[z0,z1,z3,z162,z4,z6]),(0,[z0,z1,z3,z4,z6,z174,z55]),(1,[z0,z175,z9,z3,z4,z6])],[]],
   [[(0,[z62,z0,z20,z1,z3,z4,z6]),(0,[z176,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z177,z3,z4,z6]),(0,[z0,z60,z1,z2,z3,z4,z6]),(0,[z0,z1,z65,z3,z4,z6,z37])],[(0,[z178,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z74,z2,z3,z4,z6])],[(0,[z0,z1,z40,z3,z179,z4,z6]),(0,[z0,z42,z1,z147,z3,z4,z6]),(0,[z8,z0,z1,z9,z3,z4,z6]),(1,[z0,z1,z180,z3,z4,z6]),(1,[z0,z1,z181,z3,z4,z6])],[(0,[z152,z0,z1,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z137,z6]),(1,[z0,z1,z3,z4,z6,z174])],[(0,[z0,z182,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z72,z159]),(0,[z0,z20,z1,z3,z4,z6,z55]),(0,[z183,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z184])],[(0,[z0,z1,z3,z185,z10,z4,z6])],[(0,[z0,z1,z186,z9,z3,z4,z6])],[(0,[z0,z1,z40,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z159]),(1,[z31,z1,z9,z3,z4,z6])],[(0,[z0,z1,z187,z9,z3,z4,z6]),(0,[z188,z0,z1,z3,z4,z6,z55])],[(1,[z0,z1,z9,z3,z4,z129]),(0,[z59,z0,z1,z3,z4,z17,z6]),(0,[z189,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z190,z6,z191])],[(0,[z0,z1,z9,z192,z3,z4,z6]),(1,[z0,z43,z9,z3,z4,z6])],[(0,[z0,z106,z9,z3,z10,z4,z6]),(0,[z59,z0,z20,z1,z3,z4,z6]),(0,[z0,z73,z9,z147,z3,z4,z6])],[(1,[z0,z1,z193,z3,z4,z6]),(0,[z0,z73,z9,z3,z4,z137,z6]),(0,[z19,z0,z1,z9,z82,z3,z4]),(0,[z101,z0,z1,z3,z4,z17,z6])],[(0,[z0,z1,z106,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z194,z6]),(0,[z0,z1,z9,z3,z195,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z196])],[(0,[z197,z0,z1,z9,z3,z4,z6]),(0,[z198,z0,z1,z9,z3,z4,z6]),(0,[z57,z0,z1,z9,z122,z4,z6]),(0,[z0,z1,z9,z199,z3,z4,z6]),(0,[z0,z200,z1,z9,z3,z4,z6])]],
   [[],[(0,[z0,z1,z9,z201,z3,z4,z6]),(0,[z0,z202,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z203]),(0,[z0,z1,z180,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z204,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z205])],[(0,[z98,z0,z1,z15,z3,z4,z6]),(0,[z98,z0,z1,z206,z3,z4,z6]),(1,[z0,z1,z207,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z72,z6]),(0,[z57,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z9,z3,z4,z6])],[(0,[z0,z1,z208,z9,z3,z4,z6]),(0,[z0,z209,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z210]),(0,[z0,z1,z9,z3,z131,z6,z191]),(0,[z101,z0,z175,z9,z3,z4,z6])],[(1,[z0,z1,z9,z211,z4,z6]),(0,[z119,z0,z1,z212,z3,z4,z6]),(0,[z108,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z213,z6]),(0,[z0,z1,z9,z3,z214,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z215]),(0,[z30,z0,z1,z9,z3,z131,z6]),(0,[z216,z0,z1,z9,z3,z4,z6])],[],[(0,[z0,z1,z217,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z6,z159]),(0,[z0,z1,z9,z3,z4,z6,z218]),(0,[z0,z74,z9,z7,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z76,z6]),(0,[z0,z219,z1,z9,z3,z4,z6]),(0,[z0,z1,z220,z9,z3,z4,z6])],[(0,[z24,z0,z16,z9,z3,z4,z6]),(0,[z0,z20,z1,z117,z3,z4,z6]),(0,[z108,z0,z1,z9,z3,z12,z6])],[(0,[z0,z221,z1,z9,z3,z4,z6]),(0,[z222,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z223,z6]),(0,[z0,z1,z9,z82,z4,z72,z6]),(0,[z0,z1,z224,z9,z3,z4,z6])],[(0,[z225,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z220,z3,z114,z4,z6])],[(0,[z0,z1,z3,z4,z17,z6,z55])],[(0,[z0,z1,z9,z3,z226,z4,z6]),(0,[z0,z1,z9,z3,z227,z4,z6]),(0,[z0,z1,z9,z3,z4,z228,z6])],[(0,[z229,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z17,z6]),(0,[z0,z1,z40,z69,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z230])],[(0,[z0,z1,z9,z3,z231,z4,z6]),(0,[z0,z1,z207,z51,z3,z4,z6]),(1,[z0,z34,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z232,z6]),(0,[z0,z1,z2,z3,z4,z131,z6])]],
   [[(0,[z0,z1,z9,z233,z3,z4,z6]),(1,[z0,z1,z44,z3,z4,z6]),(0,[z59,z0,z1,z193,z3,z4,z6]),(0,[z0,z1,z9,z234,z3,z4,z6]),(1,[z0,z126,z1,z3,z4,z6])],[(1,[z0,z1,z104,z3,z4,z6])],[(0,[z30,z0,z1,z51,z3,z4,z6]),(0,[z0,z75,z1,z9,z3,z4,z191]),(0,[z0,z1,z9,z3,z4,z235,z6])],[(0,[z0,z1,z51,z3,z4,z6,z22]),(0,[z119,z1,z9,z3,z4,z41,z6]),(0,[z0,z1,z9,z3,z236,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z237]),(0,[z0,z1,z9,z3,z4,z238,z6])],[(1,[z0,z1,z9,z3,z4,z239]),(0,[z0,z1,z9,z3,z4,z49,z6]),(0,[z0,z20,z1,z74,z3,z4,z6])],[(0,[z152,z0,z1,z9,z201,z4,z6]),(0,[z108,z0,z9,z3,z4,z137,z6])],[(0,[z0,z1,z9,z3,z4,z240,z6]),(0,[z0,z1,z9,z3,z241,z12,z4]),(0,[z242,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z2,z9,z3,z17,z6]),(0,[z0,z1,z9,z3,z4,z243,z6])],[(0,[z0,z1,z9,z3,z4,z6,z244]),(0,[z0,z73,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z245,z6])],[(0,[z152,z0,z246,z9,z3,z4,z6]),(0,[z247,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z248,z6])],[(1,[z0,z249,z1,z3,z4,z6]),(0,[z0,z1,z181,z9,z3,z4,z6])],[(0,[z0,z1,z250,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z251,z6]),(0,[z0,z1,z9,z3,z4,z252,z6])],[(0,[z253,z0,z1,z9,z3,z4,z6]),(0,[z62,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z254,z9,z3,z4,z6]),(0,[z33,z0,z1,z255,z3,z4,z6]),(0,[z0,z256,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z6,z37]),(0,[z257,z0,z1,z3,z4,z17,z6])],[(0,[z98,z0,z1,z9,z3,z4,z6]),(0,[z98,z0,z106,z9,z3,z4,z6]),(0,[z0,z1,z9,z258,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z137,z6])],[(0,[z19,z0,z1,z9,z3,z4,z191])],[(0,[z33,z0,z1,z9,z120,z4,z6]),(0,[z0,z1,z9,z259,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z131,z6])]],
   [[(0,[z260,z0,z1,z9,z3,z4,z6]),(0,[z134,z0,z1,z2,z3,z4,z6])],[(0,[z0,z16,z1,z51,z3,z4,z6]),(0,[z0,z1,z51,z3,z120,z4,z6]),(0,[z0,z261,z1,z51,z3,z4,z6]),(0,[z262,z0,z1,z9,z3,z4,z6]),(0,[z36,z0,z1,z9,z3,z4,z39])],[(0,[z98,z0,z1,z2,z3,z4,z6]),(0,[z0,z263,z1,z9,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z41,z6]),(0,[z0,z42,z1,z3,z236,z4,z6]),(0,[z0,z1,z264,z9,z3,z4,z6]),(1,[z265,z0,z1,z9,z4,z55])],[(0,[z0,z1,z9,z3,z4,z266,z6]),(0,[z0,z73,z1,z9,z147,z4,z6]),(1,[z0,z1,z3,z4,z267,z6])],[(0,[z268,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z269,z3,z4,z6]),(0,[z0,z70,z20,z1,z3,z4,z6]),(0,[z270,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z271,z9,z3,z4,z6]),(0,[z0,z1,z272,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z273,z6]),(1,[z0,z1,z65,z94,z4,z6])],[(0,[z0,z274,z1,z9,z3,z4,z6]),(1,[z0,z1,z102,z3,z4,z6])],[(0,[z59,z0,z1,z51,z3,z4,z6]),(0,[z0,z75,z9,z3,z10,z4,z6])],[(0,[z0,z1,z9,z3,z5,z131,z6]),(0,[z275,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z276]),(0,[z0,z277,z1,z9,z3,z4,z6]),(0,[z0,z1,z264,z2,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z251,z6]),(0,[z0,z1,z9,z3,z4,z6,z278])],[(0,[z0,z42,z1,z3,z190,z4,z6]),(0,[z0,z279,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z280,z22]),(1,[z0,z81,z1,z3,z4,z6])],[(0,[z281,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z51,z3,z10,z4,z6]),(0,[z282,z0,z1,z9,z3,z4,z6]),(0,[z1,z9,z3,z120,z4,z6,z159])],[(1,[z27,z0,z1,z3,z4,z6]),(1,[z33,z1,z9,z120,z4,z6]),(1,[z0,z20,z1,z3,z4,z6]),(0,[z283,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z17,z6])],[(0,[z0,z1,z9,z3,z284,z4,z6]),(0,[z119,z0,z1,z9,z3,z4,z41]),(0,[z0,z20,z1,z3,z53,z4,z6]),(0,[z0,z1,z9,z285,z3,z4,z6]),(0,[z0,z1,z65,z9,z56,z4,z6])],[],[(0,[z0,z286,z1,z9,z3,z4,z6]),(0,[z36,z0,z42,z1,z3,z4,z6])]],
   [[(0,[z59,z0,z1,z9,z3,z4,z159]),(0,[z0,z42,z9,z7,z3,z4,z6]),(0,[z19,z0,z75,z9,z3,z4,z6]),(0,[z0,z1,z132,z9,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z159]),(0,[z0,z287,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z191])],[(0,[z288,z0,z1,z9,z3,z4,z6])],[(0,[z0,z289,z1,z9,z3,z4,z6])],[(0,[z0,z9,z3,z4,z76,z6,z22])],[],[(1,[z98,z16,z9,z3,z4,z6]),(0,[z0,z1,z290,z9,z3,z4,z6]),(0,[z170,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z118,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z291]),(0,[z0,z1,z9,z3,z4,z292,z6])],[(0,[z0,z1,z293,z9,z3,z4,z6])],[(0,[z0,z1,z146,z9,z3,z4,z6]),(0,[z0,z1,z94,z3,z4,z39,z6])],[(0,[z0,z1,z294,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z295,z6]),(0,[z0,z42,z75,z1,z3,z4,z6])],[(0,[z0,z1,z51,z51,z3,z4,z6]),(0,[z296,z0,z1,z9,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z124,z4,z6]),(0,[z0,z1,z297,z9,z3,z4,z6])],[(0,[z119,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z9,z3,z298,z4,z6]),(0,[z152,z0,z1,z2,z3,z4,z6]),(1,[z0,z299,z9,z3,z4,z6]),(1,[z0,z1,z9,z3,z300,z6])],[(0,[z0,z1,z206,z9,z3,z4,z6]),(0,[z0,z1,z40,z122,z3,z4,z6]),(0,[z19,z0,z60,z9,z3,z4,z6]),(0,[z0,z1,z9,z301,z3,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z265,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z40,z302,z3,z4,z6]),(0,[z0,z66,z1,z40,z3,z4,z6]),(0,[z0,z20,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z12,z4,z123]),(0,[z0,z1,z9,z303,z3,z4,z6]),(0,[z0,z1,z69,z9,z3,z4,z37]),(0,[z0,z1,z9,z3,z304,z4,z6])],[(0,[z0,z1,z9,z3,z305,z4,z6]),(0,[z0,z75,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z306,z4,z6])]],
   [[(0,[z0,z1,z51,z3,z4,z6,z37]),(0,[z0,z42,z1,z3,z4,z6,z191]),(0,[z19,z0,z42,z9,z3,z4,z6]),(0,[z307,z0,z1,z9,z3,z4,z6]),(1,[z0,z1,z9,z3,z105,z6])],[(0,[z308,z0,z1,z9,z3,z4,z6]),(0,[z309,z0,z1,z9,z3,z4,z6]),(0,[z108,z0,z1,z40,z3,z4,z6]),(0,[z0,z20,z1,z3,z114,z4,z6])],[(0,[z101,z0,z20,z1,z3,z4,z6])],[(0,[z119,z0,z42,z1,z3,z4,z6]),(1,[z310,z0,z1,z3,z4,z6]),(0,[z265,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z311,z9,z3,z4,z6]),(0,[z0,z1,z312,z9,z3,z4,z6]),(0,[z188,z0,z1,z9,z3,z4,z6])],[(0,[z0,z20,z1,z2,z3,z4,z6])],[(0,[z0,z20,z1,z3,z61,z4,z6]),(1,[z19,z0,z9,z3,z4,z22]),(0,[z313,z0,z1,z9,z3,z4,z6])],[(0,[z314,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z211,z4,z6]),(0,[z0,z1,z9,z109,z3,z4,z6])],[(0,[z0,z315,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z316,z4,z6]),(0,[z0,z1,z9,z3,z317,z4,z6]),(0,[z0,z42,z60,z1,z3,z4,z6])],[(0,[z97,z0,z1,z40,z3,z4,z6]),(0,[z0,z20,z1,z94,z3,z4,z6]),(0,[z0,z1,z69,z9,z3,z4,z6]),(1,[z0,z1,z318,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z319]),(1,[z0,z1,z208,z3,z4,z6]),(0,[z0,z9,z3,z12,z4,z137,z6]),(0,[z0,z1,z2,z3,z114,z4,z6])],[(0,[z0,z20,z1,z3,z4,z131,z6])],[(0,[z19,z0,z16,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z185,z4,z6]),(1,[z0,z1,z3,z4,z6,z320]),(0,[z0,z1,z9,z3,z4,z6,z321])],[(0,[z24,z0,z1,z9,z3,z4,z6]),(0,[z24,z0,z106,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z322]),(0,[z0,z1,z3,z18,z4,z17,z6]),(0,[z0,z249,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z323,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z238,z6])],[(0,[z45,z0,z1,z9,z3,z61,z6]),(0,[z0,z1,z2,z3,z61,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z324])],[(0,[z0,z70,z1,z51,z3,z4,z6]),(0,[z97,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z248,z137,z6])]],
   [[(0,[z325,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z40,z3,z326,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z6])],[(0,[z0,z1,z9,z3,z327,z4,z6]),(0,[z0,z328,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z84,z4,z159])],[(0,[z0,z1,z9,z3,z52,z4,z6]),(0,[z329,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z330,z6])],[(0,[z0,z42,z16,z1,z3,z4,z6]),(0,[z0,z16,z9,z3,z4,z76,z6])],[(0,[z0,z1,z40,z3,z12,z4,z6]),(1,[z0,z331,z9,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z84,z4])],[(1,[z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z5,z6]),(0,[z0,z1,z40,z7,z3,z4,z6]),(0,[z0,z1,z9,z3,z332,z4,z6]),(0,[z0,z20,z1,z147,z3,z4,z6])],[(0,[z0,z1,z40,z3,z18,z4,z6]),(0,[z333,z0,z1,z9,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z137,z6])],[(0,[z334,z0,z1,z9,z3,z4,z6]),(0,[z119,z57,z1,z9,z3,z4,z6])],[(0,[z335,z0,z1,z9,z3,z4,z6]),(0,[z30,z0,z1,z336,z3,z4,z6])],[(0,[z0,z1,z9,z3,z337,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z338])],[(0,[z0,z1,z9,z3,z4,z339,z6]),(0,[z0,z1,z9,z3,z340,z4,z6]),(0,[z0,z1,z9,z3,z4,z341,z6])],[(0,[z0,z1,z9,z3,z4,z342,z6]),(1,[z36,z0,z1,z3,z4,z37])],[(0,[z0,z1,z343,z9,z3,z4,z6]),(0,[z344,z0,z1,z9,z3,z4,z6]),(0,[z19,z0,z9,z3,z4,z6,z22]),(0,[z0,z1,z9,z3,z190,z4,z6])],[(1,[z0,z315,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z345,z6]),(0,[z0,z1,z2,z147,z3,z4,z6]),(0,[z0,z60,z1,z9,z3,z12,z6]),(0,[z265,z0,z1,z9,z82,z4,z6])]],
   [[(0,[z0,z1,z40,z3,z4,z6,z55]),(0,[z0,z1,z9,z3,z346,z4,z6]),(0,[z0,z1,z9,z347,z3,z4,z6]),(0,[z0,z1,z9,z348,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z131,z6])],[(0,[z0,z1,z51,z3,z84,z4,z6]),(1,[z0,z79,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z349,z4,z6])],[(0,[z0,z1,z51,z3,z4,z100,z6]),(0,[z33,z0,z1,z9,z3,z350,z6]),(0,[z0,z351,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z352,z4,z6])],[(1,[z0,z1,z83,z3,z4,z6]),(0,[z0,z42,z1,z3,z56,z4,z6]),(0,[z353,z0,z1,z9,z3,z4,z6]),(1,[z108,z0,z9,z3,z137,z6])],[(0,[z0,z1,z40,z3,z4,z39,z6])],[(0,[z0,z1,z51,z3,z4,z41,z6]),(0,[z354,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z355,z6]),(0,[z119,z0,z146,z9,z3,z4,z6]),(0,[z0,z356,z1,z9,z3,z4,z6])],[(0,[z357,z0,z1,z9,z3,z4,z6]),(0,[z358,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z359,z3,z4,z6]),(0,[z0,z1,z9,z360,z3,z4,z6]),(0,[z30,z0,z1,z9,z3,z190,z6]),(0,[z0,z1,z9,z3,z361,z4,z6])],[(1,[z97,z1,z40,z3,z4,z6]),(1,[z0,z42,z7,z3,z4,z6])],[(0,[z0,z1,z34,z9,z3,z4,z6]),(0,[z0,z362,z20,z1,z3,z4,z6]),(0,[z134,z0,z1,z9,z94,z4,z6]),(0,[z363,z0,z1,z9,z3,z4,z6]),(0,[z364,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z365,z6])],[(0,[z0,z16,z73,z9,z3,z4,z6]),(0,[z36,z0,z1,z40,z3,z4,z6]),(0,[z33,z0,z1,z9,z3,z4,z6]),(0,[z366,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z367,z4,z6]),(0,[z0,z20,z1,z3,z4,z6,z159]),(0,[z0,z1,z3,z4,z137,z17,z6]),(0,[z0,z1,z9,z368,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z369,z6]),(0,[z101,z0,z331,z9,z3,z4,z6])],[(1,[z0,z261,z1,z3,z4,z6]),(0,[z101,z0,z1,z51,z3,z4,z6]),(0,[z119,z0,z1,z3,z4,z17,z6]),(1,[z0,z221,z1,z3,z4,z6]),(0,[z0,z370,z1,z9,z3,z4,z6])],[(0,[z0,z1,z106,z51,z3,z4,z6]),(0,[z57,z0,z42,z1,z3,z4,z6]),(1,[z0,z9,z3,z371,z4,z6])],[(0,[z119,z0,z20,z1,z3,z4,z6]),(0,[z0,z372,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z373]),(0,[z0,z1,z9,z3,z4,z374,z6])]],
   [[(1,[z0,z1,z25,z3,z4,z6]),(0,[z0,z1,z255,z9,z3,z4,z6]),(0,[z375,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z376,z4,z6]),(0,[z0,z1,z9,z3,z4,z72,z191])],[(0,[z0,z1,z9,z3,z241,z4,z6]),(0,[z0,z1,z9,z3,z4,z377,z6])],[(0,[z0,z20,z1,z3,z4,z194,z6]),(0,[z108,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z6,z378])],[(0,[z0,z42,z73,z1,z3,z4,z6]),(0,[z265,z0,z1,z9,z4,z6,z55])],[(0,[z98,z16,z1,z9,z3,z4,z6]),(0,[z379,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z380,z4,z6]),(0,[z108,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z381,z6]),(0,[z0,z1,z9,z82,z3,z4,z6])],[(0,[z382,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z40,z117,z3,z4,z6]),(0,[z0,z383,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z384,z4,z6]),(1,[z0,z1,z9,z117,z190,z6])],[(1,[z0,z1,z255,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z385])],[(0,[z0,z1,z2,z303,z3,z4,z6])],[(0,[z0,z16,z9,z3,z10,z4,z6]),(0,[z0,z1,z9,z3,z386,z4,z6])],[(0,[z97,z0,z1,z3,z4,z17,z6])],[(0,[z387,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z13,z6]),(0,[z388,z0,z1,z9,z3,z4,z6])],[(0,[z0,z0,z1,z9,z3,z4,z6]),(0,[z0,z389,z1,z9,z3,z4,z6]),(0,[z152,z0,z1,z9,z3,z4,z390]),(0,[z0,z1,z9,z58,z3,z4,z6]),(0,[z288,z0,z1,z2,z3,z4,z6])],[(0,[z0,z391,z1,z106,z3,z4,z6])],[(0,[z96,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z392,z6])],[(1,[z0,z1,z3,z4,z100,z6]),(0,[z0,z1,z9,z3,z393,z4,z6])],[]],
   [[(0,[z98,z0,z1,z9,z3,z4,z394]),(0,[z0,z395,z1,z9,z3,z4,z6])],[(0,[z310,z0,z1,z9,z3,z4,z6])],[(0,[z0,z16,z60,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z396,z6])],[(0,[z0,z1,z9,z3,z4,z397,z6]),(0,[z0,z42,z1,z82,z3,z4,z6])],[(0,[z398,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z6,z159])],[(0,[z399,z0,z1,z9,z3,z4,z6]),(0,[z400,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z371,z4,z6])],[(1,[z1,z40,z51,z3,z4,z6]),(0,[z0,z42,z1,z40,z3,z4,z6])],[(0,[z0,z73,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z401]),(0,[z310,z0,z1,z2,z3,z4,z6]),(0,[z265,z0,z402,z9,z3,z4,z6])],[(0,[z0,z75,z1,z2,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z403]),(0,[z0,z1,z9,z3,z404,z4,z6]),(0,[z0,z1,z9,z3,z405,z4,z6]),(0,[z265,z406,z1,z9,z3,z4,z6])],[(0,[z407,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z120,z4,z131,z6]),(0,[z408,z0,z1,z9,z3,z4,z6])],[(0,[z134,z0,z42,z1,z3,z4,z6]),(0,[z409,z0,z1,z9,z3,z4,z6]),(0,[z0,z21,z1,z9,z3,z4,z6]),(0,[z410,z0,z1,z9,z3,z4,z6]),(0,[z36,z0,z1,z3,z4,z6,z37])],[(0,[z0,z1,z9,z3,z411,z4,z6]),(0,[z0,z1,z9,z3,z4,z350,z6]),(0,[z1,z9,z122,z3,z120,z4,z6]),(0,[z0,z1,z311,z2,z3,z4,z6])],[(0,[z0,z42,z42,z1,z3,z4,z6]),(0,[z30,z0,z1,z9,z117,z4,z6])],[(0,[z19,z0,z106,z9,z3,z4,z6]),(0,[z0,z1,z412,z40,z3,z4,z6]),(0,[z0,z1,z91,z9,z3,z4,z6]),(0,[z19,z0,z1,z9,z3,z4,z6]),(0,[z0,z75,z1,z9,z3,z4,z22])],[(0,[z0,z1,z413,z51,z3,z4,z6]),(0,[z414,z0,z1,z9,z3,z4,z6])]],
   [[(0,[z152,z0,z1,z269,z3,z4,z6])],[(0,[z0,z1,z9,z415,z3,z4,z6]),(0,[z0,z1,z9,z190,z4,z131,z6])],[],[(0,[z0,z1,z9,z3,z4,z6,z99]),(0,[z0,z20,z1,z259,z3,z4,z6]),(0,[z0,z1,z9,z3,z416,z4,z6])],[(0,[z45,z0,z1,z9,z3,z4,z6]),(0,[z265,z417,z1,z9,z3,z4,z6])],[(0,[z24,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z4,z6]),(0,[z0,z1,z9,z418,z3,z4,z6])],[],[(0,[z0,z60,z1,z40,z3,z4,z6]),(0,[z0,z1,z9,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z190,z4,z6])],[(0,[z0,z1,z74,z40,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z6,z403]),(0,[z0,z1,z117,z3,z4,z17,z6])],[(0,[z0,z1,z51,z3,z12,z4,z6]),(0,[z0,z1,z122,z3,z4,z17,z6]),(0,[z59,z1,z9,z3,z4,z6,z159]),(1,[z0,z42,z73,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z228,z6]),(0,[z0,z1,z2,z347,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z5,z6]),(0,[z119,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z419,z4,z6])],[(0,[z420,z0,z1,z9,z3,z4,z6]),(0,[z421,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z422,z3,z4,z6])],[(0,[z0,z423,z1,z9,z3,z4,z6]),(0,[z36,z0,z1,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z4,z424,z6])],[(0,[z0,z1,z9,z3,z4,z425,z6]),(0,[z36,z0,z20,z1,z3,z4,z6]),(0,[z426,z0,z1,z9,z3,z4,z6])],[(0,[z427,z0,z1,z9,z3,z4,z6]),(1,[z0,z391,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z428]),(0,[z108,z0,z1,z51,z3,z4,z6]),(0,[z0,z20,z75,z1,z3,z4,z6]),(1,[z0,z1,z336,z3,z4,z6])]],
   [[(0,[z0,z1,z9,z3,z429,z4,z6]),(0,[z108,z0,z1,z9,z3,z137,z6])],[(0,[z0,z1,z9,z3,z4,z6,z6]),(0,[z170,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z430,z9,z3,z4,z6])],[(0,[z176,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z76,z6]),(0,[z0,z1,z431,z9,z3,z4,z6])],[(0,[z119,z0,z1,z9,z3,z4,z159])],[(0,[z0,z1,z9,z432,z3,z4,z6]),(0,[z134,z0,z1,z65,z3,z4,z6]),(0,[z134,z0,z1,z3,z56,z4,z6])],[(0,[z0,z1,z3,z433,z4,z17,z6])],[(0,[z0,z1,z9,z3,z4,z434,z6]),(0,[z0,z1,z9,z435,z3,z4,z6]),(0,[z8,z0,z42,z1,z3,z4,z6]),(0,[z0,z42,z1,z65,z3,z4,z6]),(0,[z0,z1,z9,z3,z436,z4,z6]),(0,[z265,z0,z1,z312,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z39,z6]),(0,[z152,z0,z42,z1,z3,z4,z6]),(0,[z437,z0,z1,z9,z3,z4,z6]),(0,[z45,z0,z1,z9,z3,z17,z6]),(1,[z0,z9,z3,z4,z6,z438])],[(0,[z0,z1,z9,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z439,z4,z6]),(0,[z0,z1,z9,z117,z190,z4,z6])],[(0,[z0,z1,z40,z9,z3,z4,z6]),(0,[z57,z0,z1,z40,z3,z4,z6]),(0,[z30,z0,z1,z9,z3,z4,z440])],[(0,[z0,z441,z1,z9,z3,z4,z6]),(0,[z0,z1,z442,z9,z3,z4,z6])],[(0,[z443,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z444,z9,z3,z4,z6]),(0,[z0,z1,z40,z3,z114,z4,z6]),(0,[z0,z1,z9,z3,z445,z4,z6]),(0,[z0,z1,z2,z82,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z191]),(0,[z0,z1,z3,z190,z4,z112,z6])],[(0,[z57,z288,z1,z9,z3,z4,z6]),(0,[z417,z0,z1,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z438,z55])],[(0,[z446,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z162,z4,z6]),(0,[z357,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z4,z191])]],
   [[(0,[z33,z0,z1,z9,z122,z4,z6]),(0,[z265,z19,z0,z1,z9,z3,z4]),(0,[z0,z1,z331,z9,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z76,z6]),(0,[z108,z0,z1,z102,z3,z4,z6]),(1,[z0,z1,z447,z3,z4,z6])],[(0,[z0,z1,z9,z448,z3,z4,z6]),(0,[z0,z202,z60,z1,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z449,z6]),(0,[z0,z1,z9,z3,z4,z450,z6]),(0,[z0,z1,z9,z451,z3,z4,z6])],[(0,[z33,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z3,z10,z4,z6,z22]),(0,[z0,z402,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z174])],[(0,[z288,z1,z9,z3,z120,z4,z6]),(1,[z0,z1,z153,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z452,z6]),(0,[z453,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z40,z3,z4,z131,z6]),(0,[z57,z1,z9,z3,z4,z5,z6]),(0,[z454,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z455,z3,z4,z6]),(0,[z0,z1,z44,z3,z4,z5,z6]),(0,[z0,z42,z1,z3,z4,z17,z6])],[(1,[z0,z1,z9,z3,z4,z99]),(0,[z456,z0,z1,z9,z3,z4,z6]),(0,[z1,z9,z3,z18,z4,z5,z6]),(1,[z188,z0,z1,z3,z4,z6])],[(0,[z0,z1,z9,z3,z18,z131,z6]),(0,[z0,z1,z9,z3,z4,z191,z55])],[(0,[z0,z1,z9,z457,z3,z4,z6])],[(0,[z0,z1,z9,z3,z120,z4,z6]),(0,[z0,z1,z9,z458,z3,z4,z6]),(0,[z0,z1,z9,z3,z459,z4,z6]),(0,[z460,z0,z1,z9,z3,z4,z6])],[],[(0,[z0,z1,z9,z150,z3,z4,z6]),(0,[z461,z0,z20,z1,z3,z4,z6]),(1,[z0,z20,z74,z3,z4,z6]),(0,[z0,z1,z9,z462,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z6,z191]),(0,[z379,z0,z1,z2,z3,z4,z6])],[(0,[z97,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z9,z193,z3,z4,z6]),(0,[z0,z1,z463,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z438])],[]],
   [[],[(0,[z0,z1,z207,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z464,z6]),(0,[z0,z465,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z466,z3,z4,z6]),(0,[z0,z1,z9,z3,z467,z4,z6])],[(0,[z119,z0,z299,z9,z3,z4,z6]),(1,[z468,z0,z1,z9,z3,z4]),(0,[z469,z0,z1,z9,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z190,z6])],[(0,[z0,z1,z51,z122,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z161,z6]),(0,[z0,z1,z40,z147,z3,z4,z6]),(0,[z0,z470,z1,z9,z3,z4,z6])],[(0,[z0,z1,z51,z471,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z137,z6]),(0,[z30,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z10,z4,z6])],[(0,[z0,z1,z9,z3,z165,z4,z6]),(0,[z0,z20,z74,z9,z3,z4,z6]),(1,[z0,z1,z220,z3,z4,z6])],[(0,[z134,z0,z1,z40,z3,z4,z6]),(0,[z0,z406,z1,z9,z3,z4,z6])],[(0,[z0,z472,z1,z9,z3,z4,z6]),(0,[z0,z68,z1,z9,z3,z4,z6]),(0,[z0,z60,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z473,z3,z4,z6])],[(0,[z98,z0,z1,z40,z3,z4,z6]),(0,[z36,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z74,z3,z4,z17,z6])],[(0,[z0,z42,z1,z3,z120,z4,z6]),(0,[z0,z1,z9,z3,z4,z474,z6]),(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z440]),(0,[z475,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z476,z4,z6])],[(0,[z247,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z477,z6]),(0,[z0,z1,z9,z163,z3,z4,z6]),(0,[z172,z0,z1,z3,z4,z17,z6])],[(0,[z62,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z478])],[(0,[z0,z1,z2,z3,z4,z4,z6])],[(0,[z0,z1,z297,z3,z190,z4,z6])]],
   [[(0,[z98,z0,z42,z1,z3,z4,z6]),(0,[z479,z0,z1,z9,z3,z4,z6]),(0,[z8,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z2,z3,z56,z4,z6]),(0,[z0,z1,z2,z65,z3,z4,z6]),(0,[z0,z1,z9,z3,z433,z4,z6])],[(0,[z268,z0,z1,z40,z3,z4,z6]),(0,[z0,z480,z1,z9,z3,z4,z6]),(0,[z0,z1,z481,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z41,z191]),(0,[z0,z20,z1,z3,z190,z4,z6]),(0,[z0,z1,z69,z3,z56,z4,z6]),(0,[z0,z1,z9,z104,z3,z4,z6])],[(0,[z0,z16,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z482,z6]),(0,[z0,z261,z1,z9,z3,z4,z6]),(0,[z483,z0,z1,z9,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z345,z6]),(0,[z0,z484,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z485,z4,z6]),(0,[z0,z42,z1,z3,z10,z4,z6]),(0,[z486,z0,z1,z9,z3,z4,z6])],[(0,[z152,z0,z1,z9,z3,z5,z6])],[(0,[z0,z127,z1,z106,z3,z4,z6]),(0,[z487,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z117,z3,z131,z6])],[(0,[z488,z0,z1,z9,z3,z4,z6]),(0,[z19,z0,z1,z2,z3,z4,z6])],[(0,[z489,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z6,z159]),(0,[z0,z20,z73,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z490,z4,z6]),(0,[z0,z491,z1,z9,z3,z4,z6]),(0,[z492,z0,z1,z9,z3,z4,z6]),(0,[z414,z0,z1,z2,z3,z4,z6]),(1,[z30,z0,z1,z9,z131,z6])],[(0,[z59,z0,z1,z9,z3,z4,z6]),(0,[z493,z0,z1,z9,z3,z4,z6]),(0,[z265,z0,z1,z9,z3,z4,z55]),(0,[z494,z0,z1,z9,z3,z4,z6])],[(0,[z495,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z37]),(0,[z265,z0,z1,z9,z3,z4,z72]),(0,[z0,z1,z9,z3,z84,z6,z191])],[(0,[z0,z42,z1,z106,z3,z4,z6]),(0,[z57,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z496,z6]),(0,[z0,z42,z1,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z76,z6]),(0,[z0,z1,z9,z3,z497,z4,z6])],[(0,[z8,z0,z1,z9,z147,z4,z6]),(0,[z0,z277,z9,z94,z3,z4,z6]),(0,[z0,z43,z1,z9,z3,z4,z6])],[(0,[z0,z1,z51,z7,z3,z4,z6]),(0,[z170,z0,z1,z40,z3,z4,z6]),(0,[z57,z0,z20,z1,z3,z4,z6]),(0,[z19,z0,z1,z9,z3,z4,z22]),(0,[z45,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z51,z3,z18,z4,z6]),(0,[z498,z0,z1,z9,z3,z4,z6])],[(0,[z57,z1,z9,z122,z3,z4,z6]),(0,[z265,z0,z75,z1,z9,z3,z4]),(0,[z36,z0,z1,z69,z3,z4,z6]),(0,[z499,z0,z1,z9,z3,z4,z6])]],
   [[(0,[z0,z1,z9,z3,z4,z500,z6]),(0,[z0,z1,z65,z9,z3,z4,z6]),(0,[z0,z1,z9,z501,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z72,z6])],[(0,[z502,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z17,z6])],[(0,[z8,z0,z1,z40,z3,z4,z6])],[(0,[z503,z0,z1,z9,z3,z4,z6]),(0,[z152,z0,z1,z40,z3,z4,z6]),(0,[z288,z0,z1,z58,z3,z4,z6]),(0,[z0,z504,z1,z9,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z84,z6])],[(0,[z0,z42,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z267,z6])],[(0,[z98,z24,z1,z9,z3,z4,z6]),(1,[z0,z1,z3,z4,z144,z6])],[(0,[z0,z1,z51,z3,z4,z6,z55]),(0,[z288,z0,z42,z1,z3,z4,z6])],[(0,[z152,z288,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z505])],[(0,[z296,z0,z1,z40,z3,z4,z6]),(1,[z0,z1,z9,z201,z4,z6]),(0,[z0,z20,z1,z82,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z6,z191]),(0,[z506,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z507])],[(0,[z97,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z508,z6]),(0,[z0,z42,z1,z3,z4,z6,z37]),(0,[z509,z0,z1,z9,z3,z4,z6]),(0,[z0,z510,z1,z9,z3,z4,z6]),(0,[z0,z1,z511,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z512])],[(0,[z265,z0,z1,z40,z3,z4,z6]),(0,[z0,z513,z1,z9,z3,z4,z6]),(0,[z0,z1,z65,z94,z3,z4,z6])],[(0,[z0,z20,z1,z40,z3,z4,z6]),(1,[z0,z246,z9,z3,z4,z6]),(0,[z514,z0,z1,z9,z3,z4,z6]),(0,[z515,z0,z1,z9,z3,z4,z6]),(0,[z516,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z517,z4,z6]),(0,[z0,z1,z9,z518,z3,z4,z6]),(0,[z30,z0,z1,z9,z3,z4,z245])],[(0,[z0,z1,z9,z3,z519,z4,z6]),(1,[z0,z1,z3,z4,z6,z280])],[(0,[z33,z1,z9,z3,z120,z4,z6]),(0,[z0,z1,z69,z9,z3,z4,z39]),(0,[z0,z520,z1,z9,z3,z4,z6])],[(0,[z152,z1,z9,z3,z4,z5,z6]),(0,[z0,z42,z1,z3,z4,z72,z6]),(0,[z0,z20,z60,z1,z3,z4,z6]),(0,[z0,z9,z94,z3,z371,z4,z6]),(1,[z0,z1,z9,z3,z4,z440])]],
   [[(1,[z0,z1,z15,z3,z4,z6]),(1,[z0,z1,z206,z3,z4,z6]),(0,[z0,z521,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z522,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z22])],[(0,[z0,z1,z9,z523,z3,z4,z6]),(0,[z265,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z181,z3,z4,z76,z6])],[(0,[z0,z1,z9,z3,z4,z6,z524]),(0,[z0,z1,z9,z3,z84,z114,z4])],[(0,[z0,z1,z40,z2,z3,z4,z6]),(0,[z525,z0,z1,z9,z3,z4,z6])],[(0,[z27,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z6,z526]),(0,[z0,z1,z40,z3,z61,z4,z6]),(0,[z0,z1,z2,z3,z120,z4,z6]),(0,[z0,z20,z68,z1,z3,z4,z6]),(0,[z0,z126,z1,z3,z4,z17,z6])],[(0,[z0,z60,z1,z51,z3,z4,z6]),(0,[z33,z0,z1,z9,z3,z4,z434])],[(0,[z0,z1,z9,z3,z527,z4,z6]),(0,[z0,z1,z74,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z528,z4,z6]),(0,[z0,z1,z7,z3,z4,z17,z6]),(0,[z0,z60,z1,z9,z3,z137,z6])],[(0,[z0,z1,z40,z94,z3,z4,z6]),(0,[z0,z73,z1,z9,z10,z4,z6]),(0,[z0,z1,z9,z3,z529,z4,z6])],[(0,[z134,z0,z1,z3,z4,z17,z6])],[(0,[z0,z1,z51,z3,z4,z131,z6])],[(0,[z98,z0,z1,z3,z4,z17,z6]),(0,[z57,z0,z1,z208,z3,z4,z6]),(0,[z0,z42,z1,z69,z3,z4,z6]),(0,[z134,z0,z20,z1,z3,z4,z6]),(0,[z530,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z531,z6]),(0,[z0,z1,z9,z3,z4,z6,z532])],[(0,[z0,z1,z51,z117,z3,z4,z6]),(0,[z0,z1,z9,z533,z3,z4,z6]),(0,[z0,z1,z9,z3,z84,z4,z6])],[(0,[z0,z42,z20,z1,z3,z4,z6])],[(0,[z534,z0,z1,z9,z3,z4,z6]),(0,[z0,z20,z16,z1,z3,z4,z6]),(0,[z0,z1,z535,z51,z3,z4,z6]),(1,[z0,z1,z64,z3,z4,z6]),(0,[z0,z1,z9,z3,z190,z5,z6]),(1,[z8,z0,z9,z10,z4,z6])],[(0,[z0,z1,z9,z3,z536,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z537]),(0,[z0,z1,z2,z3,z10,z4,z6]),(0,[z0,z1,z3,z84,z4,z17,z6]),(0,[z0,z1,z9,z538,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z539,z6]),(0,[z0,z1,z9,z3,z4,z41,z6]),(0,[z0,z42,z1,z3,z522,z4,z6]),(0,[z0,z42,z1,z3,z4,z6,z22]),(0,[z0,z1,z9,z3,z4,z6,z540])]],
   [[(0,[z24,z0,z42,z1,z3,z4,z6]),(1,[z0,z1,z9,z3,z350,z6]),(0,[z0,z1,z9,z541,z3,z4,z6]),(0,[z108,z0,z60,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z542])],[(0,[z0,z70,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z543,z3,z4,z6]),(0,[z270,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z246,z9,z3,z4,z6])],[(0,[z0,z299,z1,z9,z3,z4,z6])],[],[(0,[z1,z9,z3,z4,z41,z6,z159]),(0,[z0,z1,z9,z3,z4,z544,z6])],[(0,[z0,z1,z9,z3,z545,z4,z6])],[(0,[z546,z0,z1,z9,z3,z4,z6]),(1,[z0,z127,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z547]),(0,[z548,z0,z1,z9,z3,z4,z6]),(0,[z0,z549,z1,z9,z3,z4,z6])],[(0,[z57,z0,z1,z51,z3,z4,z6]),(0,[z33,z0,z1,z9,z3,z380,z6]),(0,[z0,z1,z9,z3,z4,z6,z550])],[(1,[z0,z1,z9,z3,z4,z6]),(0,[z0,z73,z9,z3,z4,z6,z22]),(0,[z0,z1,z9,z318,z3,z4,z6])],[(0,[z0,z1,z44,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z84,z4,z6]),(0,[z0,z1,z9,z3,z551,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z552]),(0,[z553,z0,z1,z9,z3,z4,z6]),(0,[z265,z0,z132,z9,z3,z4,z6])],[(0,[z0,z1,z343,z40,z3,z4,z6]),(0,[z0,z20,z1,z3,z56,z4,z6]),(0,[z0,z20,z1,z65,z3,z4,z6]),(1,[z0,z1,z2,z3,z61,z6]),(0,[z0,z175,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z320]),(1,[z0,z1,z3,z4,z112,z6]),(0,[z38,z0,z1,z9,z3,z4,z6])],[(0,[z554,z0,z1,z9,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z41,z6]),(0,[z0,z1,z9,z555,z3,z4,z6]),(0,[z170,z0,z1,z3,z4,z17,z6])],[(1,[z0,z1,z2,z3,z4,z6])]],
   [[(0,[z170,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z44,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z556,z6]),(0,[z0,z1,z9,z82,z3,z4,z55])],[(0,[z0,z1,z557,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z558,z6]),(0,[z0,z1,z9,z3,z4,z559,z6]),(0,[z0,z1,z9,z82,z3,z4,z72])],[(0,[z0,z1,z9,z3,z179,z4,z6]),(0,[z88,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z37])],[(0,[z152,z0,z1,z3,z4,z17,z6]),(0,[z288,z0,z1,z9,z3,z5,z6]),(0,[z0,z1,z9,z3,z560,z4,z6])],[(0,[z8,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z69,z65,z3,z4,z6])],[(0,[z62,z0,z1,z2,z3,z4,z6]),(0,[z152,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z561,z4,z6]),(0,[z0,z20,z1,z3,z4,z76,z6]),(0,[z19,z0,z74,z9,z3,z4,z6])],[(0,[z354,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z562,z6]),(0,[z563,z0,z1,z9,z3,z4,z6]),(1,[z0,z1,z138,z3,z4,z6])],[(0,[z0,z1,z9,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z564,z6]),(0,[z0,z565,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z566]),(0,[z0,z1,z567,z9,z3,z4,z6])],[(0,[z0,z1,z9,z568,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z72,z6]),(0,[z0,z569,z9,z3,z4,z6,z37]),(0,[z570,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z90,z9,z3,z4,z6])],[(0,[z0,z106,z9,z3,z4,z137,z6]),(0,[z282,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z9,z3,z18,z190,z6]),(0,[z0,z1,z9,z3,z4,z571,z6]),(0,[z265,z0,z1,z3,z4,z17,z6])],[(0,[z0,z16,z1,z2,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z572,z6])],[(0,[z0,z42,z1,z555,z3,z4,z6]),(1,[z0,z1,z9,z3,z114,z191])],[],[(0,[z33,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z573,z4,z6]),(0,[z0,z1,z9,z3,z574,z4,z6]),(0,[z101,z0,z1,z9,z3,z4,z6])]],
   [[(0,[z0,z1,z1,z9,z3,z4,z6]),(0,[z0,z1,z106,z9,z3,z4,z6]),(1,[z0,z1,z151,z3,z4,z6]),(0,[z0,z1,z212,z9,z3,z4,z6]),(0,[z0,z75,z1,z9,z3,z4,z41])],[(0,[z0,z1,z3,z4,z76,z6,z320])],[(0,[z97,z62,z1,z9,z3,z4,z6]),(0,[z288,z0,z1,z40,z3,z4,z6]),(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z8,z19,z0,z9,z3,z4,z6]),(0,[z0,z202,z1,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z4,z575,z6]),(0,[z0,z1,z9,z3,z4,z576,z6]),(0,[z577,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z578,z6])],[(0,[z0,z1,z9,z83,z3,z4,z6]),(0,[z0,z202,z20,z1,z3,z4,z6])],[(0,[z134,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z579,z6])],[(0,[z580,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z122,z117,z4,z6]),(0,[z0,z1,z69,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z581,z4,z6])],[(0,[z0,z31,z1,z9,z3,z4,z6])],[(0,[z0,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z582,z6])],[(0,[z0,z1,z9,z3,z4,z6,z390]),(0,[z583,z0,z1,z9,z3,z4,z6]),(0,[z0,z60,z9,z3,z4,z76,z6]),(0,[z0,z1,z2,z3,z4,z6,z22]),(0,[z0,z1,z9,z3,z300,z4,z6])],[],[],[],[(0,[z0,z1,z9,z584,z3,z4,z6]),(1,[z0,z60,z9,z3,z12,z6]),(0,[z0,z585,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z586,z6]),(0,[z0,z1,z9,z3,z4,z6,z587]),(0,[z101,z0,z1,z138,z3,z4,z6])],[(0,[z0,z42,z73,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z76,z6])],[(0,[z16,z1,z106,z9,z3,z4,z6]),(0,[z0,z75,z1,z40,z3,z4,z6]),(0,[z0,z20,z1,z3,z120,z4,z6]),(0,[z0,z1,z65,z9,z94,z4,z6]),(1,[z0,z277,z9,z3,z4,z6])]],
   [[(0,[z0,z1,z9,z3,z4,z394,z6])],[(0,[z0,z1,z9,z25,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z588,z6]),(0,[z589,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z191,z159]),(1,[z0,z1,z9,z3,z4,z245])],[(0,[z590,z0,z1,z9,z3,z4,z6]),(0,[z152,z0,z1,z9,z211,z4,z6]),(0,[z0,z74,z9,z3,z4,z76,z6]),(0,[z0,z565,z1,z3,z4,z137,z6]),(0,[z310,z0,z60,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z591])],[(0,[z0,z1,z51,z3,z114,z4,z6]),(0,[z288,z0,z1,z91,z3,z4,z6]),(0,[z0,z1,z9,z3,z12,z4,z6])],[(0,[z24,z1,z106,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z17,z6]),(0,[z0,z1,z2,z3,z84,z4,z6])],[(0,[z33,z57,z1,z9,z3,z4,z6]),(0,[z310,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z3,z114,z4,z17,z6])],[(0,[z0,z1,z9,z3,z592,z4,z6]),(0,[z593,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z51,z3,z61,z4,z6]),(0,[z594,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z117,z3,z190,z6])],[(0,[z0,z73,z106,z9,z3,z4,z6]),(1,[z0,z70,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z595,z6]),(0,[z0,z20,z1,z3,z10,z4,z6]),(0,[z0,z73,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z85])],[(0,[z0,z1,z51,z94,z3,z4,z6])],[(0,[z0,z1,z596,z9,z3,z4,z6]),(0,[z170,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z597,z4,z6]),(0,[z598,z0,z1,z9,z3,z4,z6])],[(0,[z599,z0,z1,z9,z3,z4,z6]),(0,[z24,z0,z1,z40,z3,z4,z6]),(0,[z600,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z601,z9,z3,z4,z6])],[(0,[z602,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z342,z6]),(0,[z0,z1,z9,z3,z4,z603,z6]),(0,[z0,z42,z221,z1,z3,z4,z6]),(0,[z0,z1,z3,z10,z4,z17,z6]),(0,[z0,z1,z3,z4,z140,z17,z6]),(0,[z257,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z40,z3,z190,z4,z6]),(0,[z0,z1,z3,z120,z4,z17,z6]),(0,[z0,z1,z604,z9,z3,z4,z6])],[(0,[z98,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z100,z6]),(0,[z0,z60,z73,z9,z3,z4,z6])]],
   [[(0,[z0,z20,z1,z106,z3,z4,z6]),(0,[z0,z1,z9,z605,z3,z4,z6]),(0,[z8,z0,z1,z51,z3,z4,z6]),(1,[z0,z1,z557,z3,z4,z6]),(0,[z0,z20,z1,z1,z3,z4,z6])],[(0,[z152,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z413,z9,z3,z4,z6]),(0,[z45,z0,z1,z40,z3,z4,z6]),(0,[z152,z0,z1,z9,z3,z4,z239]),(0,[z0,z1,z3,z4,z17,z452,z6]),(0,[z0,z1,z9,z3,z4,z39,z6])],[(0,[z0,z42,z1,z3,z12,z4,z6]),(0,[z19,z0,z42,z1,z3,z4,z6]),(0,[z606,z0,z1,z9,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z3,z4,z6,z607]),(0,[z0,z1,z3,z61,z4,z17,z6]),(0,[z0,z1,z9,z3,z608,z4,z6]),(1,[z101,z0,z1,z9,z3,z84])],[(0,[z0,z1,z9,z3,z4,z6,z609]),(0,[z0,z1,z9,z3,z610,z4,z6])],[(0,[z0,z1,z40,z3,z4,z355,z6]),(0,[z0,z1,z9,z3,z4,z611,z6])],[(1,[z288,z1,z9,z3,z18,z6]),(0,[z0,z362,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z612,z6]),(0,[z0,z1,z9,z613,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z614,z6])],[(0,[z0,z1,z40,z359,z3,z4,z6]),(0,[z0,z249,z1,z3,z10,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z615]),(0,[z45,z0,z42,z1,z3,z4,z6]),(0,[z616,z0,z1,z9,z3,z4,z6]),(1,[z0,z569,z9,z3,z4,z6]),(0,[z0,z1,z9,z4,z72,z6,z55])],[(0,[z0,z1,z51,z147,z3,z4,z6]),(0,[z0,z1,z9,z117,z120,z4,z6]),(0,[z152,z0,z315,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z196,z37])],[(0,[z0,z1,z51,z3,z4,z137,z6])],[(0,[z0,z9,z147,z3,z4,z76,z6]),(0,[z0,z75,z1,z9,z3,z4,z76])],[(0,[z0,z20,z1,z3,z490,z4,z6]),(0,[z0,z1,z617,z9,z3,z4,z6]),(0,[z0,z60,z9,z3,z10,z4,z6]),(1,[z134,z0,z1,z56,z4,z6]),(0,[z0,z1,z94,z3,z56,z4,z6])],[(0,[z0,z1,z447,z9,z3,z4,z6])],[(1,[z0,z1,z9,z3,z4,z390]),(0,[z0,z20,z1,z3,z4,z6,z37]),(0,[z618,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z619])],[(0,[z620,z0,z1,z9,z3,z4,z6]),(0,[z283,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z336,z9,z3,z4,z6])]],
   [[(0,[z0,z42,z1,z3,z4,z39,z6]),(0,[z621,z0,z1,z9,z3,z4,z6]),(0,[z30,z0,z1,z9,z4,z131,z6])],[(0,[z0,z1,z2,z51,z3,z4,z6]),(0,[z19,z0,z9,z147,z3,z4,z6]),(0,[z108,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z622,z9,z3,z4,z6])],[(0,[z19,z0,z9,z3,z4,z137,z6]),(0,[z623,z0,z1,z9,z3,z4,z6]),(1,[z0,z1,z86,z3,z4,z6])],[(0,[z0,z1,z69,z51,z3,z4,z6]),(0,[z288,z0,z1,z3,z4,z17,z6]),(1,[z0,z1,z3,z4,z49,z6]),(0,[z59,z0,z1,z557,z3,z4,z6]),(0,[z427,z0,z42,z1,z3,z4,z6]),(0,[z624,z0,z1,z9,z3,z4,z6]),(1,[z0,z402,z9,z3,z4,z6])],[(0,[z0,z1,z40,z82,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z6,z191]),(0,[z0,z1,z9,z3,z4,z6,z625]),(0,[z0,z42,z1,z3,z4,z611,z6]),(0,[z0,z20,z1,z3,z4,z72,z6])],[(0,[z24,z0,z1,z118,z3,z4,z6]),(0,[z288,z0,z20,z1,z3,z4,z6]),(0,[z0,z74,z9,z3,z10,z4,z6]),(0,[z626,z0,z1,z9,z3,z4,z6]),(1,[z406,z1,z9,z3,z4,z6])],[(0,[z627,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z628,z4,z6]),(0,[z0,z629,z1,z9,z3,z4,z6])],[(0,[z0,z1,z40,z40,z3,z4,z6]),(0,[z468,z0,z1,z9,z3,z4,z6]),(1,[z0,z1,z3,z4,z248,z6]),(0,[z0,z630,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z631])],[(0,[z0,z1,z9,z3,z632,z4,z6])],[(1,[z0,z1,z3,z4,z251,z6]),(0,[z0,z1,z3,z4,z374,z17,z6])],[(0,[z0,z1,z40,z3,z4,z6,z291])],[(0,[z33,z0,z1,z40,z3,z4,z6]),(0,[z0,z42,z9,z3,z4,z76,z6])],[(0,[z633,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z122,z3,z4,z6]),(0,[z0,z1,z634,z9,z3,z4,z6]),(0,[z0,z1,z94,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z114,z4,z191])],[(0,[z0,z1,z9,z471,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z6,z159]),(0,[z0,z1,z9,z302,z3,z4,z6]),(0,[z635,z0,z1,z9,z3,z4,z6])],[(0,[z0,z20,z1,z69,z3,z4,z6]),(0,[z0,z569,z1,z9,z3,z4,z6])]],
   [[(0,[z265,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z636,z9,z3,z4,z6]),(0,[z0,z75,z1,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z637,z4,z6]),(0,[z0,z1,z9,z3,z638,z4,z6]),(1,[z417,z1,z9,z3,z4,z6])],[(0,[z0,z20,z20,z1,z3,z4,z6]),(0,[z639,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z640,z6])],[(0,[z0,z1,z9,z3,z641,z4,z6])],[(1,[z0,z1,z9,z3,z380,z6]),(1,[z0,z1,z269,z3,z4,z6]),(1,[z0,z1,z135,z3,z4,z6])],[(0,[z0,z20,z1,z3,z4,z6,z22]),(0,[z0,z1,z9,z3,z642,z4,z6]),(0,[z643,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z644,z4,z6])],[(0,[z0,z1,z9,z3,z4,z645,z6]),(0,[z0,z1,z9,z3,z4,z6,z646]),(1,[z0,z1,z2,z3,z17,z6]),(0,[z30,z0,z77,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z647,z4,z6]),(0,[z0,z1,z9,z3,z648,z4,z6]),(0,[z0,z1,z3,z4,z17,z6,z37])],[(0,[z0,z1,z9,z649,z3,z4,z6]),(0,[z1,z40,z9,z51,z3,z4,z6]),(0,[z134,z0,z1,z9,z56,z4,z6]),(0,[z0,z1,z2,z69,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z650]),(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z86,z3,z4,z6])],[(0,[z0,z1,z106,z2,z3,z4,z6]),(0,[z0,z1,z254,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z651])],[(0,[z98,z0,z1,z51,z3,z4,z6]),(0,[z62,z1,z9,z51,z3,z4,z6]),(0,[z30,z103,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z652,z6])],[(0,[z653,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z654,z3,z4,z6])],[(0,[z0,z42,z1,z122,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z72,z6]),(0,[z38,z0,z9,z3,z4,z6,z55])],[(0,[z24,z0,z1,z3,z4,z17,z6]),(1,[z0,z1,z9,z3,z4,z394])],[(0,[z655,z0,z1,z9,z3,z4,z6]),(0,[z57,z0,z1,z9,z120,z4,z6]),(0,[z656,z0,z1,z9,z3,z4,z6]),(0,[z0,z9,z147,z3,z10,z4,z6]),(0,[z0,z1,z121,z9,z3,z4,z6]),(1,[z0,z21,z1,z3,z4,z6]),(1,[z45,z0,z1,z3,z17,z6])],[(0,[z24,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z657,z9,z3,z4,z6]),(0,[z19,z0,z1,z9,z3,z4,z41]),(0,[z0,z20,z1,z3,z84,z4,z6]),(0,[z658,z0,z1,z9,z3,z4,z6])]],
   [[(0,[z0,z1,z9,z3,z326,z4,z6]),(0,[z0,z1,z9,z3,z659,z4,z6]),(0,[z265,z0,z1,z9,z3,z300,z6])],[(0,[z0,z1,z9,z3,z660,z4,z6]),(0,[z30,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z3,z114,z4,z267,z6])],[(0,[z288,z1,z9,z3,z18,z4,z6]),(0,[z45,z0,z1,z3,z4,z17,z6]),(1,[z0,z1,z312,z3,z4,z6])],[(1,[z152,z1,z9,z3,z5,z6])],[(0,[z661,z0,z1,z9,z3,z4,z6]),(0,[z662,z0,z1,z9,z3,z4,z6]),(0,[z8,z0,z9,z3,z4,z76,z6]),(0,[z265,z0,z1,z9,z3,z105,z6])],[(0,[z0,z465,z42,z1,z3,z4,z6])],[(0,[z0,z663,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z664,z4,z6]),(0,[z0,z75,z1,z9,z3,z84,z4])],[(0,[z0,z1,z40,z3,z56,z4,z6]),(0,[z0,z1,z40,z65,z3,z4,z6]),(0,[z665,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z5,z6]),(0,[z0,z1,z9,z3,z4,z159,z55]),(0,[z0,z1,z9,z7,z3,z4,z6])],[(0,[z0,z1,z9,z3,z18,z4,z6]),(0,[z30,z0,z42,z1,z3,z4,z6]),(0,[z134,z36,z0,z1,z3,z4,z6])],[(0,[z0,z1,z666,z9,z3,z4,z6]),(1,[z0,z1,z297,z3,z4,z6])],[(0,[z0,z391,z1,z9,z3,z4,z6]),(0,[z57,z1,z9,z3,z4,z6,z159]),(0,[z0,z1,z9,z667,z3,z4,z6]),(0,[z0,z81,z1,z9,z3,z4,z6])],[(0,[z288,z0,z1,z9,z3,z18,z6]),(0,[z0,z1,z2,z3,z4,z41,z6]),(0,[z36,z0,z1,z9,z3,z4,z6])],[(0,[z0,z20,z1,z3,z4,z6,z550]),(0,[z0,z1,z3,z4,z17,z6,z22]),(0,[z0,z1,z668,z9,z3,z4,z6]),(0,[z265,z0,z1,z318,z3,z4,z6])],[(0,[z669,z0,z1,z9,z3,z4,z6]),(0,[z0,z670,z1,z9,z3,z4,z6])],[(0,[z19,z0,z1,z40,z3,z4,z6]),(0,[z0,z42,z9,z3,z10,z4,z6])],[(0,[z152,z0,z1,z9,z3,z18,z6]),(1,[z0,z1,z212,z3,z4,z6]),(0,[z0,z1,z3,z4,z39,z6,z37])]],
   [[(0,[z0,z16,z1,z40,z3,z4,z6]),(0,[z288,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z671,z6]),(1,[z0,z1,z9,z3,z241,z4]),(0,[z0,z1,z9,z3,z4,z6,z55])],[(0,[z62,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z51,z3,z190,z4,z6])],[(0,[z0,z1,z40,z3,z4,z76,z6]),(0,[z0,z73,z1,z2,z3,z4,z6])],[(0,[z0,z1,z9,z3,z672,z4,z6])],[(0,[z0,z1,z9,z3,z89,z4,z6])],[(1,[z0,z1,z109,z3,z4,z6]),(0,[z673,z0,z1,z9,z3,z4,z6]),(0,[z674,z0,z1,z9,z3,z4,z6])],[(0,[z0,z0,z1,z51,z3,z4,z6]),(0,[z0,z42,z1,z7,z3,z4,z6]),(0,[z353,z0,z20,z1,z3,z4,z6]),(1,[z0,z565,z1,z3,z4,z6])],[(0,[z675,z0,z1,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z18,z4,z6]),(0,[z0,z1,z121,z147,z3,z4,z6]),(0,[z676,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z677,z4,z6])],[(0,[z0,z1,z40,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z678,z4,z6]),(0,[z0,z1,z3,z190,z4,z17,z6])],[(0,[z0,z1,z9,z3,z679,z4,z6]),(0,[z680,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z442,z3,z4,z17,z6])],[(0,[z8,z0,z73,z9,z3,z4,z6]),(1,[z0,z1,z3,z185,z4,z6])],[(0,[z265,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z41,z6]),(0,[z0,z1,z9,z3,z681,z4,z6]),(1,[z0,z73,z9,z147,z4,z6]),(0,[z0,z682,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z683,z4,z6])],[(0,[z0,z20,z1,z51,z3,z4,z6]),(0,[z33,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z684,z9,z3,z4,z6]),(0,[z685,z0,z1,z9,z3,z4,z6])],[(0,[z0,z75,z1,z51,z3,z4,z6]),(0,[z59,z0,z42,z1,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z526]),(0,[z33,z0,z20,z1,z3,z4,z6]),(1,[z19,z0,z42,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z686,z6])],[(0,[z309,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z17,z6]),(0,[z119,z0,z1,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z6,z55]),(0,[z0,z1,z9,z3,z687,z4,z6])]],
   [[],[(0,[z0,z66,z1,z9,z3,z4,z6]),(0,[z0,z79,z1,z9,z3,z4,z6]),(0,[z134,z0,z1,z3,z4,z39,z6])],[(0,[z498,z0,z42,z1,z3,z4,z6])],[(0,[z0,z1,z688,z9,z3,z4,z6]),(1,[z0,z1,z9,z3,z4,z434]),(1,[z0,z42,z20,z3,z4,z6]),(1,[z0,z42,z3,z4,z76,z6])],[(0,[z689,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z690])],[(0,[z119,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z117,z3,z4,z6])],[(0,[z98,z0,z16,z9,z3,z4,z6]),(0,[z0,z1,z2,z122,z3,z4,z6]),(0,[z0,z75,z1,z9,z3,z4,z159]),(1,[z0,z202,z1,z3,z4,z6]),(0,[z0,z1,z9,z691,z3,z4,z6])],[(0,[z0,z16,z9,z3,z4,z137,z6]),(0,[z0,z1,z51,z82,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z6,z191]),(0,[z8,z0,z9,z3,z10,z4,z6]),(0,[z0,z1,z9,z3,z692,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z693]),(0,[z0,z383,z20,z1,z3,z4,z6])],[],[(0,[z461,z0,z1,z9,z3,z4,z6]),(0,[z24,z0,z1,z51,z3,z4,z6]),(0,[z694,z0,z1,z9,z3,z4,z6]),(0,[z108,z0,z1,z2,z3,z4,z6]),(0,[z19,z0,z1,z9,z3,z4,z76]),(0,[z0,z1,z622,z2,z3,z4,z6])],[(0,[z97,z0,z1,z9,z3,z4,z6]),(0,[z0,z1,z40,z3,z120,z4,z6]),(0,[z0,z1,z3,z12,z4,z17,z6]),(0,[z0,z1,z9,z3,z695,z4,z6]),(0,[z388,z0,z1,z3,z4,z17,z6])],[(1,[z0,z1,z3,z4,z342,z6])],[(0,[z468,z0,z1,z9,z3,z10,z4]),(0,[z0,z1,z9,z3,z130,z4,z6])],[(0,[z0,z1,z412,z9,z3,z4,z6]),(0,[z696,z0,z1,z9,z3,z4,z6]),(0,[z0,z513,z42,z1,z3,z4,z6]),(1,[z0,z1,z3,z4,z345,z6])],[(0,[z33,z0,z1,z9,z3,z4,z129])]],
   [[(0,[z0,z1,z9,z3,z697,z4,z6])],[(0,[z97,z0,z1,z2,z3,z4,z6]),(0,[z27,z0,z1,z40,z3,z4,z6]),(0,[z0,z698,z1,z9,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z131,z6]),(0,[z30,z0,z1,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z4,z6,z699]),(0,[z0,z1,z153,z9,z3,z4,z6]),(0,[z0,z700,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z701]),(0,[z0,z42,z1,z117,z3,z4,z6]),(1,[z0,z9,z3,z4,z6,z196])],[(0,[z0,z1,z40,z3,z10,z4,z6]),(0,[z0,z702,z1,z9,z3,z4,z6])],[(0,[z119,z0,z1,z151,z3,z4,z6]),(0,[z0,z1,z703,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z144,z6])],[(0,[z0,z60,z106,z9,z3,z4,z6]),(0,[z0,z20,z1,z3,z12,z4,z6]),(0,[z0,z60,z1,z9,z3,z4,z6])],[(0,[z27,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z74,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z704,z6]),(0,[z705,z0,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6,z154])],[(0,[z1,z9,z3,z120,z4,z5,z6]),(1,[z0,z77,z9,z3,z4,z6])],[(0,[z0,z1,z2,z447,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z239,z6]),(0,[z0,z706,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z123]),(0,[z0,z1,z9,z3,z114,z6,z191])],[(0,[z0,z1,z180,z3,z12,z4,z6])],[(0,[z57,z0,z1,z64,z3,z4,z6]),(0,[z409,z0,z20,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z6,z280]),(0,[z0,z75,z1,z9,z82,z3,z4])],[(0,[z0,z1,z535,z9,z3,z4,z6]),(0,[z0,z42,z1,z74,z3,z4,z6]),(0,[z0,z1,z2,z3,z12,z4,z6]),(0,[z19,z0,z1,z3,z4,z17,z6]),(1,[z103,z1,z9,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z9,z3,z707,z4,z6]),(0,[z57,z42,z1,z122,z4,z6]),(0,[z0,z708,z9,z3,z4,z6]),(0,[z0,z1,z709,z3,z4,z6])],[(0,[z0,z42,z66,z3,z4,z6]),(0,[z344,z0,z1,z9,z131,z6]),(0,[z0,z1,z3,z4,z710,z6]),(0,[z0,z1,z711,z3,z4,z6]),(0,[z0,z712,z9,z3,z4,z6]),(0,[z0,z402,z9,z3,z105,z6])],[(0,[z62,z1,z713,z3,z4,z6]),(0,[z0,z1,z51,z3,z241,z4]),(0,[z0,z714,z9,z3,z4,z6])],[(0,[z0,z146,z40,z3,z4,z6]),(0,[z108,z0,z565,z3,z137,z6]),(0,[z265,z0,z1,z4,z17,z55]),(0,[z0,z1,z3,z4,z715,z6])],[(0,[z0,z1,z3,z4,z716,z6]),(0,[z0,z717,z9,z3,z4,z6]),(0,[z0,z42,z75,z3,z4,z76]),(0,[z0,z9,z3,z241,z4,z137]),(0,[z103,z1,z3,z4,z17,z6])],[(0,[z0,z718,z1,z3,z4,z6]),(0,[z19,z0,z2,z3,z4,z22]),(0,[z30,z0,z43,z9,z131,z6])],[(0,[z0,z1,z3,z4,z719,z6]),(0,[z103,z20,z1,z3,z4,z6])],[(0,[z0,z20,z1,z3,z4,z394]),(0,[z0,z720,z1,z3,z4,z6]),(0,[z721,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z722,z6])],[(0,[z0,z42,z511,z3,z4,z6]),(0,[z0,z42,z481,z3,z4,z6]),(0,[z0,z1,z723,z3,z4,z6])],[(0,[z0,z724,z1,z3,z4,z6]),(0,[z0,z42,z277,z3,z4,z6]),(0,[z0,z1,z725,z3,z4,z6]),(0,[z38,z0,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z190,z440]),(0,[z0,z402,z318,z3,z4,z6])],[(0,[z59,z1,z40,z3,z4,z159]),(0,[z0,z249,z1,z3,z89,z4]),(0,[z417,z1,z9,z3,z300,z6])],[(0,[z0,z1,z9,z3,z726,z6]),(0,[z96,z27,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z251,z6]),(0,[z0,z1,z2,z3,z252,z6]),(0,[z0,z1,z3,z4,z727,z6]),(0,[z406,z1,z318,z3,z4,z6])],[(0,[z0,z1,z728,z3,z4,z6]),(0,[z0,z729,z1,z3,z4,z6]),(0,[z730,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z731,z6])],[(0,[z0,z73,z51,z147,z4,z6]),(0,[z0,z1,z3,z4,z732,z6]),(0,[z0,z1,z543,z3,z17,z6]),(0,[z0,z43,z3,z4,z17,z6]),(0,[z31,z1,z733,z3,z4,z6]),(0,[z0,z734,z1,z3,z4,z6])],[(0,[z0,z246,z153,z3,z4,z6]),(0,[z0,z735,z9,z3,z4,z6]),(0,[z417,z1,z9,z3,z105,z6])],[(0,[z24,z106,z118,z3,z4,z6]),(0,[z736,z106,z9,z3,z4,z6]),(0,[z736,z1,z9,z3,z4,z6])]],
   [[(0,[z0,z34,z9,z3,z4,z434]),(0,[z0,z1,z737,z3,z4,z6]),(0,[z738,z0,z1,z3,z4,z6])],[(0,[z98,z16,z9,z3,z4,z394]),(0,[z0,z739,z1,z3,z4,z6])],[(0,[z0,z175,z40,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z740]),(0,[z0,z741,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z742,z6])],[(0,[z0,z1,z117,z3,z342,z6]),(0,[z0,z1,z9,z3,z136,z191]),(1,[z743,z1,z3,z4,z6]),(0,[z108,z0,z109,z3,z137,z6]),(0,[z0,z9,z3,z744,z4,z6]),(0,[z745,z0,z1,z3,z4,z6])],[(0,[z1,z40,z447,z3,z4,z6]),(0,[z45,z0,z1,z3,z251,z6]),(0,[z0,z1,z9,z3,z4,z746])],[(0,[z0,z1,z51,z3,z4,z434]),(0,[z0,z1,z201,z4,z17,z6]),(0,[z747,z0,z1,z3,z4,z6]),(0,[z0,z1,z748,z3,z4,z6])],[(0,[z0,z1,z15,z3,z4,z99]),(0,[z0,z1,z206,z3,z4,z99]),(0,[z0,z1,z749,z3,z4,z6]),(0,[z0,z1,z750,z3,z4,z6]),(0,[z0,z1,z3,z751,z4,z6]),(0,[z0,z1,z336,z3,z4,z6]),(0,[z0,z331,z2,z3,z4,z6]),(0,[z417,z1,z318,z3,z4,z6]),(0,[z0,z752,z1,z3,z4,z6]),(0,[z0,z331,z86,z3,z4,z6])],[(0,[z509,z1,z51,z3,z4,z6]),(0,[z0,z42,z670,z3,z4,z6])],[(0,[z0,z1,z3,z4,z753,z6]),(0,[z0,z31,z1,z9,z131,z6])],[(0,[z0,z1,z207,z3,z5,z6]),(0,[z0,z1,z3,z4,z144,z6]),(0,[z19,z0,z42,z3,z4,z159]),(0,[z0,z42,z77,z3,z4,z6]),(0,[z0,z1,z3,z4,z754,z6]),(0,[z0,z1,z755,z3,z4,z6]),(0,[z0,z1,z3,z241,z4,z13]),(0,[z0,z1,z756,z3,z4,z6]),(0,[z757,z1,z9,z3,z4,z6]),(0,[z0,z1,z758,z3,z105,z6])],[(0,[z0,z1,z9,z3,z4,z759]),(0,[z0,z1,z760,z3,z4,z6]),(0,[z310,z0,z1,z3,z522,z6]),(0,[z0,z20,z1,z3,z241,z4]),(0,[z761,z1,z9,z3,z4,z6])],[(0,[z627,z0,z9,z10,z4,z6]),(0,[z0,z762,z1,z3,z4,z6]),(0,[z0,z20,z254,z3,z4,z6]),(0,[z0,z315,z9,z3,z4,z390]),(0,[z0,z1,z9,z211,z5,z6]),(0,[z0,z1,z9,z3,z4,z763])],[(0,[z31,z1,z40,z3,z4,z6]),(0,[z0,z764,z1,z3,z4,z6]),(0,[z0,z765,z1,z3,z4,z6]),(0,[z0,z766,z1,z3,z4,z6]),(0,[z19,z0,z565,z3,z4,z6]),(0,[z0,z1,z9,z767,z4,z6]),(0,[z0,z1,z312,z3,z300,z6])],[(0,[z0,z1,z3,z4,z768,z6]),(0,[z0,z20,z1,z3,z89,z4]),(0,[z0,z277,z3,z4,z39,z6]),(0,[z0,z9,z3,z4,z6,z769])],[(0,[z0,z1,z770,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z129]),(0,[z0,z1,z9,z3,z4,z771]),(0,[z0,z772,z9,z3,z4,z6]),(0,[z0,z2,z3,z371,z4,z6]),(0,[z353,z0,z569,z3,z4,z6]),(0,[z31,z43,z9,z3,z4,z6]),(0,[z0,z1,z9,z82,z4,z773])],[(0,[z0,z246,z9,z3,z4,z6]),(0,[z0,z43,z40,z3,z4,z6]),(0,[z0,z79,z9,z3,z4,z434]),(0,[z0,z1,z3,z4,z774,z6]),(0,[z468,z0,z42,z1,z3,z4]),(0,[z0,z1,z775,z3,z4,z6]),(0,[z36,z0,z569,z3,z4,z6]),(0,[z38,z0,z9,z3,z84,z4])]],
   [[(0,[z0,z1,z9,z3,z4,z776]),(0,[z288,z1,z9,z3,z628,z6]),(0,[z0,z1,z777,z3,z4,z6]),(0,[z19,z0,z9,z3,z4,z625]),(0,[z0,z778,z1,z3,z4,z6]),(0,[z0,z42,z192,z3,z4,z6]),(0,[z0,z60,z9,z3,z214,z6]),(0,[z0,z1,z312,z3,z105,z6])],[(0,[z0,z1,z83,z3,z4,z434]),(0,[z0,z1,z3,z4,z779,z6]),(0,[z0,z42,z3,z53,z4,z6]),(0,[z0,z1,z3,z4,z780,z6]),(0,[z188,z0,z3,z4,z6,z438])],[(0,[z344,z0,z1,z3,z17,z6])],[(0,[z0,z42,z3,z4,z194,z6]),(0,[z0,z42,z3,z4,z6,z196]),(0,[z0,z1,z781,z3,z4,z6])],[(0,[z0,z1,z15,z3,z4,z6]),(0,[z0,z1,z206,z3,z4,z6]),(0,[z0,z1,z782,z3,z4,z6]),(0,[z0,z1,z9,z783,z4,z6]),(0,[z0,z784,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z785,z4]),(0,[z0,z1,z786,z3,z4,z6]),(0,[z0,z1,z9,z3,z497,z191])],[(0,[z417,z1,z51,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z129]),(0,[z0,z73,z3,z4,z251,z6])],[(0,[z0,z42,z175,z3,z4,z6]),(0,[z0,z1,z787,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z123]),(0,[z0,z1,z65,z654,z4,z6]),(0,[z0,z1,z3,z114,z17,z191])],[(0,[z24,z106,z3,z4,z17,z6]),(0,[z0,z1,z9,z3,z4,z788]),(0,[z0,z1,z789,z3,z4,z6]),(0,[z0,z1,z9,z3,z790,z6]),(0,[z0,z2,z3,z4,z6,z791])],[(0,[z0,z1,z51,z3,z380,z6]),(0,[z1,z51,z541,z3,z4,z6]),(0,[z0,z1,z792,z3,z4,z6]),(0,[z0,z793,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z105,z6]),(0,[z0,z126,z60,z3,z4,z6]),(0,[z19,z0,z21,z3,z4,z22]),(0,[z0,z794,z9,z3,z4,z6])],[(0,[z24,z20,z106,z3,z4,z6]),(0,[z19,z0,z261,z3,z4,z6]),(0,[z30,z0,z1,z51,z131,z6]),(0,[z0,z1,z40,z211,z4,z6]),(0,[z0,z299,z212,z3,z4,z6]),(0,[z19,z0,z221,z3,z4,z6]),(0,[z0,z77,z104,z3,z4,z6])],[(0,[z0,z1,z3,z4,z795,z6]),(0,[z0,z1,z9,z3,z796,z6]),(0,[z0,z1,z3,z4,z797,z6]),(0,[z0,z1,z3,z4,z798,z6])],[(0,[z487,z0,z1,z9,z131,z6]),(0,[z0,z42,z668,z3,z4,z6]),(0,[z0,z132,z3,z4,z17,z6]),(0,[z265,z406,z1,z9,z4,z55])],[(0,[z0,z1,z153,z3,z4,z6]),(0,[z0,z77,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z799]),(0,[z57,z20,z1,z122,z4,z6]),(0,[z0,z800,z1,z3,z4,z6])],[(0,[z33,z1,z9,z120,z4,z434]),(0,[z288,z1,z9,z211,z4,z6])],[(0,[z0,z1,z9,z3,z4,z801]),(0,[z103,z1,z104,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z99]),(0,[z0,z1,z802,z3,z4,z6]),(0,[z0,z803,z1,z3,z4,z6]),(0,[z188,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z648,z17,z6]),(0,[z0,z1,z804,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z6,z805]),(0,[z0,z315,z269,z3,z4,z6]),(0,[z0,z42,z1,z211,z4,z6])],[(0,[z103,z1,z51,z3,z4,z6]),(0,[z158,z1,z51,z3,z4,z6]),(0,[z0,z1,z64,z3,z4,z6]),(0,[z806,z0,z1,z3,z4,z6]),(0,[z19,z0,z42,z82,z3,z4]),(0,[z0,z1,z3,z4,z807,z6]),(0,[z0,z1,z180,z3,z4,z123]),(0,[z0,z808,z1,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z394]),(0,[z499,z1,z51,z3,z4,z6]),(0,[z0,z79,z9,z3,z380,z6]),(0,[z0,z42,z3,z89,z10,z4]),(0,[z0,z126,z7,z3,z4,z6]),(0,[z0,z81,z74,z3,z4,z6]),(0,[z0,z1,z809,z3,z4,z6]),(0,[z810,z1,z2,z3,z4,z6])],[(0,[z0,z34,z40,z3,z4,z6])],[(0,[z0,z1,z9,z3,z811,z6]),(0,[z0,z1,z9,z3,z350,z6]),(0,[z0,z1,z83,z3,z380,z6]),(0,[z0,z146,z3,z4,z17,z6]),(0,[z0,z20,z74,z3,z4,z6]),(0,[z0,z1,z812,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z99]),(0,[z27,z0,z302,z3,z4,z6]),(0,[z0,z1,z813,z3,z4,z6]),(0,[z0,z1,z9,z3,z814,z4]),(0,[z0,z20,z277,z3,z4,z6]),(0,[z30,z0,z1,z9,z131,z440]),(0,[z0,z1,z9,z190,z815,z6])],[(0,[z0,z741,z1,z3,z4,z6]),(0,[z38,z0,z51,z3,z4,z6]),(0,[z0,z1,z9,z122,z350,z6]),(0,[z0,z816,z1,z3,z4,z6]),(0,[z0,z569,z3,z4,z39,z6]),(0,[z0,z1,z817,z3,z4,z6]),(0,[z265,z0,z1,z9,z4,z773])],[(0,[z1,z3,z4,z144,z100,z6]),(0,[z0,z818,z1,z3,z4,z6]),(0,[z0,z42,z1,z3,z819,z6])],[(0,[z0,z1,z820,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z239]),(0,[z0,z1,z9,z3,z821,z6]),(0,[z0,z1,z822,z3,z4,z6]),(0,[z0,z823,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z824,z6]),(0,[z101,z0,z1,z2,z3,z84])],[(0,[z0,z1,z9,z3,z4,z825])],[(0,[z57,z1,z9,z3,z4,z129]),(0,[z0,z1,z826,z3,z4,z6]),(0,[z59,z1,z3,z4,z17,z159]),(0,[z0,z42,z3,z4,z243,z6]),(0,[z0,z1,z3,z4,z13,z123]),(0,[z19,z0,z1,z9,z3,z105])],[(0,[z510,z1,z51,z3,z4,z6]),(0,[z1,z51,z3,z560,z4,z6]),(0,[z0,z827,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z6]),(0,[z59,z20,z1,z3,z4,z159]),(0,[z221,z1,z3,z4,z6,z159]),(0,[z38,z0,z42,z3,z4,z6]),(0,[z0,z1,z220,z3,z4,z6])],[(0,[z0,z1,z828,z3,z4,z6]),(0,[z0,z51,z3,z4,z6,z196]),(0,[z0,z829,z9,z3,z4,z6]),(0,[z0,z1,z336,z3,z4,z245])],[(0,[z0,z1,z3,z830,z4,z6]),(0,[z0,z1,z9,z3,z831,z4]),(0,[z0,z1,z3,z4,z832,z6]),(0,[z0,z42,z1,z3,z4,z239]),(0,[z38,z0,z9,z3,z4,z159]),(0,[z134,z0,z1,z236,z4,z6]),(0,[z0,z1,z9,z3,z84,z574]),(0,[z0,z1,z2,z3,z61,z6])]],
   [[(0,[z1,z51,z3,z4,z6,z566]),(0,[z0,z1,z833,z3,z4,z6]),(0,[z0,z834,z9,z3,z4,z6])],[(0,[z0,z246,z9,z201,z4,z6]),(0,[z0,z835,z9,z3,z4,z6])],[(0,[z0,z81,z60,z3,z4,z6]),(0,[z0,z1,z3,z241,z4,z17])],[(0,[z0,z1,z836,z3,z4,z6]),(0,[z0,z1,z9,z3,z837,z6]),(0,[z468,z0,z132,z9,z3,z4]),(0,[z0,z838,z9,z3,z4,z6]),(0,[z0,z175,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z4,z839]),(0,[z0,z840,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z841,z6])],[(0,[z0,z1,z9,z3,z842,z6]),(0,[z0,z843,z1,z3,z4,z6])],[(0,[z0,z1,z844,z3,z4,z6]),(0,[z98,z42,z16,z3,z4,z6]),(0,[z845,z0,z40,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z846]),(0,[z0,z1,z3,z847,z4,z6])],[(0,[z0,z1,z255,z3,z380,z6]),(0,[z0,z1,z848,z3,z4,z6])],[(0,[z0,z1,z51,z3,z89,z4]),(0,[z0,z849,z1,z3,z4,z6]),(0,[z850,z0,z1,z3,z4,z6]),(0,[z0,z851,z1,z3,z4,z6])],[(0,[z198,z1,z9,z120,z4,z6]),(0,[z0,z1,z852,z3,z4,z6]),(0,[z468,z0,z42,z9,z3,z4]),(0,[z225,z0,z1,z3,z17,z6]),(0,[z0,z853,z402,z3,z4,z6])],[(0,[z854,z0,z9,z3,z4,z6]),(0,[z0,z855,z1,z3,z4,z6]),(0,[z0,z42,z60,z3,z12,z6]),(0,[z0,z74,z3,z4,z6,z320]),(0,[z0,z1,z94,z4,z6,z552]),(0,[z101,z0,z1,z9,z3,z856])],[(0,[z0,z1,z857,z3,z4,z6]),(0,[z0,z261,z3,z12,z4,z6]),(1,[z468,z0,z42,z3,z4]),(0,[z468,z0,z42,z3,z4,z6]),(0,[z0,z1,z138,z3,z4,z6]),(0,[z0,z1,z9,z3,z84,z856])],[(0,[z0,z1,z9,z3,z4,z858]),(0,[z859,z0,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z860,z6]),(0,[z0,z1,z9,z4,z773,z55])],[(0,[z0,z1,z9,z3,z4,z861]),(0,[z0,z3,z862,z10,z4,z6]),(0,[z31,z1,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z863,z6]),(0,[z0,z1,z2,z3,z342,z6]),(0,[z0,z1,z153,z201,z4,z6])],[(0,[z387,z1,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z129]),(0,[z1,z3,z4,z5,z144,z6]),(0,[z31,z20,z1,z3,z4,z6]),(0,[z108,z0,z9,z3,z841,z6]),(0,[z30,z0,z1,z9,z131,z6])]],
   [[(0,[z1,z51,z3,z4,z582,z6]),(0,[z0,z864,z9,z3,z4,z6]),(0,[z33,z1,z40,z120,z4,z6])],[(0,[z0,z1,z3,z678,z17,z6]),(0,[z59,z1,z193,z3,z4,z159]),(0,[z0,z299,z9,z3,z4,z41]),(0,[z0,z42,z157,z3,z4,z6]),(0,[z0,z1,z3,z61,z345,z6]),(0,[z0,z1,z220,z3,z114,z191])],[(0,[z16,z736,z9,z3,z4,z6]),(0,[z0,z1,z3,z679,z17,z6]),(0,[z865,z0,z1,z3,z4,z6]),(0,[z1,z9,z3,z4,z866,z159])],[(0,[z0,z261,z70,z3,z4,z6]),(0,[z0,z867,z1,z3,z4,z6]),(0,[z0,z1,z868,z3,z4,z6]),(0,[z310,z0,z73,z3,z4,z6]),(0,[z0,z1,z9,z3,z105,z55])],[(0,[z24,z106,z51,z3,z4,z6]),(0,[z0,z127,z3,z4,z76,z6]),(0,[z0,z1,z869,z3,z4,z6]),(0,[z870,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z105,z72])],[(0,[z0,z1,z3,z4,z6,z871]),(0,[z872,z0,z1,z3,z4,z6])],[(0,[z0,z1,z40,z3,z873,z6]),(0,[z0,z1,z3,z190,z251,z6]),(0,[z548,z0,z42,z3,z4,z6]),(0,[z0,z42,z702,z3,z4,z6]),(0,[z417,z1,z874,z3,z4,z6])],[(0,[z19,z0,z9,z3,z4,z615]),(0,[z57,z1,z51,z122,z4,z6]),(0,[z0,z875,z1,z3,z4,z6]),(0,[z876,z0,z1,z3,z4,z6]),(0,[z45,z0,z1,z3,z342,z6]),(0,[z33,z42,z1,z120,z4,z6]),(0,[z0,z9,z3,z12,z841,z6]),(0,[z0,z1,z3,z4,z877,z6]),(0,[z0,z2,z3,z4,z6,z438]),(0,[z38,z0,z9,z82,z3,z4]),(0,[z0,z1,z878,z3,z4,z6])],[(0,[z36,z0,z569,z3,z4,z37]),(0,[z0,z879,z1,z3,z4,z6])],[(0,[z0,z1,z9,z880,z4,z6])],[(0,[z98,z16,z40,z3,z4,z6]),(0,[z0,z881,z1,z3,z4,z6]),(0,[z0,z882,z1,z3,z4,z6]),(0,[z0,z20,z331,z3,z4,z6])],[(0,[z0,z883,z9,z3,z4,z6]),(0,[z0,z362,z277,z3,z4,z6])],[(0,[z0,z1,z207,z3,z52,z6]),(0,[z0,z20,z1,z211,z4,z6]),(0,[z8,z0,z9,z445,z4,z6]),(0,[z0,z1,z297,z117,z190,z6])],[(0,[z0,z1,z3,z4,z884,z6]),(0,[z885,z0,z1,z3,z4,z6]),(0,[z0,z1,z886,z3,z4,z6])],[(0,[z0,z1,z887,z3,z4,z6]),(0,[z0,z16,z9,z3,z4,z394]),(0,[z288,z1,z3,z18,z49,z6]),(0,[z888,z1,z9,z3,z4,z6]),(0,[z0,z1,z889,z3,z4,z6])],[(0,[z0,z1,z9,z201,z4,z6]),(0,[z0,z1,z9,z3,z4,z890]),(0,[z0,z1,z3,z4,z891,z6])]],
   [[(0,[z0,z299,z40,z3,z4,z6]),(0,[z0,z1,z892,z3,z4,z6]),(0,[z0,z1,z40,z3,z300,z6]),(0,[z0,z1,z9,z3,z893,z6])],[(0,[z468,z0,z1,z40,z3,z4]),(0,[z149,z1,z40,z3,z4,z6]),(0,[z0,z1,z894,z3,z4,z6]),(0,[z0,z60,z9,z3,z12,z6])],[(0,[z0,z1,z9,z895,z4,z6]),(0,[z0,z1,z2,z3,z326,z6]),(0,[z152,z0,z1,z3,z251,z6]),(0,[z0,z20,z1,z82,z4,z72]),(0,[z0,z1,z3,z896,z4,z6]),(0,[z0,z1,z897,z3,z4,z6]),(0,[z0,z1,z2,z3,z377,z6]),(0,[z0,z1,z3,z114,z267,z191]),(0,[z898,z0,z175,z3,z4,z6])],[(0,[z0,z1,z2,z3,z527,z6]),(0,[z0,z277,z9,z3,z4,z6]),(0,[z0,z126,z73,z3,z4,z6]),(0,[z0,z60,z9,z3,z241,z4]),(0,[z0,z1,z3,z4,z899,z6]),(0,[z0,z752,z132,z3,z4,z6]),(0,[z0,z1,z3,z300,z900,z6]),(0,[z0,z1,z3,z4,z901,z6])],[(0,[z0,z1,z40,z3,z105,z6]),(0,[z0,z34,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z6,z280])],[(0,[z1,z51,z3,z4,z6,z532]),(0,[z0,z1,z9,z3,z4,z902]),(0,[z0,z1,z9,z3,z903,z6]),(0,[z0,z1,z9,z815,z131,z6]),(0,[z0,z1,z904,z3,z4,z6])],[(0,[z101,z0,z20,z1,z3,z84]),(0,[z0,z202,z60,z3,z12,z6]),(0,[z0,z60,z9,z3,z241,z12]),(0,[z0,z1,z9,z3,z4,z440])],[(0,[z905,z0,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z300,z6]),(0,[z0,z3,z4,z17,z6,z438])],[(0,[z59,z1,z51,z3,z4,z159]),(0,[z0,z1,z906,z3,z4,z6]),(0,[z0,z246,z2,z3,z4,z6]),(0,[z0,z1,z9,z3,z907,z6]),(0,[z0,z1,z908,z3,z4,z6]),(0,[z0,z909,z1,z3,z4,z6]),(0,[z0,z910,z9,z3,z4,z6])],[(0,[z19,z0,z40,z3,z4,z22]),(0,[z0,z1,z3,z4,z17,z239]),(0,[z461,z68,z1,z3,z4,z6]),(0,[z0,z60,z9,z3,z574,z6]),(0,[z0,z1,z94,z767,z4,z6])],[(0,[z0,z9,z911,z3,z4,z6]),(0,[z0,z75,z1,z9,z3,z105]),(0,[z0,z1,z912,z3,z4,z6])],[(0,[z0,z913,z9,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z123]),(0,[z914,z1,z9,z3,z4,z6]),(0,[z0,z915,z1,z3,z4,z6]),(0,[z0,z916,z1,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z917]),(0,[z0,z1,z2,z3,z4,z440])],[(0,[z24,z106,z25,z3,z4,z6]),(0,[z0,z1,z918,z3,z4,z6]),(0,[z0,z20,z246,z3,z4,z6]),(0,[z31,z1,z9,z3,z131,z6]),(0,[z563,z0,z1,z9,z131,z6])],[(0,[z0,z1,z3,z919,z4,z6]),(0,[z310,z743,z1,z3,z4,z6])],[(0,[z0,z920,z1,z3,z4,z6]),(0,[z108,z0,z20,z3,z137,z6]),(0,[z0,z20,z3,z4,z140,z6]),(0,[z257,z0,z1,z56,z4,z6])]],
   [[(0,[z27,z0,z66,z3,z4,z6]),(0,[z0,z42,z3,z185,z4,z6]),(0,[z0,z1,z9,z3,z4,z921]),(0,[z0,z1,z9,z922,z4,z6])],[(0,[z0,z1,z923,z3,z380,z6]),(0,[z0,z1,z3,z4,z924,z6]),(0,[z0,z1,z153,z3,z4,z390]),(0,[z0,z925,z9,z3,z4,z6]),(0,[z0,z1,z926,z3,z4,z6])],[(0,[z0,z1,z927,z3,z4,z6]),(0,[z0,z1,z928,z3,z4,z6]),(0,[z0,z1,z929,z3,z4,z6])],[(0,[z0,z930,z9,z3,z4,z6]),(0,[z0,z60,z1,z3,z251,z6]),(0,[z406,z1,z789,z3,z4,z6])],[(0,[z1,z44,z447,z3,z4,z6]),(0,[z8,z0,z9,z10,z4,z6])],[(0,[z0,z1,z9,z3,z4,z866]),(0,[z0,z1,z3,z4,z6,z931]),(0,[z0,z1,z9,z3,z4,z932])],[(0,[z0,z1,z933,z3,z4,z6]),(0,[z0,z261,z471,z3,z4,z6]),(0,[z408,z1,z9,z3,z4,z159]),(0,[z19,z0,z121,z3,z4,z6]),(0,[z0,z81,z3,z4,z137,z6])],[(0,[z0,z127,z3,z10,z4,z6]),(0,[z30,z0,z1,z40,z131,z6]),(0,[z0,z34,z9,z3,z4,z129]),(0,[z0,z1,z255,z3,z4,z434]),(0,[z0,z2,z3,z934,z4,z6]),(0,[z31,z1,z104,z3,z4,z6]),(0,[z30,z0,z1,z9,z131,z245])],[(0,[z0,z1,z935,z3,z4,z6]),(0,[z0,z1,z9,z936,z4,z6]),(0,[z30,z0,z42,z1,z131,z6]),(0,[z0,z21,z3,z4,z76,z6]),(0,[z0,z1,z937,z3,z4,z6]),(0,[z38,z0,z9,z3,z4,z191])],[(0,[z0,z1,z9,z3,z4,z938]),(0,[z0,z939,z1,z3,z4,z6]),(0,[z141,z0,z9,z10,z4,z6]),(0,[z103,z1,z940,z3,z4,z6]),(0,[z103,z1,z336,z3,z4,z6])],[(0,[z31,z1,z51,z3,z4,z6]),(0,[z0,z331,z40,z3,z4,z6]),(0,[z288,z1,z9,z3,z18,z6]),(0,[z0,z1,z941,z3,z4,z6]),(0,[z36,z0,z1,z3,z4,z942]),(0,[z0,z43,z104,z3,z4,z6])],[(0,[z0,z1,z713,z3,z4,z6]),(0,[z1,z51,z3,z4,z556,z6]),(0,[z0,z943,z1,z3,z4,z6]),(0,[z0,z944,z9,z3,z4,z6]),(0,[z0,z1,z945,z3,z4,z6]),(0,[z0,z1,z946,z3,z4,z6])],[(0,[z0,z1,z947,z3,z4,z6])],[(0,[z0,z43,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z350,z6]),(0,[z0,z221,z73,z3,z4,z6]),(0,[z0,z73,z9,z948,z4,z6]),(0,[z0,z1,z949,z3,z4,z6]),(0,[z950,z1,z9,z3,z4,z6])],[(0,[z0,z127,z1,z3,z4,z6]),(0,[z57,z1,z122,z4,z17,z6]),(0,[z0,z1,z3,z4,z951,z6])],[(0,[z27,z0,z73,z3,z4,z6]),(0,[z0,z1,z952,z3,z4,z6]),(1,[z0,z9,z948,z4,z6])]],
   [[(0,[z0,z1,z9,z3,z953,z6]),(0,[z0,z1,z954,z3,z4,z6]),(0,[z0,z955,z1,z3,z4,z6]),(0,[z0,z1,z207,z3,z18,z6]),(0,[z134,z0,z1,z56,z4,z6]),(0,[z0,z132,z9,z3,z300,z6])],[(0,[z176,z0,z1,z56,z4,z6]),(0,[z0,z1,z956,z3,z4,z6])],[(0,[z0,z741,z51,z3,z4,z6]),(0,[z1,z9,z3,z4,z907,z6]),(0,[z0,z1,z957,z3,z4,z6])],[(0,[z0,z315,z40,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z958]),(0,[z216,z1,z9,z3,z5,z6]),(0,[z0,z1,z9,z3,z959,z4]),(0,[z0,z1,z3,z960,z4,z6]),(0,[z0,z1,z3,z4,z112,z6])],[(0,[z0,z1,z961,z3,z4,z6]),(0,[z0,z132,z9,z3,z105,z6])],[(0,[z0,z51,z3,z4,z962,z6]),(0,[z0,z79,z40,z3,z4,z6]),(0,[z0,z1,z3,z137,z342,z6]),(0,[z0,z963,z9,z3,z4,z6]),(0,[z0,z42,z347,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z964]),(0,[z19,z0,z9,z3,z4,z965]),(0,[z30,z0,z1,z336,z131,z6]),(0,[z0,z1,z966,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z509,z16,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z967,z6])],[(0,[z0,z1,z51,z211,z4,z6]),(0,[z0,z1,z3,z4,z49,z6]),(0,[z108,z0,z40,z3,z137,z6]),(0,[z0,z1,z9,z211,z4,z239])],[(0,[z0,z1,z9,z3,z968,z6]),(0,[z0,z20,z77,z3,z4,z6]),(0,[z969,z0,z1,z3,z4,z6])],[(0,[z406,z1,z9,z3,z4,z6]),(0,[z0,z1,z970,z3,z4,z6]),(0,[z152,z246,z9,z3,z5,z6])],[(0,[z1,z106,z447,z3,z4,z6]),(0,[z0,z971,z1,z3,z4,z6]),(0,[z8,z0,z10,z4,z17,z6])],[(0,[z0,z1,z3,z4,z972,z6]),(0,[z98,z16,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z6,z973]),(0,[z0,z74,z911,z3,z4,z6]),(0,[z172,z1,z3,z4,z144,z6])],[(0,[z0,z1,z974,z3,z4,z6]),(0,[z0,z1,z975,z3,z4,z6]),(0,[z1,z51,z3,z644,z4,z6]),(0,[z0,z976,z1,z3,z4,z6]),(0,[z57,z1,z208,z122,z4,z6]),(0,[z0,z1,z3,z80,z17,z6]),(0,[z0,z977,z9,z3,z4,z6]),(0,[z0,z132,z318,z3,z4,z6]),(0,[z0,z3,z4,z6,z174,z438])],[(0,[z0,z1,z51,z82,z4,z72]),(0,[z0,z1,z3,z4,z251,z6]),(0,[z0,z1,z978,z3,z4,z6]),(0,[z0,z979,z1,z3,z4,z6]),(0,[z265,z0,z1,z9,z105,z55])],[],[(0,[z0,z261,z7,z3,z4,z6]),(0,[z0,z743,z1,z3,z4,z6]),(0,[z0,z42,z629,z3,z4,z6]),(0,[z0,z980,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z981])]],
   [[(0,[z0,z565,z3,z4,z76,z6])],[(0,[z409,z1,z51,z3,z4,z6]),(0,[z0,z982,z9,z3,z4,z6]),(0,[z0,z299,z3,z4,z17,z6]),(0,[z468,z0,z42,z3,z10,z4]),(0,[z47,z0,z1,z3,z17,z6]),(0,[z494,z0,z1,z9,z3,z84])],[(0,[z0,z983,z9,z3,z4,z6]),(0,[z487,z1,z9,z120,z4,z6]),(0,[z0,z984,z9,z3,z4,z6]),(0,[z88,z0,z1,z3,z251,z6]),(0,[z0,z20,z3,z4,z6,z196]),(0,[z0,z1,z985,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z361])],[(0,[z0,z986,z9,z3,z4,z6]),(0,[z0,z1,z987,z3,z4,z6])],[(0,[z101,z0,z1,z51,z3,z84]),(0,[z0,z20,z1,z3,z4,z129]),(0,[z33,z1,z9,z120,z4,z129]),(0,[z0,z1,z988,z3,z4,z6]),(0,[z19,z0,z20,z3,z4,z22]),(0,[z0,z1,z989,z3,z4,z6]),(0,[z0,z1,z9,z3,z114,z191])],[(0,[z19,z0,z42,z3,z4,z191]),(0,[z0,z20,z175,z3,z4,z6]),(0,[z0,z1,z2,z3,z860,z6])],[(0,[z0,z1,z51,z3,z4,z123]),(0,[z152,z1,z153,z3,z5,z6]),(0,[z0,z9,z3,z990,z4,z6]),(0,[z0,z1,z3,z61,z860,z6]),(0,[z0,z991,z9,z3,z4,z6])],[(0,[z0,z1,z135,z3,z4,z6]),(0,[z0,z1,z151,z3,z4,z6]),(0,[z119,z221,z1,z3,z4,z6]),(0,[z992,z42,z1,z3,z4,z6]),(0,[z0,z20,z1,z3,z105,z6]),(0,[z101,z0,z1,z3,z84,z17]),(0,[z993,z1,z9,z3,z4,z6]),(0,[z0,z1,z117,z190,z112,z6])],[(0,[z0,z1,z994,z3,z4,z6]),(0,[z119,z1,z447,z3,z4,z6]),(0,[z265,z188,z0,z1,z4,z55])],[(0,[z0,z1,z3,z4,z995,z6]),(0,[z0,z1,z3,z4,z996,z6]),(0,[z0,z1,z2,z3,z17,z6]),(0,[z0,z1,z997,z3,z4,z6]),(0,[z0,z1,z998,z3,z4,z6])],[(0,[z0,z999,z9,z3,z4,z6]),(0,[z0,z1,z1000,z3,z4,z6]),(0,[z19,z0,z3,z4,z17,z22]),(0,[z0,z1001,z1,z3,z4,z6])],[(0,[z0,z1,z1002,z3,z4,z6]),(0,[z0,z132,z51,z3,z4,z6]),(0,[z1,z9,z3,z4,z6,z866]),(0,[z1003,z42,z1,z3,z4,z6]),(0,[z0,z73,z121,z3,z4,z6]),(0,[z0,z75,z9,z3,z529,z4])],[(0,[z24,z391,z106,z3,z4,z6]),(0,[z0,z1,z9,z3,z1004,z6]),(0,[z0,z1,z3,z4,z6,z1005]),(0,[z0,z175,z9,z3,z84,z4])],[(0,[z1003,z310,z1,z3,z4,z6]),(0,[z0,z1,z1006,z3,z4,z6]),(0,[z0,z1,z1007,z3,z4,z6])],[(0,[z1008,z0,z1,z9,z3,z4]),(0,[z0,z126,z202,z3,z4,z6]),(0,[z45,z0,z1,z3,z860,z6])],[(0,[z0,z1,z9,z3,z1009,z6]),(0,[z0,z42,z73,z555,z4,z6]),(0,[z0,z126,z3,z4,z137,z6])]],
   [[(0,[z0,z1010,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1011,z6]),(0,[z0,z480,z20,z3,z4,z6]),(0,[z0,z1012,z1,z3,z4,z6]),(0,[z0,z1013,z1,z3,z4,z6])],[(0,[z0,z42,z3,z4,z295,z6]),(0,[z0,z21,z1,z3,z4,z6]),(0,[z45,z0,z1,z3,z17,z6]),(0,[z0,z1,z3,z139,z17,z6])],[(0,[z0,z1,z1014,z3,z4,z6]),(0,[z36,z0,z1,z3,z4,z154]),(0,[z0,z1,z3,z4,z1015,z6])],[(0,[z0,z146,z51,z3,z4,z6]),(0,[z0,z1016,z9,z3,z4,z6]),(0,[z0,z1,z9,z201,z4,z390]),(0,[z8,z468,z0,z9,z10,z4]),(0,[z1017,z1,z9,z3,z4,z6])],[(0,[z0,z1,z1018,z3,z4,z6]),(0,[z0,z1,z3,z4,z1019,z6]),(0,[z0,z1,z3,z1020,z4,z6]),(0,[z0,z42,z301,z3,z4,z6])],[(0,[z364,z1,z9,z122,z4,z6]),(0,[z0,z42,z1,z1021,z4,z6]),(0,[z0,z9,z3,z4,z965,z22]),(0,[z0,z1,z1022,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1023]),(0,[z0,z1,z3,z4,z1024,z6])],[(0,[z152,z1,z9,z3,z5,z6]),(0,[z0,z246,z9,z3,z4,z390]),(0,[z0,z851,z315,z3,z4,z6]),(0,[z0,z1,z3,z4,z1025,z6]),(0,[z0,z42,z43,z3,z4,z6]),(0,[z0,z73,z9,z555,z4,z6]),(0,[z0,z1,z3,z17,z48,z6]),(0,[z0,z1,z163,z4,z374,z6])],[(0,[z0,z1,z9,z1026,z4,z6]),(0,[z0,z1,z2,z201,z4,z6]),(0,[z0,z1027,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z245])],[(0,[z0,z741,z3,z4,z100,z6]),(0,[z33,z34,z9,z120,z4,z6])],[(0,[z1,z40,z713,z3,z4,z6]),(0,[z19,z0,z42,z3,z4,z403]),(0,[z0,z1,z3,z4,z194,z37]),(0,[z0,z60,z2,z3,z12,z6]),(0,[z0,z1,z1028,z3,z4,z6]),(0,[z265,z0,z1,z318,z4,z55])],[(0,[z183,z1,z40,z3,z4,z6]),(0,[z0,z1,z1029,z3,z4,z6]),(0,[z0,z42,z402,z3,z4,z6]),(0,[z0,z1,z9,z3,z1030,z6]),(0,[z0,z9,z3,z4,z6,z1031]),(0,[z0,z1,z9,z3,z4,z1032]),(0,[z0,z331,z3,z4,z17,z6]),(0,[z0,z1,z9,z451,z4,z72])],[(0,[z0,z1033,z9,z3,z4,z6]),(0,[z0,z1034,z1,z3,z4,z6]),(0,[z0,z277,z2,z3,z4,z6])],[(0,[z24,z221,z1,z3,z4,z6]),(0,[z11,z106,z9,z3,z4,z6]),(0,[z0,z1,z1035,z3,z4,z6]),(0,[z661,z0,z1,z9,z3,z84]),(0,[z0,z1,z9,z3,z856,z4])],[(0,[z0,z1,z1036,z3,z4,z6]),(0,[z363,z1,z51,z3,z4,z6]),(0,[z57,z221,z1,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z239]),(0,[z0,z1,z3,z160,z17,z6]),(0,[z0,z1,z9,z3,z1037,z6]),(0,[z0,z1,z2,z3,z4,z245]),(0,[z101,z0,z1,z86,z3,z84])],[(0,[z0,z1,z3,z4,z6,z1038]),(0,[z0,z1039,z1,z3,z4,z6]),(0,[z0,z1,z9,z4,z815,z6])]],
   [[(0,[z0,z70,z1,z3,z4,z6]),(0,[z176,z0,z1,z165,z4,z6]),(0,[z0,z1,z9,z3,z4,z1040]),(0,[z0,z1,z1041,z3,z4,z6]),(0,[z0,z42,z3,z862,z4,z6])],[(0,[z0,z1042,z51,z3,z4,z6]),(0,[z1,z9,z3,z907,z5,z6]),(0,[z0,z1043,z1,z3,z4,z6]),(0,[z0,z1,z1044,z3,z4,z6]),(1,[z0,z1,z9,z815,z6])],[(0,[z0,z1,z1045,z3,z4,z6])],[(0,[z0,z1,z1046,z3,z4,z6]),(0,[z98,z27,z16,z3,z4,z6]),(0,[z0,z1,z212,z3,z4,z6]),(0,[z0,z175,z51,z3,z4,z6]),(0,[z0,z565,z3,z10,z4,z6]),(0,[z36,z0,z277,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1047]),(0,[z0,z315,z3,z4,z17,z6]),(0,[z0,z1,z1048,z3,z4,z6]),(0,[z0,z1,z3,z17,z6,z218]),(0,[z0,z42,z323,z3,z4,z6]),(0,[z0,z1049,z1,z3,z4,z6])],[(0,[z98,z20,z16,z3,z4,z6]),(0,[z0,z1050,z1,z3,z4,z6]),(0,[z0,z1051,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z1052,z4]),(0,[z1053,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1054]),(0,[z0,z79,z3,z4,z17,z6]),(0,[z0,z939,z299,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z1055])],[(0,[z0,z1,z557,z3,z4,z6]),(0,[z1,z9,z3,z120,z350,z6]),(0,[z0,z42,z73,z147,z4,z6]),(0,[z0,z1,z1056,z3,z4,z6]),(0,[z0,z77,z336,z3,z4,z6])],[(0,[z98,z16,z51,z3,z4,z6]),(0,[z0,z60,z1,z3,z345,z6]),(1,[z0,z1,z767,z4,z6]),(0,[z358,z0,z1,z3,z4,z37])],[(0,[z0,z1,z109,z3,z4,z6]),(0,[z0,z20,z60,z3,z12,z6]),(0,[z0,z1057,z3,z4,z17,z6]),(0,[z1058,z0,z1,z9,z3,z4])],[(0,[z0,z1,z3,z4,z1059,z6]),(0,[z0,z1,z1060,z3,z4,z6]),(0,[z0,z1,z9,z3,z1061,z6]),(0,[z33,z1,z83,z120,z4,z6]),(0,[z0,z565,z1,z3,z4,z6]),(0,[z0,z1,z1062,z3,z4,z6]),(0,[z101,z0,z1,z9,z3,z84])],[(0,[z0,z1,z3,z380,z995,z6]),(0,[z721,z42,z1,z3,z4,z6]),(0,[z0,z42,z1,z3,z722,z6])],[(0,[z221,z1,z40,z3,z4,z6]),(0,[z0,z246,z269,z3,z4,z6]),(0,[z0,z1,z3,z1063,z4,z6]),(0,[z30,z0,z1,z104,z131,z6])],[(0,[z57,z1,z9,z1064,z4,z6]),(0,[z8,z0,z2,z10,z4,z6]),(0,[z0,z1,z2,z3,z477,z6])],[(0,[z0,z1,z9,z3,z350,z434]),(0,[z0,z1,z3,z4,z1065,z6]),(0,[z0,z1,z3,z185,z4,z6]),(0,[z108,z0,z3,z248,z137,z6]),(0,[z0,z1,z9,z3,z4,z1066]),(0,[z0,z1,z1067,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1068]),(0,[z0,z1,z51,z3,z4,z129]),(0,[z0,z569,z9,z3,z4,z6]),(0,[z0,z73,z9,z147,z4,z6]),(0,[z1069,z1,z9,z3,z4,z6]),(0,[z0,z1,z1070,z3,z4,z6])]],
   [[(0,[z0,z261,z73,z3,z4,z6]),(0,[z0,z1071,z9,z3,z4,z6]),(0,[z8,z0,z249,z10,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1072]),(0,[z0,z1,z3,z4,z6,z1073]),(0,[z0,z1074,z9,z3,z4,z6])],[(0,[z0,z51,z3,z4,z6,z1075]),(0,[z0,z1,z51,z3,z105,z6]),(0,[z1,z9,z3,z1064,z4,z6]),(0,[z31,z1,z336,z3,z4,z6]),(0,[z0,z1076,z9,z3,z4,z6])],[(0,[z24,z736,z9,z3,z4,z6]),(0,[z0,z1,z211,z4,z17,z6]),(0,[z288,z1,z2,z3,z18,z6]),(0,[z0,z42,z3,z4,z425,z6])],[(0,[z0,z1,z1077,z3,z4,z6]),(0,[z0,z9,z3,z1078,z4,z6]),(0,[z0,z1,z3,z4,z6,z1079]),(0,[z1080,z1,z9,z3,z4,z6])],[(0,[z0,z40,z3,z371,z4,z6]),(0,[z0,z1,z9,z3,z4,z390]),(0,[z0,z1,z9,z211,z18,z6]),(0,[z0,z569,z2,z3,z4,z6]),(0,[z0,z43,z336,z3,z4,z6])],[(0,[z33,z20,z1,z120,z4,z6])],[(0,[z0,z1,z9,z3,z4,z434]),(0,[z0,z42,z20,z3,z4,z6]),(0,[z0,z42,z3,z4,z76,z6]),(0,[z19,z0,z9,z3,z4,z50])],[(0,[z1,z51,z3,z697,z4,z6]),(0,[z0,z42,z348,z3,z4,z6]),(0,[z0,z1,z3,z4,z1081,z6]),(0,[z1082,z0,z1,z3,z4,z6])],[(0,[z0,z1083,z1,z3,z4,z6]),(0,[z0,z79,z9,z3,z4,z129]),(0,[z152,z1,z9,z201,z5,z6]),(0,[z0,z1,z86,z3,z4,z6])],[(0,[z1,z40,z430,z3,z4,z6]),(0,[z468,z0,z74,z9,z3,z4]),(0,[z0,z402,z9,z3,z4,z6])],[(0,[z0,z1,z15,z3,z4,z394]),(0,[z0,z1,z206,z3,z4,z394]),(0,[z0,z1,z83,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z390]),(0,[z1084,z1,z9,z3,z4,z6]),(0,[z19,z0,z3,z4,z280,z22])],[(0,[z0,z9,z3,z948,z4,z6]),(0,[z0,z1085,z1,z3,z4,z6]),(0,[z0,z1,z1086,z3,z4,z6]),(0,[z265,z0,z1,z312,z4,z55]),(0,[z265,z0,z1,z9,z300,z55])],[],[(0,[z221,z16,z1,z3,z4,z6]),(0,[z0,z1,z1087,z3,z4,z6]),(0,[z1,z51,z3,z4,z144,z6]),(0,[z0,z1,z3,z4,z248,z6]),(0,[z0,z1,z9,z3,z4,z1088])],[(0,[z0,z42,z146,z3,z4,z6]),(0,[z108,z0,z1,z3,z251,z6]),(0,[z0,z73,z9,z368,z4,z6]),(0,[z31,z1,z9,z3,z190,z6])]],
   [[(0,[z0,z1,z1089,z3,z4,z6]),(0,[z0,z1,z3,z4,z342,z6]),(0,[z1090,z0,z1,z3,z4,z6]),(0,[z0,z40,z3,z4,z6,z1091]),(0,[z310,z0,z60,z3,z12,z6]),(0,[z0,z1,z1092,z3,z4,z6]),(0,[z0,z1,z1093,z3,z4,z6]),(0,[z0,z402,z2,z3,z4,z6])],[(0,[z0,z1,z9,z1094,z4,z6]),(0,[z0,z1,z9,z3,z1095,z6]),(0,[z0,z1,z2,z3,z500,z6]),(0,[z247,z0,z1,z3,z4,z403])],[(0,[z0,z1,z3,z1096,z4,z6]),(0,[z0,z315,z9,z211,z4,z6]),(0,[z0,z42,z3,z445,z4,z6]),(0,[z0,z853,z1,z3,z4,z6]),(0,[z0,z1097,z1,z3,z4,z6]),(0,[z0,z1,z1098,z3,z4,z6]),(0,[z406,z1,z2,z3,z4,z6])],[(0,[z0,z3,z185,z371,z4,z6])],[(0,[z0,z34,z51,z3,z4,z6]),(0,[z1099,z0,z1,z3,z4,z6]),(0,[z0,z1100,z1,z3,z4,z6]),(0,[z288,z1,z135,z3,z18,z6]),(0,[z0,z1,z1101,z3,z4,z6])],[(0,[z0,z1,z1102,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1103]),(0,[z265,z0,z1,z2,z4,z55])],[(0,[z0,z1,z1104,z3,z4,z6]),(0,[z0,z20,z1,z3,z300,z6]),(0,[z0,z9,z3,z4,z6,z965]),(0,[z0,z1,z1105,z3,z4,z6])],[(0,[z0,z1,z1106,z3,z4,z6]),(0,[z0,z1,z3,z1107,z4,z6]),(0,[z417,z1,z9,z3,z4,z6]),(0,[z19,z310,z0,z3,z4,z6]),(0,[z0,z202,z1,z3,z345,z6]),(0,[z0,z20,z402,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1108]),(0,[z0,z1,z3,z4,z1109,z6]),(0,[z0,z9,z1110,z3,z4,z6])],[(0,[z0,z1111,z1,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z239]),(0,[z288,z1,z447,z3,z4,z6]),(0,[z0,z42,z73,z236,z4,z6]),(0,[z0,z1112,z43,z3,z4,z6])],[(0,[z0,z1,z269,z3,z4,z6]),(0,[z0,z1,z9,z3,z380,z6]),(0,[z468,z0,z60,z9,z3,z4]),(0,[z0,z1,z1113,z3,z4,z6]),(0,[z0,z1,z1114,z3,z4,z6])],[(0,[z0,z1,z1115,z3,z4,z6]),(0,[z0,z1,z1116,z3,z4,z6]),(0,[z108,z0,z3,z137,z17,z6])],[(0,[z0,z1,z40,z3,z4,z99]),(0,[z0,z1,z3,z4,z6,z1117]),(0,[z0,z1,z3,z4,z1118,z6])],[(0,[z0,z1,z1119,z3,z4,z6]),(0,[z0,z1,z1120,z3,z4,z6]),(0,[z417,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z114,z191]),(0,[z30,z31,z1,z9,z131,z6]),(0,[z0,z1121,z9,z3,z4,z6])],[(0,[z1122,z0,z1,z3,z4,z6]),(0,[z0,z1,z1123,z3,z4,z6]),(0,[z0,z1,z255,z3,z4,z129]),(0,[z0,z42,z1,z3,z796,z6]),(0,[z0,z77,z9,z3,z4,z6]),(0,[z0,z21,z3,z10,z4,z6]),(0,[z0,z1,z3,z4,z1124,z6])],[(0,[z483,z0,z1,z3,z17,z6]),(0,[z0,z202,z1,z3,z490,z6]),(0,[z0,z1125,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z1126,z3,z4,z6]),(0,[z0,z34,z83,z3,z4,z6]),(0,[z0,z1127,z9,z3,z4,z6])],[(0,[z0,z315,z51,z3,z4,z6]),(0,[z1,z9,z120,z5,z131,z6]),(0,[z0,z315,z9,z3,z4,z239]),(0,[z1,z9,z211,z4,z5,z6]),(0,[z0,z741,z3,z4,z5,z6]),(0,[z0,z1,z3,z1128,z4,z6]),(0,[z0,z1,z9,z3,z4,z1129]),(0,[z0,z9,z3,z4,z6,z1130])],[(0,[z101,z0,z1,z40,z3,z84]),(0,[z0,z42,z1,z3,z4,z801]),(0,[z0,z1,z758,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z99]),(0,[z0,z79,z51,z3,z4,z6]),(0,[z103,z1,z9,z3,z4,z6]),(0,[z0,z42,z3,z4,z6,z438]),(0,[z101,z0,z42,z1,z3,z84]),(0,[z674,z0,z9,z3,z137,z6]),(0,[z379,z1,z447,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z394]),(0,[z0,z106,z9,z3,z4,z394]),(0,[z0,z1,z9,z3,z6,z1131]),(0,[z0,z1132,z9,z3,z4,z6]),(0,[z0,z1,z1133,z3,z4,z6]),(0,[z0,z20,z504,z3,z4,z6]),(0,[z0,z9,z3,z4,z1134,z6]),(0,[z0,z1135,z9,z3,z4,z6])],[(0,[z108,z0,z51,z3,z137,z6]),(0,[z1,z447,z122,z3,z4,z6]),(0,[z0,z1,z3,z4,z1136,z6]),(0,[z0,z1,z9,z948,z4,z6])],[(0,[z0,z1,z1137,z3,z4,z6]),(0,[z0,z1138,z1,z3,z4,z6]),(0,[z1139,z1,z9,z3,z4,z6])],[(0,[z1,z40,z271,z3,z4,z6]),(0,[z0,z1,z1140,z3,z4,z6]),(0,[z0,z1,z3,z1141,z4,z6]),(0,[z0,z1,z3,z124,z4,z37])],[(0,[z0,z1,z3,z4,z6,z1142]),(0,[z0,z1,z3,z342,z6,z191]),(0,[z0,z42,z1,z3,z350,z6]),(0,[z0,z1,z9,z3,z4,z1143]),(0,[z38,z0,z9,z3,z4,z6]),(1,[z0,z1,z3,z860,z6])],[(0,[z0,z3,z4,z251,z76,z6]),(0,[z0,z1,z312,z3,z4,z6]),(0,[z0,z1,z65,z767,z4,z6]),(0,[z0,z1144,z9,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z394]),(0,[z0,z971,z79,z3,z4,z6]),(0,[z1,z9,z3,z211,z5,z6]),(0,[z113,z1,z9,z3,z4,z159]),(0,[z0,z42,z3,z10,z4,z6]),(0,[z468,z0,z9,z147,z3,z4]),(0,[z0,z1,z1145,z3,z4,z6]),(0,[z0,z1,z9,z117,z815,z6]),(0,[z0,z1146,z1,z3,z4,z6])],[(0,[z0,z9,z234,z10,z4,z6])],[(0,[z0,z1147,z40,z3,z4,z6]),(0,[z0,z1,z3,z4,z1148,z6]),(0,[z108,z0,z42,z3,z137,z6])],[(0,[z0,z1,z1149,z3,z4,z6]),(0,[z24,z0,z126,z3,z4,z6]),(0,[z0,z42,z3,z371,z4,z6]),(0,[z0,z1,z1150,z3,z4,z6]),(0,[z0,z1,z1151,z3,z4,z6]),(0,[z265,z38,z0,z9,z4,z55])],[(0,[z0,z1,z9,z3,z1152,z6]),(0,[z0,z1,z58,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1153]),(0,[z216,z1,z51,z3,z4,z6]),(0,[z0,z79,z83,z3,z4,z6]),(0,[z0,z1,z1154,z3,z4,z6]),(0,[z0,z1,z3,z1155,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z1156,z6]),(0,[z0,z1,z207,z3,z61,z6]),(0,[z152,z1,z2,z3,z5,z6]),(0,[z0,z1,z297,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z6]),(0,[z0,z1157,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1158,z6]),(0,[z33,z1,z51,z120,z4,z6]),(0,[z0,z1159,z1,z3,z4,z6]),(0,[z0,z1160,z1,z3,z4,z6])],[(0,[z0,z1161,z1,z3,z4,z6]),(0,[z0,z1162,z1,z3,z4,z6]),(0,[z0,z1,z1163,z3,z4,z6]),(0,[z0,z1,z318,z3,z300,z6])],[(0,[z0,z66,z1,z3,z4,z6]),(0,[z0,z66,z106,z3,z4,z6]),(0,[z0,z68,z1,z3,z4,z6]),(0,[z0,z34,z255,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1164]),(0,[z0,z956,z3,z4,z6,z438])],[(0,[z0,z1,z1165,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1166]),(0,[z19,z0,z9,z3,z4,z276])],[(0,[z0,z1,z3,z4,z1167,z6]),(0,[z0,z1,z3,z4,z6,z1168]),(0,[z333,z0,z1,z9,z131,z6]),(0,[z19,z0,z9,z3,z4,z278]),(0,[z0,z1,z3,z1169,z4,z6]),(0,[z31,z1,z9,z117,z4,z6]),(0,[z0,z175,z9,z3,z4,z191])],[(0,[z1170,z1,z9,z3,z4,z6]),(0,[z0,z1,z318,z3,z105,z6])],[(0,[z0,z1,z9,z3,z1171,z6]),(0,[z108,z0,z102,z3,z137,z6]),(0,[z0,z1,z9,z3,z241,z4]),(0,[z0,z1172,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1173,z6]),(0,[z0,z1,z1174,z3,z4,z6]),(0,[z0,z42,z287,z3,z4,z6])],[(0,[z0,z1,z1175,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1176]),(0,[z0,z1,z9,z3,z4,z1177]),(0,[z101,z0,z1,z3,z251,z6]),(0,[z0,z1,z9,z3,z89,z4]),(0,[z0,z1,z3,z1178,z4,z6]),(0,[z0,z1,z9,z1179,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1180]),(0,[z0,z1,z40,z3,z863,z6]),(0,[z0,z42,z34,z3,z4,z6]),(0,[z33,z79,z9,z120,z4,z6]),(0,[z1181,z1,z9,z3,z4,z6])],[(0,[z0,z1,z3,z1182,z4,z6]),(0,[z0,z1,z3,z4,z1183,z6]),(0,[z0,z1,z269,z201,z4,z6]),(0,[z310,z0,z1,z3,z251,z6])],[(0,[z0,z9,z3,z1184,z4,z6]),(0,[z0,z1185,z1,z3,z4,z6]),(0,[z0,z1,z1186,z3,z4,z6]),(0,[z0,z1,z2,z3,z241,z4]),(0,[z19,z0,z132,z9,z3,z4]),(0,[z1187,z1,z9,z3,z4,z6]),(0,[z0,z1,z1188,z3,z4,z6]),(0,[z1189,z38,z0,z3,z4,z6]),(0,[z0,z1,z1190,z3,z4,z6])],[(0,[z0,z40,z3,z4,z6,z438]),(0,[z57,z1,z9,z3,z350,z6]),(0,[z0,z1,z3,z862,z4,z6])],[(0,[z1,z447,z3,z4,z5,z6]),(0,[z0,z1,z1191,z3,z4,z6])]],
   [[(0,[z221,z1,z3,z120,z4,z6]),(0,[z0,z1,z9,z3,z4,z1192]),(0,[z0,z1,z3,z4,z6,z1193]),(0,[z31,z1,z869,z3,z4,z6])],[(0,[z0,z1,z9,z1194,z4,z6]),(0,[z0,z1195,z9,z3,z4,z6]),(0,[z0,z299,z51,z3,z4,z6]),(0,[z0,z1,z51,z3,z300,z6]),(0,[z0,z1,z1196,z3,z4,z6]),(0,[z0,z1,z3,z4,z1197,z6])],[(0,[z1,z9,z120,z4,z350,z6]),(0,[z0,z1198,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z863,z6]),(0,[z265,z0,z20,z1,z4,z55]),(0,[z468,z0,z9,z3,z4,z22]),(0,[z19,z0,z9,z3,z687,z4]),(0,[z0,z1,z1199,z3,z4,z6])],[(0,[z0,z42,z585,z3,z4,z6]),(0,[z0,z911,z7,z3,z4,z6])],[(0,[z108,z0,z261,z3,z4,z6]),(0,[z0,z1,z2,z3,z476,z6]),(0,[z0,z1,z1200,z3,z4,z6])],[(0,[z0,z1,z1201,z3,z4,z6]),(0,[z0,z1,z3,z4,z1202,z6]),(0,[z19,z0,z42,z3,z4,z6]),(0,[z0,z383,z1,z3,z4,z194]),(0,[z183,z1,z44,z3,z4,z6])],[(0,[z24,z106,z9,z3,z4,z6]),(0,[z1203,z1,z9,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1204]),(0,[z0,z77,z9,z3,z4,z440])],[(0,[z0,z51,z3,z371,z4,z6]),(0,[z0,z73,z2,z147,z4,z6])],[(0,[z0,z20,z3,z384,z4,z6]),(0,[z0,z1,z3,z1205,z4,z6])],[(0,[z0,z42,z444,z3,z4,z6]),(0,[z46,z1,z51,z3,z4,z6]),(0,[z19,z0,z51,z3,z4,z22]),(0,[z0,z299,z9,z3,z4,z159])],[(0,[z1206,z1,z9,z3,z4,z6]),(0,[z310,z0,z347,z3,z4,z6]),(0,[z103,z1,z9,z3,z4,z245])],[(0,[z0,z1,z40,z201,z4,z6]),(0,[z0,z1,z1207,z3,z4,z6]),(0,[z103,z1,z9,z3,z4,z440])],[(0,[z0,z1,z3,z4,z17,z99]),(0,[z0,z1,z40,z3,z893,z6]),(0,[z288,z1,z3,z4,z144,z6]),(0,[z0,z1,z3,z4,z1208,z6]),(0,[z0,z202,z1,z3,z4,z6]),(0,[z0,z42,z1,z880,z4,z6]),(0,[z0,z1,z9,z3,z4,z1209]),(0,[z0,z1,z9,z3,z1210,z4]),(0,[z36,z0,z1,z3,z4,z237]),(0,[z0,z1,z9,z3,z856,z191])],[(0,[z97,z1,z3,z4,z144,z6]),(0,[z0,z42,z79,z3,z4,z6]),(0,[z0,z1211,z1,z3,z4,z6]),(0,[z1212,z1,z9,z3,z4,z6])],[(0,[z0,z246,z40,z3,z4,z6]),(0,[z1213,z0,z299,z3,z4,z6])]],
   [[(0,[z33,z1,z255,z120,z4,z6]),(0,[z0,z1,z2,z3,z4,z434]),(0,[z0,z1214,z1,z3,z4,z6]),(0,[z0,z1215,z9,z3,z4,z6]),(0,[z265,z0,z402,z9,z4,z55])],[(0,[z19,z0,z42,z3,z4,z22]),(0,[z0,z1,z2,z3,z404,z6])],[(0,[z0,z1,z1216,z3,z4,z6]),(0,[z0,z1217,z9,z3,z4,z6]),(0,[z134,z0,z1,z767,z4,z6])],[(0,[z626,z1,z51,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z440]),(0,[z0,z42,z1,z201,z4,z6]),(0,[z0,z1,z1218,z3,z4,z6]),(0,[z0,z9,z3,z4,z76,z184])],[(0,[z0,z1,z3,z4,z1219,z6]),(0,[z0,z720,z246,z3,z4,z6]),(0,[z0,z1,z1220,z3,z4,z6]),(0,[z0,z1,z3,z4,z1221,z6]),(0,[z0,z1,z2,z3,z576,z6])],[(0,[z0,z1,z9,z1222,z4,z6]),(0,[z1213,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z345,z6]),(0,[z0,z1,z9,z128,z190,z6])],[(0,[z0,z20,z43,z3,z4,z6]),(0,[z406,z402,z9,z3,z4,z6])],[(0,[z356,z1,z40,z3,z4,z6]),(0,[z0,z1,z3,z860,z17,z6]),(0,[z0,z1,z3,z4,z860,z6])],[(0,[z0,z1,z9,z3,z4,z1223]),(0,[z1,z9,z122,z1064,z4,z6])],[(0,[z1224,z0,z1,z9,z3,z6]),(0,[z0,z1,z1225,z3,z4,z6]),(0,[z0,z20,z3,z371,z4,z6])],[(0,[z1,z40,z634,z3,z4,z6]),(0,[z59,z1,z9,z3,z4,z159]),(0,[z0,z42,z1,z3,z4,z440]),(0,[z685,z0,z42,z3,z4,z6])],[(0,[z0,z331,z51,z3,z4,z6]),(0,[z0,z42,z3,z528,z4,z6]),(0,[z0,z9,z3,z4,z6,z196]),(0,[z0,z81,z264,z3,z4,z6])],[(0,[z0,z1226,z9,z3,z4,z6]),(0,[z0,z1,z3,z1227,z4,z6]),(0,[z0,z42,z3,z529,z4,z6]),(0,[z1228,z0,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z942])],[(0,[z0,z1229,z9,z3,z4,z6]),(0,[z0,z1230,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z856,z114])],[(0,[z19,z0,z127,z3,z4,z6]),(0,[z0,z1,z733,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1231])],[(0,[z0,z1,z9,z3,z1232,z6]),(0,[z119,z1,z51,z3,z4,z41]),(0,[z0,z9,z3,z4,z962,z6]),(0,[z370,z1,z40,z3,z4,z6]),(0,[z0,z1233,z1,z3,z4,z6]),(0,[z0,z1,z269,z3,z4,z390]),(0,[z0,z1,z1234,z3,z4,z6])]],
   [[(0,[z110,z106,z9,z3,z4,z6]),(0,[z1,z713,z51,z3,z4,z6]),(0,[z0,z1,z9,z82,z641,z4]),(0,[z0,z3,z371,z4,z17,z6])],[(0,[z8,z0,z40,z10,z4,z6]),(0,[z0,z1,z3,z251,z131,z6]),(0,[z0,z1235,z9,z3,z4,z6]),(0,[z103,z1,z945,z3,z4,z6]),(0,[z0,z1,z9,z3,z815,z6]),(0,[z417,z402,z9,z3,z4,z6]),(0,[z0,z1,z1236,z3,z4,z6])],[(0,[z1237,z0,z1,z3,z4,z6]),(0,[z0,z1,z1238,z3,z4,z6]),(0,[z446,z0,z42,z3,z4,z6])],[(0,[z0,z51,z3,z707,z4,z6]),(0,[z0,z1,z2,z3,z380,z6]),(0,[z0,z42,z3,z4,z6,z1239]),(0,[z0,z1112,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1240,z6]),(0,[z30,z0,z1,z17,z131,z6])],[(0,[z0,z1,z40,z3,z350,z6]),(0,[z0,z1,z1241,z3,z4,z6]),(0,[z0,z1242,z1,z3,z4,z6])],[(0,[z309,z0,z1,z3,z17,z6]),(0,[z265,z0,z1,z4,z174,z55])],[(0,[z589,z0,z1,z9,z4,z55]),(0,[z0,z1,z180,z3,z4,z6]),(0,[z0,z1,z181,z3,z4,z6]),(0,[z0,z20,z73,z147,z4,z6]),(0,[z0,z3,z4,z6,z196,z320]),(0,[z0,z1,z3,z1243,z4,z6])],[(0,[z0,z1244,z1,z3,z4,z6]),(0,[z0,z1,z1245,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1246]),(0,[z0,z1,z3,z4,z6,z174]),(0,[z0,z77,z2,z3,z4,z6])],[(0,[z0,z70,z254,z3,z4,z6]),(0,[z0,z1,z153,z211,z4,z6]),(0,[z0,z1,z3,z1247,z4,z6])],[(0,[z0,z1,z2,z3,z522,z6]),(0,[z0,z1,z9,z3,z4,z1248]),(0,[z0,z1249,z1,z3,z4,z6])],[(0,[z57,z1,z9,z435,z4,z6]),(0,[z0,z1,z1250,z3,z4,z6]),(0,[z0,z1,z3,z4,z942,z37]),(0,[z0,z1,z1251,z3,z4,z6]),(0,[z0,z1252,z9,z3,z4,z6])],[(0,[z0,z1,z1253,z3,z4,z6]),(0,[z0,z1,z3,z1254,z4,z6]),(0,[z288,z1,z58,z3,z18,z6]),(0,[z0,z1,z1255,z3,z4,z6]),(0,[z0,z9,z147,z4,z6,z591]),(0,[z406,z75,z1,z9,z3,z4]),(0,[z0,z1,z69,z3,z4,z686]),(0,[z1256,z0,z1,z3,z4,z6]),(0,[z0,z1257,z1,z3,z4,z6])],[(0,[z31,z1,z9,z3,z4,z6]),(0,[z0,z1,z1258,z3,z4,z6]),(0,[z0,z75,z132,z9,z3,z4]),(0,[z357,z0,z1,z130,z4,z6]),(0,[z103,z1,z2,z3,z4,z6])],[(0,[z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z1259,z3,z4,z6]),(0,[z354,z0,z1,z3,z4,z37]),(0,[z97,z1,z713,z3,z4,z6]),(0,[z898,z0,z1,z3,z4,z6]),(0,[z0,z126,z3,z4,z452,z6])],[(0,[z0,z1,z3,z4,z6,z1260]),(0,[z0,z1,z1261,z3,z4,z6]),(0,[z288,z42,z1,z3,z18,z6]),(0,[z0,z42,z299,z3,z4,z6]),(0,[z30,z103,z1,z9,z131,z6]),(0,[z0,z1262,z1,z3,z4,z6])],[(0,[z0,z1,z90,z359,z4,z6]),(0,[z152,z1,z9,z3,z5,z390]),(0,[z0,z20,z630,z3,z4,z6]),(0,[z0,z43,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z1263,z6]),(0,[z0,z1,z1264,z3,z4,z6]),(0,[z0,z1,z3,z1265,z4,z6])]],
   [[(0,[z0,z1266,z9,z3,z4,z6]),(0,[z265,z0,z1,z51,z4,z55]),(0,[z0,z1,z3,z4,z13,z6]),(0,[z0,z277,z3,z56,z4,z6]),(0,[z0,z277,z65,z3,z4,z6]),(0,[z0,z1,z1267,z3,z4,z6])],[(0,[z36,z0,z1,z3,z4,z291]),(0,[z0,z42,z3,z4,z6,z320]),(0,[z38,z0,z2,z3,z4,z6])],[(0,[z222,z1,z40,z3,z4,z6]),(0,[z0,z1268,z1,z3,z4,z6])],[(0,[z1,z9,z3,z4,z1269,z6]),(0,[z0,z402,z312,z3,z4,z6]),(0,[z101,z0,z1,z138,z3,z84])],[(0,[z0,z1,z9,z3,z1270,z4]),(0,[z0,z1,z1271,z3,z4,z6]),(0,[z0,z741,z9,z3,z4,z6]),(0,[z0,z1,z1272,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1273]),(0,[z288,z1,z3,z18,z17,z6]),(0,[z0,z513,z1,z555,z4,z6]),(0,[z1274,z1,z9,z3,z4,z6]),(0,[z406,z1,z312,z3,z4,z6])],[(0,[z0,z1,z1275,z3,z4,z6]),(0,[z0,z1,z1276,z3,z4,z6])],[(0,[z0,z1,z207,z3,z4,z6]),(0,[z0,z1,z1277,z3,z4,z6]),(0,[z0,z1278,z9,z3,z4,z6])],[(0,[z0,z1,z1279,z3,z4,z6]),(0,[z152,z1,z3,z5,z17,z6]),(0,[z0,z1280,z9,z3,z4,z6])],[(0,[z673,z106,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1281]),(0,[z506,z1,z40,z3,z4,z6])],[(0,[z0,z1282,z9,z3,z4,z6])],[(0,[z0,z1,z3,z350,z17,z6]),(0,[z0,z1,z1283,z3,z4,z6]),(0,[z0,z1,z1284,z3,z4,z6]),(0,[z19,z0,z9,z3,z4,z373]),(0,[z0,z1,z1285,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1286,z6]),(0,[z525,z16,z9,z3,z4,z6]),(0,[z0,z1,z1287,z3,z4,z6]),(0,[z0,z1233,z79,z3,z4,z6]),(0,[z0,z1,z94,z53,z4,z6]),(0,[z0,z1,z1288,z3,z4,z6])],[(0,[z101,z0,z1,z3,z342,z6]),(0,[z0,z1,z3,z380,z17,z6]),(0,[z0,z1,z1289,z3,z4,z6]),(0,[z0,z42,z3,z4,z564,z6]),(0,[z406,z42,z1,z3,z4,z6]),(0,[z1290,z1,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1291,z6]),(0,[z0,z1,z91,z3,z4,z6]),(0,[z0,z1,z1292,z3,z4,z6]),(0,[z134,z0,z1,z179,z4,z6]),(0,[z0,z20,z146,z3,z4,z6]),(0,[z0,z42,z132,z3,z4,z6]),(0,[z1293,z0,z9,z3,z4,z6])],[(0,[z0,z1,z9,z82,z4,z72])]],
   [[(0,[z57,z1,z64,z122,z4,z6]),(0,[z0,z246,z3,z4,z17,z6]),(0,[z0,z1,z1294,z3,z4,z6]),(0,[z417,z1,z312,z3,z4,z6])],[(0,[z0,z51,z3,z4,z6,z438]),(0,[z0,z1,z40,z3,z114,z191]),(0,[z0,z42,z3,z4,z572,z6]),(0,[z1295,z1,z9,z3,z4,z6]),(0,[z0,z277,z3,z4,z17,z6])],[(0,[z19,z27,z0,z3,z4,z6]),(0,[z0,z1,z9,z3,z1296,z6]),(0,[z0,z1,z3,z4,z1297,z6]),(0,[z0,z1,z9,z3,z1298,z6]),(0,[z0,z3,z4,z17,z6,z1055]),(0,[z0,z1299,z1,z3,z4,z6])],[(0,[z0,z261,z16,z3,z4,z6]),(0,[z0,z1300,z1,z3,z4,z6]),(0,[z8,z0,z185,z10,z4,z6]),(0,[z0,z1,z2,z3,z89,z4]),(0,[z0,z1,z3,z4,z1301,z6])],[(0,[z152,z1,z269,z3,z5,z6]),(0,[z0,z1,z3,z4,z1302,z6]),(0,[z0,z1303,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z440])],[(0,[z0,z1304,z1,z3,z4,z6]),(0,[z0,z1,z1305,z3,z4,z6]),(0,[z0,z79,z255,z3,z4,z6]),(0,[z0,z1306,z9,z3,z4,z6])],[(0,[z0,z1,z118,z3,z4,z6]),(0,[z328,z1,z40,z3,z4,z6]),(0,[z0,z1307,z1,z3,z4,z6]),(0,[z0,z1,z121,z3,z4,z6]),(0,[z0,z1,z1308,z3,z4,z6]),(0,[z0,z1,z3,z124,z4,z85])],[(0,[z24,z127,z106,z3,z4,z6]),(0,[z0,z20,z688,z3,z4,z6])],[(0,[z0,z42,z1,z3,z114,z191]),(0,[z0,z1,z9,z3,z4,z123])],[(0,[z0,z1,z1309,z3,z4,z6]),(0,[z0,z569,z3,z56,z4,z6]),(0,[z0,z77,z9,z3,z4,z245])],[(0,[z0,z1,z1310,z3,z4,z6]),(0,[z743,z1,z9,z3,z4,z6]),(0,[z0,z1311,z1,z3,z4,z6]),(0,[z1312,z0,z1,z3,z4,z6]),(0,[z0,z1,z1313,z3,z4,z6]),(0,[z0,z60,z180,z3,z12,z6]),(0,[z0,z1314,z1,z3,z4,z6]),(0,[z0,z1,z1315,z3,z4,z6])],[(0,[z410,z1,z51,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z1316]),(0,[z0,z1317,z9,z3,z4,z6]),(0,[z0,z1318,z1,z3,z4,z6])],[(0,[z57,z1,z9,z122,z4,z6]),(0,[z0,z1,z1319,z3,z4,z6]),(0,[z0,z1,z3,z4,z1320,z6]),(0,[z8,z0,z20,z10,z4,z6]),(0,[z1321,z1,z9,z3,z4,z6]),(0,[z0,z1,z1322,z3,z4,z6]),(0,[z0,z1,z1323,z3,z4,z6]),(0,[z1,z9,z3,z4,z6,z1324])],[(0,[z0,z1,z1325,z3,z4,z6]),(0,[z0,z1,z1326,z3,z4,z6]),(0,[z675,z1,z9,z3,z5,z6]),(0,[z310,z0,z3,z4,z76,z6]),(0,[z0,z249,z1,z3,z4,z6]),(0,[z0,z132,z9,z3,z4,z6]),(0,[z0,z1327,z1,z3,z4,z6])],[],[(0,[z24,z106,z2,z3,z4,z6]),(0,[z0,z1328,z1,z3,z4,z6]),(0,[z0,z1,z44,z3,z342,z6]),(0,[z0,z1,z9,z117,z298,z6])]],
   [[(0,[z0,z42,z315,z3,z4,z6]),(0,[z0,z1329,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1330])],[(0,[z0,z60,z40,z3,z12,z6])],[(0,[z0,z20,z1,z3,z4,z99]),(0,[z57,z1,z2,z122,z4,z6]),(0,[z0,z20,z3,z4,z6,z438]),(0,[z0,z1,z1331,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1332])],[(0,[z0,z277,z40,z3,z4,z6]),(0,[z0,z1,z1333,z3,z4,z6]),(0,[z0,z132,z2,z3,z4,z6]),(0,[z1334,z0,z9,z3,z4,z6]),(0,[z0,z1335,z1,z3,z4,z6]),(0,[z0,z1,z9,z4,z6,z773])],[(0,[z0,z1,z1336,z3,z4,z6]),(0,[z0,z9,z3,z841,z137,z6]),(0,[z0,z2,z3,z4,z6,z196]),(0,[z31,z1,z9,z3,z4,z245])],[(0,[z62,z1,z51,z3,z4,z6]),(0,[z0,z1,z40,z3,z4,z245]),(0,[z216,z1,z9,z120,z4,z6]),(0,[z0,z1337,z1,z3,z4,z6]),(0,[z19,z0,z9,z3,z4,z403]),(0,[z0,z1,z3,z89,z4,z17]),(0,[z0,z1,z9,z3,z4,z965]),(0,[z0,z1,z3,z4,z1338,z6]),(0,[z31,z1,z9,z3,z4,z440]),(0,[z1339,z1,z9,z3,z4,z6])],[(0,[z0,z146,z9,z3,z4,z6]),(0,[z0,z1340,z9,z3,z4,z6]),(0,[z468,z0,z1,z3,z4,z17]),(0,[z265,z0,z1,z9,z4,z55]),(0,[z38,z188,z0,z3,z4,z6])],[(0,[z0,z1,z9,z1341,z4,z6]),(0,[z618,z1,z40,z3,z4,z6]),(0,[z0,z20,z1,z3,z350,z6]),(0,[z0,z1,z3,z4,z1342,z6]),(0,[z108,z0,z1,z3,z345,z6]),(0,[z1343,z1,z9,z3,z4,z6]),(0,[z1344,z1,z9,z3,z4,z6]),(0,[z0,z1,z2,z3,z578,z6]),(0,[z0,z43,z9,z3,z4,z245]),(0,[z0,z1,z3,z4,z6,z1345])],[(0,[z0,z1,z1346,z3,z4,z6]),(0,[z0,z43,z9,z3,z4,z440]),(0,[z1347,z1,z9,z3,z4,z6])],[(0,[z0,z1,z1348,z3,z4,z6]),(0,[z468,z0,z249,z1,z3,z4])],[(0,[z0,z1,z3,z4,z1349,z6]),(0,[z0,z127,z73,z3,z4,z6]),(0,[z0,z1,z3,z1350,z4,z6]),(0,[z0,z1,z1351,z3,z4,z6]),(1,[z0,z911,z3,z4,z6])],[(0,[z189,z1,z51,z3,z4,z6]),(0,[z152,z42,z1,z3,z5,z6]),(0,[z0,z1,z3,z558,z17,z6]),(0,[z265,z38,z0,z9,z3,z4])],[(0,[z98,z16,z9,z3,z4,z99]),(0,[z0,z1,z9,z3,z1352,z6]),(0,[z0,z1,z1353,z3,z4,z6]),(0,[z288,z1,z9,z3,z907,z6]),(0,[z0,z146,z2,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z245])],[(0,[z0,z1354,z9,z3,z4,z6]),(0,[z1355,z0,z1,z9,z3,z4]),(0,[z0,z126,z20,z3,z4,z6]),(0,[z0,z9,z3,z4,z1356,z6]),(0,[z0,z126,z3,z4,z76,z6]),(0,[z0,z1,z3,z4,z6,z1357])],[(0,[z0,z1,z3,z4,z17,z6]),(0,[z0,z246,z9,z211,z4,z6]),(0,[z0,z1,z1358,z3,z4,z6]),(0,[z0,z81,z1,z3,z4,z6]),(0,[z8,z0,z9,z948,z4,z6])],[(0,[z0,z1,z1359,z3,z4,z6]),(0,[z0,z1360,z1,z3,z4,z6]),(0,[z0,z42,z1,z3,z1030,z6]),(0,[z0,z1361,z1,z3,z4,z6]),(0,[z0,z1362,z1,z3,z4,z6])]],
   [[(0,[z0,z20,z1,z3,z4,z6]),(0,[z0,z1363,z1,z3,z4,z6])],[(0,[z36,z0,z3,z4,z196,z37])],[(0,[z0,z1364,z9,z3,z4,z6]),(0,[z0,z1,z3,z1365,z4,z6])],[(0,[z0,z1,z44,z3,z326,z6]),(0,[z59,z1,z2,z3,z4,z159]),(0,[z0,z121,z3,z4,z76,z6]),(0,[z0,z1,z3,z4,z1366,z6])],[(0,[z0,z1,z9,z3,z380,z434]),(0,[z0,z1,z1367,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1368])],[(0,[z0,z1,z3,z5,z342,z6]),(0,[z0,z1,z3,z162,z4,z6]),(0,[z0,z175,z9,z3,z4,z6]),(0,[z265,z417,z1,z9,z4,z55]),(0,[z0,z1,z9,z3,z167,z191])],[(0,[z0,z1369,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z873,z6]),(0,[z1189,z0,z1,z3,z4,z6]),(0,[z0,z1,z65,z303,z4,z6]),(0,[z0,z1,z3,z4,z6,z1370])],[(0,[z0,z42,z81,z3,z4,z6])],[(0,[z0,z1,z9,z3,z350,z129]),(0,[z8,z468,z0,z9,z3,z4]),(0,[z0,z1,z82,z4,z17,z72]),(0,[z406,z1,z9,z3,z4,z55])],[(0,[z0,z1,z1371,z3,z4,z6]),(0,[z0,z1,z1372,z3,z4,z6]),(0,[z406,z1,z9,z3,z4,z72])],[(0,[z98,z736,z9,z3,z4,z6]),(0,[z288,z1,z40,z3,z18,z6]),(0,[z0,z20,z34,z3,z4,z6]),(0,[z0,z1,z9,z201,z4,z239]),(0,[z0,z1,z9,z3,z4,z1373])],[(0,[z0,z1,z1374,z3,z4,z6]),(0,[z19,z0,z9,z3,z4,z428]),(0,[z62,z221,z1,z3,z4,z6]),(0,[z0,z1375,z9,z3,z4,z6]),(0,[z0,z1376,z9,z3,z4,z6]),(0,[z0,z175,z2,z3,z4,z6]),(0,[z0,z1377,z9,z3,z4,z6])],[(0,[z0,z569,z40,z3,z4,z6]),(1,[z1,z9,z120,z350,z6]),(0,[z0,z1,z9,z3,z1378,z6]),(0,[z152,z221,z1,z3,z4,z6]),(0,[z0,z42,z219,z3,z4,z6]),(0,[z468,z0,z9,z3,z4,z137]),(0,[z0,z60,z9,z3,z12,z123]),(0,[z0,z1379,z9,z3,z4,z6])],[(1,[z0,z1,z3,z1095,z6]),(0,[z0,z246,z51,z3,z4,z6]),(0,[z0,z246,z9,z3,z4,z239]),(0,[z0,z146,z151,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1380]),(0,[z0,z1,z1381,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1382]),(0,[z0,z1,z1383,z3,z4,z6]),(0,[z0,z42,z3,z545,z4,z6]),(0,[z0,z3,z4,z962,z17,z6]),(0,[z0,z1,z104,z3,z4,z440])],[(0,[z0,z1384,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z1385,z3,z4,z6]),(0,[z427,z221,z1,z3,z4,z6]),(0,[z310,z0,z3,z10,z4,z6])],[(0,[z27,z0,z1,z3,z863,z6]),(0,[z0,z1,z9,z3,z4,z129]),(0,[z0,z1,z3,z4,z6,z1239]),(0,[z0,z9,z948,z10,z4,z6]),(0,[z265,z0,z9,z4,z438,z55]),(0,[z101,z0,z331,z9,z3,z84])],[(0,[z0,z1,z40,z3,z4,z390]),(0,[z0,z42,z911,z3,z4,z6])],[(0,[z0,z1386,z1,z3,z4,z6]),(0,[z409,z70,z1,z3,z4,z6]),(0,[z0,z175,z138,z3,z4,z6])],[(0,[z0,z1,z193,z3,z4,z6]),(0,[z0,z1387,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z105,z6])],[(0,[z0,z1,z1388,z3,z4,z6]),(0,[z0,z42,z569,z3,z4,z6]),(0,[z468,z0,z1,z2,z3,z4]),(0,[z31,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z3,z508,z17,z6]),(0,[z0,z1,z3,z4,z1389,z6]),(0,[z0,z402,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z129]),(1,[z1,z9,z1064,z4,z6]),(0,[z335,z1,z9,z3,z4,z159]),(0,[z0,z1,z3,z4,z1390,z6]),(0,[z310,z0,z1,z3,z4,z6]),(0,[z19,z0,z9,z3,z376,z4]),(0,[z0,z1391,z9,z3,z4,z6]),(0,[z30,z0,z77,z9,z131,z6])],[(0,[z0,z1392,z1,z3,z4,z6]),(0,[z0,z1,z1393,z3,z4,z6]),(0,[z0,z43,z2,z3,z4,z6])],[(0,[z27,z0,z3,z4,z76,z6]),(0,[z309,z0,z1,z3,z100,z6]),(0,[z406,z1,z40,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z390]),(0,[z0,z1394,z9,z3,z4,z6]),(0,[z8,z0,z9,z89,z10,z4]),(0,[z0,z1,z767,z56,z4,z6]),(0,[z0,z1,z1395,z3,z4,z6]),(0,[z0,z840,z175,z3,z4,z6])],[(0,[z0,z1,z9,z3,z1396,z6]),(0,[z0,z1,z1397,z3,z4,z6]),(0,[z0,z1,z153,z3,z4,z239])],[(0,[z0,z1,z1398,z3,z350,z6]),(0,[z0,z42,z1,z3,z4,z434]),(0,[z288,z1,z91,z3,z18,z6]),(0,[z661,z0,z1,z3,z17,z6]),(0,[z270,z0,z1,z53,z4,z6]),(0,[z0,z1,z3,z185,z89,z4]),(0,[z0,z1,z1399,z3,z4,z6])],[(0,[z0,z1,z9,z211,z4,z6]),(0,[z0,z920,z246,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z99]),(0,[z0,z73,z9,z87,z4,z6]),(0,[z0,z1,z208,z3,z4,z6]),(0,[z0,z1386,z34,z3,z4,z6]),(0,[z0,z34,z9,z3,z350,z6]),(0,[z0,z20,z79,z3,z4,z6]),(0,[z0,z60,z3,z12,z13,z6]),(0,[z0,z1,z9,z3,z856,z6])],[(1,[z736,z9,z3,z4,z6]),(0,[z0,z1,z1400,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1401]),(0,[z1402,z0,z1,z3,z4,z6]),(0,[z0,z1,z40,z3,z1095,z6]),(0,[z0,z21,z73,z3,z4,z6]),(0,[z1274,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1403,z3,z4,z6]),(0,[z0,z1404,z1,z3,z4,z6]),(0,[z1084,z42,z1,z3,z4,z6]),(0,[z265,z0,z42,z1,z4,z55]),(0,[z0,z1,z3,z4,z1405,z6])]],
   [[(0,[z0,z1,z3,z1406,z4,z6]),(0,[z282,z0,z1,z3,z4,z291]),(0,[z0,z1,z9,z3,z4,z1407]),(0,[z1,z447,z3,z4,z6,z159]),(0,[z0,z1,z3,z4,z1408,z6]),(0,[z0,z126,z3,z10,z4,z6]),(0,[z0,z879,z77,z3,z4,z6])],[(0,[z0,z1,z1409,z3,z4,z6]),(0,[z33,z1,z120,z4,z17,z6]),(0,[z1410,z0,z1,z9,z3,z4]),(0,[z0,z42,z568,z3,z4,z6]),(0,[z0,z1,z1411,z3,z4,z6]),(0,[z0,z1,z1412,z3,z4,z6]),(0,[z0,z1413,z1,z3,z4,z6]),(0,[z19,z0,z126,z3,z4,z6])],[(0,[z0,z1,z1414,z3,z4,z6]),(0,[z0,z1,z51,z3,z350,z6]),(0,[z0,z315,z153,z3,z4,z6]),(0,[z0,z1,z2,z211,z4,z6]),(0,[z0,z20,z1,z201,z4,z6]),(0,[z0,z1,z3,z4,z1415,z6])],[(0,[z0,z42,z302,z3,z4,z6]),(0,[z0,z1,z9,z3,z819,z6]),(0,[z36,z0,z1,z3,z4,z403]),(0,[z0,z1,z1416,z3,z4,z6])],[(0,[z417,z1,z40,z3,z4,z6]),(0,[z0,z1,z1398,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1417]),(0,[z103,z77,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1418,z6]),(0,[z0,z1419,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z1095,z6]),(0,[z0,z42,z3,z638,z4,z6]),(0,[z19,z406,z1,z9,z3,z4]),(0,[z0,z65,z94,z371,z4,z6])],[(0,[z0,z34,z9,z3,z4,z6]),(0,[z0,z1,z1420,z3,z4,z6]),(0,[z0,z1421,z1,z3,z4,z6]),(0,[z0,z1422,z1,z3,z4,z6]),(0,[z0,z121,z3,z10,z4,z6]),(0,[z0,z1,z3,z4,z6,z1423]),(0,[z0,z1,z3,z4,z17,z245])],[(0,[z0,z1,z44,z3,z4,z6]),(0,[z0,z1,z40,z3,z380,z6]),(0,[z0,z1,z9,z1424,z4,z6]),(0,[z0,z1,z3,z4,z1425,z6]),(0,[z0,z126,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1426,z6]),(0,[z0,z20,z1,z3,z4,z245]),(0,[z0,z1,z104,z3,z4,z6]),(0,[z0,z1,z2,z82,z4,z72])],[(0,[z0,z42,z1,z3,z4,z1103]),(0,[z0,z3,z10,z4,z251,z6]),(0,[z0,z20,z1,z3,z4,z440]),(0,[z0,z74,z3,z185,z4,z6])],[(0,[z0,z1,z3,z1427,z4,z6]),(0,[z406,z1,z1292,z3,z4,z6]),(0,[z0,z1,z3,z4,z1428,z6])],[(0,[z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z1429,z6]),(0,[z0,z1,z1430,z3,z4,z6]),(0,[z0,z1,z1431,z3,z4,z6]),(0,[z296,z0,z1,z3,z342,z6]),(0,[z0,z1432,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z239]),(0,[z0,z42,z73,z10,z4,z6]),(0,[z417,z42,z1,z3,z4,z6])],[(0,[z0,z1,z40,z3,z1004,z6]),(0,[z0,z34,z2,z3,z4,z6]),(0,[z0,z79,z9,z3,z350,z6]),(0,[z0,z1,z9,z3,z1433,z4]),(0,[z265,z0,z1,z9,z445,z4]),(0,[z134,z0,z1,z637,z4,z6]),(0,[z0,z569,z65,z3,z4,z6]),(1,[z0,z1,z9,z4,z773])],[(0,[z0,z1,z207,z3,z17,z6]),(0,[z0,z1,z1434,z3,z4,z6])],[(0,[z16,z68,z1,z3,z4,z6]),(0,[z0,z1,z83,z3,z350,z6]),(0,[z0,z42,z1,z3,z380,z6]),(0,[z0,z20,z3,z4,z531,z6])],[(0,[z0,z1,z1435,z3,z4,z6]),(0,[z0,z73,z147,z4,z17,z6]),(0,[z0,z1,z9,z3,z1436,z6]),(0,[z0,z1,z1437,z3,z4,z6])]],
   [[(0,[z0,z16,z1,z3,z1095,z6]),(0,[z0,z60,z9,z3,z679,z6]),(0,[z0,z1,z535,z94,z4,z6]),(0,[z516,z1,z40,z3,z4,z6])],[(0,[z0,z1,z40,z3,z4,z394]),(0,[z0,z1,z2,z3,z4,z239]),(0,[z0,z73,z9,z285,z4,z6]),(0,[z0,z1,z2,z3,z4,z123])],[(0,[z0,z1,z3,z4,z6,z1438]),(0,[z0,z1,z9,z1439,z4,z6]),(0,[z0,z698,z42,z3,z4,z6]),(0,[z0,z1440,z9,z3,z4,z6]),(0,[z0,z1,z9,z4,z72,z773])],[(0,[z0,z315,z9,z3,z4,z6]),(0,[z0,z1,z1441,z3,z4,z6]),(0,[z0,z1442,z146,z3,z4,z6]),(0,[z0,z1443,z146,z3,z4,z6]),(0,[z0,z20,z3,z4,z6,z540]),(0,[z0,z1,z3,z1444,z4,z6]),(0,[z743,z1,z2,z3,z4,z6])],[(0,[z98,z16,z15,z3,z4,z6]),(0,[z98,z16,z206,z3,z4,z6]),(0,[z0,z1445,z9,z3,z4,z6]),(0,[z59,z1,z557,z3,z4,z159]),(0,[z0,z1,z3,z4,z1446,z6])],[(0,[z0,z79,z9,z3,z4,z6]),(0,[z388,z1,z51,z3,z4,z6]),(0,[z0,z1,z1447,z3,z4,z6]),(0,[z0,z1,z3,z1448,z4,z6]),(0,[z1449,z0,z1,z3,z4,z6])],[(0,[z344,z1,z9,z3,z5,z6]),(0,[z0,z73,z147,z162,z4,z6]),(0,[z0,z565,z73,z3,z4,z6]),(0,[z0,z1,z3,z1450,z4,z6])],[(0,[z0,z1,z83,z3,z4,z6]),(0,[z152,z1,z40,z3,z5,z6]),(0,[z33,z1,z447,z3,z4,z6]),(0,[z0,z1451,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1452]),(0,[z103,z42,z1,z3,z4,z6]),(0,[z0,z569,z20,z3,z4,z6]),(0,[z108,z0,z9,z3,z137,z6])],[(0,[z0,z42,z1,z3,z4,z394]),(0,[z98,z1,z447,z3,z4,z6]),(0,[z468,z0,z16,z9,z3,z4]),(0,[z0,z1,z1453,z3,z4,z6]),(0,[z0,z1057,z9,z3,z4,z6]),(0,[z0,z1318,z132,z3,z4,z6])],[(0,[z845,z0,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z1454,z6]),(0,[z406,z132,z9,z3,z4,z6])],[(0,[z33,z1,z9,z120,z350,z6]),(0,[z0,z42,z3,z4,z6,z591]),(0,[z468,z0,z1,z3,z185,z4]),(0,[z0,z1,z3,z4,z1455,z6]),(0,[z0,z1,z3,z4,z267,z6])],[(0,[z1456,z0,z1,z9,z3,z6]),(0,[z0,z1,z9,z1457,z4,z6]),(0,[z0,z1,z1458,z3,z4,z6]),(0,[z0,z1459,z9,z3,z4,z6]),(0,[z1,z1460,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1095,z6]),(0,[z27,z0,z3,z10,z4,z6]),(0,[z1461,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1462,z6]),(0,[z0,z9,z3,z4,z6,z1463]),(0,[z0,z42,z362,z3,z4,z6]),(0,[z19,z0,z42,z3,z4,z611]),(0,[z0,z42,z7,z3,z4,z6]),(0,[z0,z1,z2,z3,z664,z6]),(0,[z598,z0,z9,z3,z137,z6]),(0,[z0,z1,z65,z94,z4,z6]),(0,[z0,z1,z3,z767,z4,z6]),(1,[z31,z1,z9,z131,z6])],[(0,[z0,z1,z3,z485,z17,z6]),(0,[z288,z20,z1,z3,z18,z6]),(0,[z0,z20,z299,z3,z4,z6]),(0,[z0,z1464,z1,z3,z4,z6]),(0,[z0,z1,z102,z3,z4,z6]),(0,[z0,z569,z3,z4,z17,z6])],[(0,[z0,z1465,z9,z3,z4,z6]),(0,[z0,z362,z1,z259,z4,z6]),(0,[z0,z1,z3,z4,z1466,z6])],[(0,[z0,z9,z3,z4,z6,z1075]),(0,[z0,z1467,z9,z3,z4,z6]),(0,[z0,z1,z1468,z3,z4,z6]),(0,[z0,z1,z3,z4,z1469,z6])]],
   [[(0,[z0,z1,z3,z4,z6,z1470]),(0,[z1344,z1,z2,z3,z4,z6]),(0,[z0,z1471,z9,z3,z4,z6])],[(0,[z0,z1,z3,z490,z17,z6]),(0,[z1,z1460,z2,z3,z4,z6]),(0,[z0,z1146,z331,z3,z4,z6])],[(0,[z0,z9,z3,z371,z4,z6]),(0,[z0,z1,z3,z381,z17,z6]),(0,[z0,z1,z1472,z3,z4,z6])],[(0,[z27,z0,z1,z3,z4,z6]),(1,[z0,z741,z3,z4,z6]),(0,[z33,z1,z9,z120,z4,z6]),(0,[z0,z1473,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z390]),(0,[z19,z0,z42,z3,z4,z41]),(0,[z0,z1,z3,z4,z1474,z6]),(0,[z265,z0,z132,z9,z4,z55])],[(0,[z0,z1,z25,z3,z4,z6]),(0,[z0,z1,z40,z3,z241,z4]),(0,[z1003,z1,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1475]),(0,[z0,z1476,z9,z3,z4,z6]),(0,[z417,z132,z9,z3,z4,z6]),(0,[z1477,z1,z9,z3,z4,z6])],[(0,[z97,z68,z1,z3,z4,z6]),(0,[z33,z1,z9,z1064,z4,z6]),(0,[z0,z1,z1478,z3,z4,z6])],[(0,[z0,z1042,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1479]),(0,[z0,z1,z1480,z3,z4,z6]),(0,[z469,z0,z1,z56,z4,z6]),(0,[z0,z3,z4,z17,z6,z196]),(0,[z0,z1,z9,z3,z131,z440])],[(0,[z0,z1,z9,z3,z4,z1481]),(0,[z1,z9,z3,z18,z907,z6]),(0,[z0,z9,z147,z948,z4,z6]),(0,[z0,z1,z3,z1482,z4,z6]),(0,[z0,z402,z3,z4,z17,z6])],[(0,[z33,z1,z2,z120,z4,z6]),(0,[z633,z1,z9,z3,z4,z159]),(0,[z1483,z1,z9,z3,z4,z6]),(0,[z0,z1,z9,z117,z190,z6])],[(0,[z0,z1,z40,z3,z1061,z6]),(0,[z0,z1484,z9,z3,z4,z6]),(0,[z353,z0,z42,z3,z4,z6]),(0,[z1170,z42,z1,z3,z4,z6]),(0,[z0,z1,z1485,z3,z4,z6]),(0,[z406,z1,z3,z4,z17,z6])],[(0,[z0,z1,z9,z3,z4,z1486]),(0,[z0,z1,z9,z3,z1487,z6]),(0,[z0,z42,z1,z3,z241,z4]),(0,[z0,z60,z3,z12,z17,z6])],[(0,[z406,z20,z1,z3,z4,z6]),(0,[z0,z1,z3,z1488,z4,z6]),(0,[z0,z1,z817,z3,z300,z6])],[(0,[z98,z16,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1489]),(0,[z0,z1,z51,z201,z4,z6]),(0,[z0,z9,z3,z4,z6,z1091]),(0,[z0,z20,z132,z3,z4,z6]),(0,[z0,z1,z1490,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1491]),(0,[z0,z1,z1492,z3,z4,z6])],[(0,[z0,z1,z9,z3,z4,z1493]),(0,[z0,z66,z343,z3,z4,z6]),(0,[z0,z42,z1,z3,z89,z4]),(0,[z0,z175,z86,z3,z4,z6])],[(0,[z62,z1,z447,z3,z4,z6]),(0,[z0,z60,z51,z3,z12,z6]),(0,[z0,z73,z40,z147,z4,z6]),(0,[z0,z1494,z1,z3,z4,z6])]],
   [[(0,[z0,z42,z472,z3,z4,z6]),(0,[z0,z1,z3,z4,z1495,z6]),(0,[z0,z1,z104,z3,z4,z245])],[(0,[z0,z277,z51,z3,z4,z6]),(0,[z0,z1,z3,z12,z342,z6]),(0,[z1,z9,z3,z120,z4,z129]),(0,[z0,z1,z9,z3,z1496,z4]),(0,[z0,z1,z9,z3,z1497,z6]),(0,[z1498,z0,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z100,z6]),(0,[z0,z1,z3,z4,z1499,z6]),(0,[z0,z1,z3,z1500,z4,z6])],[(0,[z0,z299,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1501]),(0,[z98,z16,z2,z3,z4,z6]),(0,[z0,z1502,z1,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z245]),(0,[z0,z1,z9,z3,z4,z1503]),(0,[z0,z1,z9,z3,z300,z6])],[(0,[z0,z1,z51,z3,z4,z440]),(0,[z620,z1,z9,z3,z4,z159]),(0,[z0,z1504,z9,z3,z4,z6])],[(0,[z400,z1,z40,z3,z4,z6]),(0,[z0,z315,z9,z201,z4,z6]),(0,[z0,z1442,z1,z3,z4,z6]),(0,[z0,z1443,z1,z3,z4,z6]),(0,[z417,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z105,z1301,z6])],[(0,[z0,z1,z9,z3,z1505,z6])],[(0,[z0,z1,z40,z3,z4,z434]),(0,[z178,z0,z42,z3,z4,z6]),(0,[z0,z20,z1,z3,z114,z191]),(0,[z0,z1506,z9,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1507]),(0,[z0,z1,z3,z4,z1508,z6]),(0,[z0,z1,z1509,z3,z4,z6]),(0,[z0,z1,z1510,z3,z4,z6]),(0,[z0,z1,z1511,z3,z4,z6]),(0,[z31,z1,z9,z4,z131,z6]),(0,[z0,z3,z4,z6,z438,z1332]),(0,[z0,z1,z1512,z3,z4,z6])],[(0,[z0,z299,z2,z3,z4,z6]),(0,[z0,z9,z3,z4,z841,z6]),(0,[z0,z1,z2,z3,z300,z6]),(0,[z0,z1,z9,z3,z4,z773])],[(0,[z24,z42,z106,z3,z4,z6]),(0,[z1,z40,z51,z3,z4,z6]),(0,[z0,z261,z3,z4,z76,z6]),(0,[z0,z261,z20,z3,z4,z6]),(0,[z0,z1513,z1,z3,z4,z6]),(0,[z0,z221,z3,z4,z76,z6]),(0,[z460,z0,z9,z10,z4,z6])],[(0,[z0,z1514,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z1515,z6])],[(0,[z24,z68,z1,z3,z4,z6]),(0,[z70,z68,z1,z3,z4,z6]),(0,[z19,z0,z9,z3,z4,z22]),(0,[z388,z1,z3,z4,z100,z6]),(0,[z0,z1,z874,z3,z4,z6])],[(0,[z221,z1,z3,z18,z4,z6]),(0,[z19,z0,z3,z4,z251,z6]),(0,[z0,z1,z2,z3,z105,z6])],[(0,[z0,z1360,z315,z3,z4,z6]),(0,[z0,z1516,z1,z3,z4,z6])],[(0,[z0,z20,z315,z3,z4,z6]),(0,[z0,z1,z9,z3,z1517,z6]),(0,[z0,z1,z3,z251,z6,z191]),(0,[z0,z1,z318,z3,z4,z6])]],
   [[(0,[z0,z1518,z1,z3,z4,z6]),(0,[z1519,z0,z1,z3,z4,z6]),(0,[z0,z1520,z1,z3,z4,z6]),(0,[z0,z1,z911,z3,z4,z6]),(0,[z38,z0,z20,z3,z4,z6]),(0,[z406,z1,z9,z3,z105,z6]),(0,[z0,z1521,z1,z3,z4,z6])],[(0,[z265,z0,z1,z40,z4,z55]),(0,[z0,z1,z9,z211,z4,z390]),(0,[z0,z1522,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z695,z6]),(0,[z0,z1010,z3,z4,z17,z6])],[(0,[z0,z1,z3,z4,z17,z394]),(0,[z98,z70,z16,z3,z4,z6]),(0,[z8,z0,z51,z10,z4,z6]),(0,[z0,z3,z4,z962,z100,z6]),(0,[z0,z1,z3,z4,z6,z320]),(0,[z0,z277,z65,z94,z4,z6]),(0,[z0,z1001,z77,z3,z4,z6]),(0,[z0,z1523,z1,z3,z4,z6])],[(0,[z0,z1,z9,z3,z1524,z4])],[(0,[z0,z1,z1525,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1526]),(0,[z0,z1,z1527,z3,z4,z6]),(0,[z0,z1528,z9,z3,z4,z6])],[(0,[z0,z1529,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z439,z191]),(0,[z0,z1,z1530,z3,z4,z6])],[(0,[z268,z0,z1,z179,z4,z6]),(0,[z0,z1,z1531,z3,z4,z6]),(0,[z0,z1,z1532,z3,z4,z6]),(0,[z0,z729,z402,z3,z4,z6])],[(0,[z1533,z0,z1,z3,z4,z6]),(0,[z0,z66,z74,z3,z4,z6]),(0,[z0,z1534,z1,z3,z4,z6]),(0,[z0,z1535,z9,z3,z4,z6]),(0,[z0,z1,z9,z3,z349,z191])],[(0,[z0,z1,z9,z3,z1536,z6]),(0,[z288,z1,z51,z3,z18,z6]),(0,[z0,z1,z1537,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1538]),(0,[z0,z73,z121,z147,z4,z6]),(0,[z1539,z1,z9,z3,z4,z6]),(0,[z563,z0,z1,z9,z4,z55])],[(0,[z0,z16,z66,z3,z4,z6]),(0,[z38,z0,z9,z3,z4,z41]),(0,[z8,z0,z42,z10,z4,z6]),(0,[z0,z1,z9,z3,z1540,z6]),(0,[z134,z0,z1,z130,z4,z6])],[(0,[z407,z0,z9,z3,z137,z6]),(0,[z189,z16,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z1541,z6]),(0,[z0,z569,z51,z3,z4,z6]),(0,[z1,z9,z1064,z120,z4,z6]),(0,[z152,z20,z1,z3,z5,z6]),(0,[z0,z1,z9,z422,z190,z6]),(0,[z0,z299,z151,z3,z4,z6])],[(0,[z0,z1,z9,z3,z380,z129]),(0,[z0,z1,z9,z3,z306,z191])],[(0,[z0,z146,z212,z3,z4,z6]),(0,[z498,z0,z1,z236,z4,z6])],[(0,[z0,z1,z9,z3,z1542,z4]),(0,[z14,z1,z51,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1543]),(0,[z0,z42,z73,z3,z4,z6]),(0,[z0,z331,z9,z3,z4,z6]),(0,[z31,z77,z9,z3,z4,z6])],[(0,[z0,z77,z40,z3,z4,z6]),(0,[z288,z0,z1,z3,z251,z6]),(0,[z59,z42,z1,z3,z4,z159]),(0,[z19,z0,z42,z3,z4,z76]),(0,[z30,z0,z1,z2,z131,z6])],[(0,[z152,z1,z3,z5,z100,z6]),(0,[z0,z1544,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z900,z6])]],
   [[(0,[z0,z1,z51,z3,z4,z390]),(0,[z468,z0,z1,z51,z3,z4]),(0,[z0,z1,z1545,z3,z4,z6]),(0,[z0,z1,z3,z105,z17,z6])],[(0,[z0,z1,z1546,z3,z4,z6])],[(0,[z1,z713,z9,z3,z4,z6]),(0,[z0,z1547,z1,z3,z4,z6]),(0,[z417,z1,z1399,z3,z4,z6]),(0,[z38,z0,z3,z4,z6,z174])],[(0,[z0,z391,z1,z3,z4,z6]),(0,[z1548,z0,z1,z3,z4,z6]),(0,[z103,z1,z40,z3,z4,z6]),(0,[z0,z1,z3,z4,z1549,z6]),(0,[z0,z1,z1550,z3,z4,z6]),(0,[z0,z1,z3,z551,z17,z6]),(0,[z0,z1,z940,z3,z4,z6])],[(0,[z0,z1,z9,z1551,z4,z6]),(0,[z0,z1,z1552,z3,z4,z6]),(0,[z0,z1,z923,z3,z4,z6]),(0,[z426,z1,z9,z3,z18,z6]),(0,[z36,z0,z1,z3,z4,z37])],[(0,[z0,z402,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z1553,z6]),(0,[z103,z43,z9,z3,z4,z6])],[(0,[z0,z1554,z9,z3,z4,z6]),(0,[z0,z1,z269,z211,z4,z6]),(0,[z19,z0,z9,z691,z3,z4]),(0,[z0,z1,z1555,z3,z4,z6]),(0,[z0,z1,z1556,z3,z4,z6]),(0,[z0,z1,z1557,z3,z4,z6]),(0,[z0,z1,z622,z303,z4,z6]),(0,[z0,z778,z43,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z1558])],[(0,[z98,z0,z126,z3,z4,z6]),(0,[z406,z1,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z1559,z6])],[(0,[z68,z1,z51,z3,z4,z6]),(0,[z38,z0,z40,z3,z4,z6]),(0,[z0,z1560,z1,z3,z4,z6]),(0,[z283,z0,z1,z3,z345,z6])],[(0,[z1561,z0,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z4,z1562]),(0,[z19,z0,z21,z3,z4,z6]),(0,[z0,z202,z3,z4,z140,z6])],[(0,[z96,z1,z40,z3,z4,z6]),(0,[z1,z9,z3,z393,z4,z159])],[(0,[z0,z1,z1563,z3,z4,z6]),(0,[z0,z1,z1564,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z438]),(0,[z0,z1440,z2,z3,z4,z6]),(0,[z0,z331,z138,z3,z4,z6])],[(0,[z0,z315,z2,z3,z4,z6]),(0,[z0,z1,z65,z555,z4,z6]),(0,[z1,z9,z3,z1565,z4,z6])],[(0,[z0,z261,z3,z10,z4,z6]),(0,[z0,z40,z3,z1184,z4,z6]),(0,[z0,z1,z1566,z3,z4,z6]),(0,[z0,z221,z3,z10,z4,z6])],[(0,[z0,z1,z3,z4,z1567,z6]),(0,[z0,z79,z2,z3,z4,z6]),(1,[z0,z9,z3,z841,z6])],[(0,[z0,z1,z1568,z3,z4,z6]),(0,[z97,z1,z40,z3,z4,z6]),(0,[z0,z1,z1569,z3,z4,z6]),(0,[z0,z1,z259,z56,z4,z6]),(0,[z0,z1,z1570,z3,z4,z6])]],
   [[(0,[z0,z34,z9,z3,z380,z6]),(0,[z0,z1,z9,z415,z4,z72]),(0,[z31,z42,z1,z3,z4,z6]),(0,[z108,z0,z2,z3,z137,z6]),(0,[z0,z1,z180,z3,z241,z4])],[(0,[z0,z1,z1571,z3,z4,z6]),(0,[z0,z1,z207,z3,z100,z6]),(0,[z354,z0,z1,z3,z4,z526]),(0,[z0,z20,z911,z3,z4,z6]),(0,[z460,z19,z0,z9,z3,z4]),(0,[z0,z9,z3,z1572,z4,z6])],[(0,[z0,z1,z51,z3,z114,z191]),(0,[z0,z1,z3,z4,z1573,z6]),(0,[z30,z0,z1,z3,z342,z6]),(1,[z1,z9,z211,z5,z6]),(0,[z0,z1,z3,z4,z1574,z6]),(0,[z414,z0,z1,z3,z4,z154])],[(0,[z484,z1,z51,z3,z4,z6]),(0,[z0,z1575,z1,z3,z4,z6]),(0,[z992,z1,z9,z3,z4,z6])],[(0,[z0,z261,z1,z3,z4,z6]),(0,[z0,z261,z106,z3,z4,z6]),(0,[z0,z221,z1,z3,z4,z6]),(0,[z0,z1576,z1,z3,z4,z6]),(0,[z0,z1,z255,z3,z350,z6]),(0,[z0,z1,z9,z1577,z4,z6]),(0,[z0,z1578,z1,z3,z4,z6])],[(0,[z0,z1,z447,z3,z4,z6]),(0,[z0,z1,z535,z150,z4,z6]),(0,[z0,z1,z9,z1579,z4,z6]),(0,[z0,z1,z269,z3,z4,z239]),(0,[z265,z19,z0,z42,z3,z4]),(0,[z468,z0,z20,z1,z3,z4]),(0,[z1580,z1,z9,z3,z4,z6]),(0,[z257,z0,z1,z4,z228,z6])],[(0,[z152,z1,z9,z211,z5,z6]),(0,[z0,z1581,z1,z3,z4,z6]),(0,[z0,z1,z9,z3,z1582,z4]),(0,[z0,z1583,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1584,z6]),(0,[z0,z1585,z1,z3,z4,z6])],[(0,[z0,z1,z9,z120,z350,z6]),(0,[z0,z1,z3,z4,z17,z434]),(0,[z0,z20,z1,z3,z4,z390]),(0,[z0,z1,z3,z574,z17,z6])],[(0,[z0,z1,z9,z3,z1586,z6]),(0,[z810,z1,z9,z3,z4,z6]),(0,[z0,z1,z1587,z3,z4,z6])],[(0,[z0,z1,z1588,z3,z4,z6]),(0,[z0,z1,z1589,z3,z4,z6]),(0,[z0,z1,z40,z3,z89,z4]),(0,[z0,z20,z1,z3,z4,z434]),(0,[z0,z1590,z9,z3,z4,z6]),(0,[z0,z1,z1591,z3,z4,z6])],[(0,[z0,z1592,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1593,z6]),(0,[z0,z42,z331,z3,z4,z6]),(0,[z1594,z0,z1,z3,z4,z6]),(0,[z0,z1,z1595,z3,z4,z6])],[(0,[z0,z1,z1596,z3,z4,z6]),(0,[z0,z1,z40,z82,z4,z72]),(1,[z1,z9,z3,z907,z6]),(0,[z0,z1,z3,z4,z1597,z6]),(0,[z0,z1,z3,z4,z1598,z6]),(0,[z872,z38,z0,z3,z4,z6])],[(0,[z0,z1,z255,z3,z4,z6]),(0,[z57,z1,z9,z667,z4,z6]),(0,[z0,z42,z3,z93,z4,z6]),(0,[z310,z0,z81,z3,z4,z6]),(0,[z0,z3,z4,z76,z6,z1239]),(0,[z1003,z1,z2,z3,z4,z6]),(0,[z0,z1,z1599,z3,z4,z6])],[(0,[z0,z1576,z34,z3,z4,z6]),(0,[z0,z1,z1600,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z791])],[(0,[z27,z221,z1,z3,z4,z6]),(0,[z0,z1,z65,z359,z4,z6]),(0,[z0,z1,z1601,z3,z4,z6]),(0,[z589,z1,z9,z120,z4,z6]),(0,[z0,z1602,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z1603,z6]),(0,[z101,z0,z175,z9,z3,z84]),(0,[z1604,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z1605,z3,z4,z6]),(0,[z152,z1,z9,z3,z907,z6])],[(0,[z0,z1,z3,z4,z6,z1606]),(0,[z0,z1,z1607,z3,z4,z6]),(0,[z152,z1,z44,z3,z5,z6]),(1,[z0,z1,z9,z3,z856]),(0,[z0,z1172,z331,z3,z4,z6])],[(0,[z0,z1016,z51,z3,z4,z6]),(0,[z0,z1,z9,z1021,z4,z6]),(0,[z0,z1,z94,z4,z374,z6]),(0,[z0,z1,z3,z300,z17,z6]),(0,[z0,z1,z2,z117,z190,z6]),(0,[z30,z0,z1,z9,z815,z6]),(0,[z0,z1,z3,z4,z6,z1608])],[(0,[z0,z1,z9,z1064,z4,z6]),(0,[z0,z42,z1,z82,z4,z72]),(0,[z0,z60,z9,z3,z841,z6]),(0,[z0,z1,z3,z4,z6,z942])],[(0,[z27,z0,z1,z3,z1095,z6]),(0,[z0,z1,z3,z4,z6,z1609])],[(0,[z152,z1,z51,z3,z5,z6]),(0,[z0,z1,z40,z3,z4,z123]),(0,[z0,z1,z3,z4,z6,z1610]),(0,[z0,z1,z1611,z3,z4,z6]),(0,[z0,z1,z3,z350,z753,z6]),(0,[z152,z1,z9,z3,z5,z239]),(0,[z0,z1,z3,z1612,z4,z6])],[(0,[z24,z106,z40,z3,z4,z6]),(0,[z468,z0,z106,z9,z3,z4]),(0,[z0,z1,z3,z18,z342,z6]),(0,[z468,z0,z1,z9,z3,z4]),(0,[z0,z1,z3,z4,z6,z1613]),(0,[z0,z3,z990,z4,z17,z6])],[(0,[z0,z1614,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1615,z6]),(0,[z0,z1,z2,z3,z142,z6])],[(0,[z0,z1,z9,z3,z1616,z6]),(0,[z0,z1,z3,z345,z17,z6]),(0,[z0,z1,z1617,z3,z4,z6])],[(0,[z0,z20,z274,z3,z4,z6]),(0,[z57,z1,z40,z122,z4,z6]),(0,[z1618,z0,z1,z3,z4,z6]),(0,[z19,z0,z42,z3,z84,z4]),(0,[z0,z132,z312,z3,z4,z6])],[(0,[z0,z736,z9,z3,z4,z6]),(0,[z0,z42,z107,z3,z4,z6]),(0,[z0,z132,z40,z3,z4,z6]),(0,[z417,z20,z1,z3,z4,z6]),(0,[z0,z1,z1619,z3,z4,z6]),(0,[z1498,z0,z2,z3,z4,z6])],[(0,[z0,z40,z3,z4,z6,z196]),(0,[z0,z1,z3,z4,z1620,z6]),(0,[z59,z1,z9,z3,z4,z866]),(0,[z30,z0,z20,z1,z131,z6]),(0,[z1621,z1,z9,z3,z4,z6]),(0,[z743,z60,z1,z3,z4,z6]),(0,[z0,z1,z3,z17,z6,z619]),(0,[z0,z9,z3,z934,z4,z6]),(0,[z0,z1,z1622,z3,z4,z6])],[(0,[z0,z1,z1623,z3,z4,z6]),(0,[z639,z1,z51,z3,z4,z6]),(0,[z0,z1624,z9,z3,z4,z6]),(0,[z0,z1147,z9,z3,z4,z6]),(0,[z0,z42,z1,z3,z4,z123]),(0,[z0,z1,z336,z3,z4,z440]),(0,[z0,z1,z3,z4,z1625,z6])],[(0,[z0,z20,z1,z3,z380,z6]),(0,[z33,z1,z9,z120,z380,z6]),(0,[z152,z315,z9,z3,z5,z6]),(0,[z468,z0,z75,z9,z3,z4]),(0,[z0,z402,z9,z3,z300,z6])],[(0,[z0,z1,z3,z397,z17,z6]),(0,[z0,z42,z246,z3,z4,z6]),(0,[z743,z42,z1,z3,z4,z6])],[(1,[z1,z713,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1626]),(0,[z0,z77,z3,z4,z17,z6]),(0,[z406,z1,z9,z3,z300,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 484) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 484).take 488) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 972).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1457).take 136) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1593)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [484, 488, 485, 136] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 223).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 346).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 443).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 114, 123, 97, 69] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37803

theorem PEqualNP.Outside.L_meta_37803 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4276681384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4276681384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37803.solve