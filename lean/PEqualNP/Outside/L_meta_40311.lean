import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40311

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4272597152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x001023016008a5a8#64 ++ 0x200204602c0114b5#64 ++ 0xb831e703e01fffff#64 ++ 0xd7063ce07c03ffff#64 : BitVec 256),
   (0x0846886cb86592e2#64 ++ 0x4108d10d970cb25c#64 ++ 0xe8ce99fcf8e593e7#64 ++ 0xbd19d33f9f1cb27c#64 : BitVec 256),
   (0x030b1c161b061854#64 ++ 0x80616382c360c30a#64 ++ 0xf70f1e1f1f061c7f#64 ++ 0x7ee1e3c3e3e0c38f#64 : BitVec 256),
   (0x15b01fa00db81f07#64 ++ 0x02b603f401b703e0#64 ++ 0xdff01fe01ff81f86#64 ++ 0xfbfe03fc03ff03f0#64 : BitVec 256),
   (0x06efc00016d74000#64 ++ 0x00ddf80002dae800#64 ++ 0x9fffe0001fffe005#64 ++ 0xf3fffc0003fffc00#64 : BitVec 256),
   (0x27fdf7dbc0000000#64 ++ 0x04ffbefb78000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [7, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xb831e703e01fffff 0xd7063ce07c03ffff

def z1 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf70f1e1f1f061c7f 0x7ee1e3c3e3e0c38f

def z2 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z3 : W := mkw 0x0800086ca82092e2 0x4100010d9504125c 0x600019fce00013e2 0x0c00033f9c00027c

def z4 : W := mkw 0x0846886c98651242 0x4108d10d930ca248 0x40ce18fc18e00000 0x2819c31f831c0000

def z5 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z6 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x0010030000080500 0x00020060000100a0 0x9830070000181f86 0xd30600e0000303f0

def z8 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8ce99fcf8e593e7 0xbd19d33f9f1cb27c

def z9 : W := mkw 0x15b03fa16db8bfaf 0x22b607f42db717f5 0xfff1ffe3ffffffff 0xfffe3ffc7fffffff

def z10 : W := mkw 0x020b001612060050 0x80416002c240c00a 0x200f001f00060079 0x0401e003e000c00f

def z11 : W := mkw 0x14b003a004b80703 0x02960074009700e0 0x08f001e000f80380 0x811e003c001f0070

def z12 : W := mkw 0x27fff7dbd0450000 0x04fffefb7a08a000 0xeffffffff8e58007 0xfdffffffff1cb000

def z13 : W := mkw 0x27edf4dbc0000000 0x04fdbe9b78000000 0x67cff8ffe0000001 0x2cf9ff1ffc000000

def z14 : W := mkw 0x16ffc3a016ff4703 0x02dff87402dfe8e0 0x9fffe1e01fffe385 0xf3fffc3c03fffc70

def z15 : W := mkw 0x24f4e3c9c4d14000 0x049e9c79389a2800 0x08f0e1e0e0f9e000 0x811e1c3c1c1f3c00

def z16 : W := mkw 0x0002000016d74000 0x0000400002dae800 0x000000001fe00000 0x0000000003fc0000

def z17 : W := mkw 0x0eefc068b6f7c2a2 0x41ddf80d16def854 0x9fffe1e0ffffe385 0xf3fffc3c1ffffc70

def z18 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0ce99fce0000003 0xbc19d33f9c000000

def z19 : W := mkw 0x08448068a06182a2 0x4108900d140c3054 0x08c081e0e0e18380 0x8118103c1c1c3070

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0xb001060300061c7f 0x560020c06000c38f

def z21 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8cf9ffff8e79fff 0xff19f3ffff1cf3ff

def z22 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x0830e100e019e380 0x81061c201c033c70

def z23 : W := mkw 0x031b3f177b0ebdfc 0xa06367e2ef61d7bf 0xff3fff1fff1fffff 0xffe7ffe3ffe3ffff

def z24 : W := mkw 0x17ffdfb61fff5f57 0x82fffbf6c3ffebea 0xffffffff1fffffff 0xffffffffe3ffffff

def z25 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0xe0cff9ffe0000003 0xbc19ff3ffc000000

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x9831e000001fe005 0xd3063c000003fc00

def z27 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8fff9fcf8fff3e7 0xff1fff3f9f1ffe7c

def z28 : W := mkw 0x021b2317720ea5f8 0xa0436462ee41d4bf 0xb83fe71fe01fffff 0xd707fce3fc03ffff

def z29 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x88ce800018e58005 0xb119d000031cb000

def z30 : W := mkw 0x0eefc86cbef7d2e2 0x41ddf90d97defa5c 0xfffff9fcfffff3e7 0xffffff3f9ffffe7c

def z31 : W := mkw 0x15b01fa009281f07 0x02b603f4012503e0 0xc7f01fe000001f82 0xf8fe03fc000003f0

def z32 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x0800000018e593e4 0x01000000031cb27c

def z33 : W := mkw 0x15b0178005980d05 0x02b602f000b301a0 0xd7f01fe007180c02 0xfafe03fc00e30180

def z34 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x4ff019e01ff80380 0xa9fe033c03ff0070

def z35 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x20000703e0001ffa 0x040000e07c0003ff

def z36 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x07ce00001fe00000 0x20f9c00003fc0000

def z37 : W := mkw 0x0054a349c0000000 0x000a946938000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z38 : W := mkw 0x0856ab6df86db7ea 0x610ad56dbf0db6fd 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z39 : W := mkw 0x000000002008a5a8 0x20000000040114b5 0x18000000001ffffc 0x030000000003ffff

def z40 : W := mkw 0x37fdfffbc9281f07 0x06ffbfff792503e0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z41 : W := mkw 0x0b0b1c363b679af6 0xc1616386c76cf35e 0xff0f1e1f1fe79fff 0x7fe1e3c3e3fcf3ff

def z42 : W := mkw 0x0010230140000000 0x0002046028000000 0x0030e100e0000000 0x80061c201c000000

def z43 : W := mkw 0x11001ca009201a07 0x0220039401240340 0x400018e000000000 0x0800031c00000000

def z44 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x48ce18fc18e593e4 0x2919c31f831cb27c

def z45 : W := mkw 0x0000001600000050 0x80000002c000000a 0x2000001f00000078 0x04000003e000000f

def z46 : W := mkw 0x27fdffdbc9001804 0x04ffbffb79200300 0xf7ffffffff001c07 0xfeffffffffe00380

def z47 : W := mkw 0x000208041b061854 0x800041008360c30a 0x100000001f061c7c 0x0200000003e0c38f

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001f000004 0x72e0000003e00000

def z49 : W := mkw 0x01001c1609001854 0x80200382c120030a 0x60001e1f00001c7a 0x0c0003c3e000038f

def z50 : W := mkw 0x37fdf7fbc4b80703 0x06ffbeff789700e0 0xefffffffe0f80383 0xfdfffffffc1f0070

def z51 : W := mkw 0x0ce6886cbcf592e2 0x419cd10d979eb25c 0xfffe99fcfffd93e7 0xffffd33f9fffb27c

def z52 : W := mkw 0x15b0178005980d05 0x02b602f000b301a0 0x1730060007180c00 0x42e600c000e30180

def z53 : W := mkw 0x1df69fecbdfd9fe7 0x43bed3fd97bfb3fc 0xfffe9ffcfffd9fe7 0xffffd3ff9fffb3fc

def z54 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x60ce19fcf8e013e2 0x2c19c33f9f1c027c

def z55 : W := mkw 0x08020824386db7ea 0x61004104870db6fd 0x1800000018fffffc 0x03000000031fffff

def z56 : W := mkw 0x224fe05bd2474000 0x0449fc0b7a48e800 0x200fe01fe007e001 0x0401fc03fc00fc00

def z57 : W := mkw 0x0000082008201202 0x0000010401040240 0xc8c019e018e01386 0xb918033c031c0270

def z58 : W := mkw 0x03091c120b021814 0x8061238241604302 0xd7011e031f021c1e 0x7ae023c063e04383

def z59 : W := mkw 0x020b08161a061050 0x80416102c340c20a 0xe00f181f1806107f 0x3c01e303e300c20f

def z60 : W := mkw 0x0000200140000000 0x0000040028000000 0x2001e003e0000001 0x04003c007c000000

def z61 : W := mkw 0x27fff7dfd2060050 0x84fffefbfa40c00a 0xe7ffffffe006007b 0xfcfffffffc00c00f

def z62 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87f0000000000000 0xf0fe000000000000

def z63 : W := mkw 0x00100300200885a0 0x00020060040110b4 0xb8308700e01d9fe7 0xd70610e01c03b3fc

def z64 : W := mkw 0x000208041b061854 0x800041008360c30a 0xb00106031f061c7f 0x560020c063e0c38f

def z65 : W := mkw 0x08000068a02082a2 0x4100000d14041054 0x000001e0e0000380 0x0000003c1c000070

def z66 : W := mkw 0x08448048a04180a0 0x4108900914083014 0x00008000e0018000 0x000010001c003000

def z67 : W := mkw 0x0209400002024000 0x0041280000404800 0x0001600000026000 0x00002c0000004c00

def z68 : W := mkw 0x024fc00012474000 0x0049f8000248e800 0x000fe0000007e001 0x0001fc000000fc00

def z69 : W := mkw 0x17ffdfa01fff5f07 0x02fffbf403ffebe0 0xdfffffe01fffff87 0xfbfffffc03fffff0

def z70 : W := mkw 0x01001c1609001854 0x80200382c120030a 0x4000181c00000000 0x0800030380000000

def z71 : W := mkw 0x0010230140000000 0x0002046028000000 0x0031660300000000 0x40062cc060000000

def z72 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x600e99fce00593e3 0x0c01d33f9c00b27c

def z73 : W := mkw 0x05f497c880000000 0x00be92f910000000 0xe7fe9ffce0000003 0xfcffd3ff9c000000

def z74 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x48ce99fcf8e18380 0xa919d33f9f1c3070

def z75 : W := mkw 0x06edc04880000000 0x00ddb80910000000 0xe7fff9fce0000003 0xfcffff3f9c000000

def z76 : W := mkw 0x2154b7dbc0000000 0x042a96fb78000000 0xe0ce9fffe0000003 0xbc19d3fffc000000

def z77 : W := mkw 0x0010230140000000 0x0002046028000000 0xb831e703e01fe007 0xd7063ce07c03fc00

def z78 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff1ffe01fffff87 0xfbfe3ffc03fffff0

def z79 : W := mkw 0x00000000200080a0 0x0000000004001014 0xa8008100e00593e7 0x950010201c00b27c

def z80 : W := mkw 0x08448868a86192a2 0x4108910d150c3254 0xc8c099e0f8e19386 0xb918133c1f1c3270

def z81 : W := mkw 0x25f4f7c9c0000000 0x04be9ef938000000 0xc7f0ffe0e0000002 0xf8fe1ffc1c000000

def z82 : W := mkw 0x080208243ef7d2e2 0x4100410487defa5c 0x180000001ffff3e4 0x0300000003fffe7c

def z83 : W := mkw 0x06a9400006924000 0x00d5280000d24800 0x17316000071a6000 0x42e62c0000e34c00

def z84 : W := mkw 0x26ede05bc0000000 0x04ddbc0b78000000 0xa7ffe01fe0000001 0xf4fffc03fc000000

def z85 : W := mkw 0x211037dbc0000000 0x042206fb78000000 0x60001fffe0000002 0x0c0003fffc000000

def z86 : W := mkw 0x27fff7dbd6d74000 0x04fffefb7adae800 0xffffffffffffe007 0xfffffffffffffc00

def z87 : W := mkw 0x27b9779340000000 0x04f72ef268000000 0xa731e703e0000003 0xd4e63ce07c000000

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c019e000000002 0xb818033c00000000

def z89 : W := mkw 0x27a9549200000000 0x04f52a9240000000 0x0700000000000000 0x00e0000000000000

def z90 : W := mkw 0x06ab400016d74000 0x00d5680002dae800 0x1f3160001fffe004 0x43e62c0003fffc00

def z91 : W := mkw 0x0046804890450000 0x0008d0091208a000 0xe8ce99fcf8e58007 0xbd19d33f9f1cb000

def z92 : W := mkw 0x100008200db81f07 0x0200010401b703e0 0xd8c019e01ff81f86 0xbb18033c03ff03f0

def z93 : W := mkw 0x100008200db81f07 0x0200010401b703e0 0x180000001ff81f84 0x0300000003ff03f0

def z94 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0x200fe01fe0000001 0x0401fc03fc000000

def z95 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0xe80e181c18e593e7 0x3d01c303831cb27c

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000001fe004 0x030000000003fc00

def z97 : W := mkw 0x0802082418651242 0x41004104830ca248 0x0000000018e00000 0x00000000031c0000

def z98 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0x47ce18fc00000000 0x28f9c31f80000000

def z99 : W := mkw 0x020b000012060000 0x004160000240c000 0x000f000000060001 0x0001e0000000c000

def z100 : W := mkw 0x04e4c00004d14000 0x009c9800009a2800 0x08f0e00000f9e000 0x811e1c00001f3c00

def z101 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x30316703e01a7ffa 0x46062ce07c034fff

def z102 : W := mkw 0x2a4fe05ff04580e0 0x4549fc0bfe08b01c 0x200fe01fe0058061 0x0401fc03fc00b00c

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001e0000007e001 0x00003c000000fc00

def z104 : W := mkw 0x0800086c88201242 0x4100010d91040248 0x400018fc00000000 0x0800031f80000000

def z105 : W := mkw 0x0000000000082508 0x20000000000104a1 0x10000000001a6c18 0x0200000000034d83

def z106 : W := mkw 0x01001c0009001804 0x0020038001200300 0xd7001e001f001c06 0x7ae003c003e00380

def z107 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xa8008703e0059fff 0x950010e07c00b3ff

def z108 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x273fe61fe0000001 0x44e7fcc3fc000000

def z109 : W := mkw 0x0002000016d74000 0x0000400002dae800 0x180000001fffe004 0x0300000003fffc00

def z110 : W := mkw 0x06edc00000000000 0x00ddb80000000000 0x87ffe00000000001 0xf0fffc0000000000

def z111 : W := mkw 0x210014da80000000 0x0420029b50000000 0x400018fc00000000 0x0800031f80000000

def z112 : W := mkw 0x00100b2008281702 0x00020164010502e0 0xd8f01fe018f81f86 0xfb1e03fc031f03f0

def z113 : W := mkw 0x06efc00012060000 0x00ddf8000240c000 0x97ffe0001f060005 0xf2fffc0003e0c000

def z114 : W := mkw 0x1000000005980d05 0x0200000000b301a0 0x1000000007180c00 0x0200000000e30180

def z115 : W := mkw 0x05b0178000080500 0x00b602f0000100a0 0xdff01fe000181f86 0xfbfe03fc000303f0

def z116 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x48f01fe000f81f82 0x891e03fc001f03f0

def z117 : W := mkw 0x0309141203020814 0x8061228240604102 0x1701060307020c18 0x42e020c060e04183

def z118 : W := mkw 0x01021c161b061854 0x80204382c360c30a 0x70001e1f1f061c7e 0x0e0003c3e3e0c38f

def z119 : W := mkw 0x0012230176dfe5a8 0x200244602edbfcb5 0xb831e703ffffffff 0xd7063ce07fffffff

def z120 : W := mkw 0x0010230140000000 0x0002046028000000 0xa031e703e0000003 0xd4063ce07c000000

def z121 : W := mkw 0x27fdf7dbe008a5a8 0x24ffbefb7c0114b5 0xffffffffe01fffff 0xfffffffffc03ffff

def z122 : W := mkw 0x27b977dbc0000000 0x04f72efb78000000 0x67317fffe0000002 0x4ce62ffffc000000

def z123 : W := mkw 0x0054a349e008a5a8 0x200a94693c0114b5 0xf8ffffffe01fffff 0xff1ffffffc03ffff

def z124 : W := mkw 0x06efc00012474000 0x00ddf8000248e800 0x87ffe0000007e001 0xf0fffc000000fc00

def z125 : W := mkw 0x27fdf7dbc0082508 0x24ffbefb780104a1 0xf7ffffffe01a6c1b 0xfefffffffc034d83

def z126 : W := mkw 0x07efdc161fd75854 0x80fdfb82c3faeb0a 0x47ce181c1fe00000 0x28f9c30383fc0000

def z127 : W := mkw 0x030b1c161fd75854 0x80616382c3faeb0a 0xff0f1e1f1ffffc7f 0x7fe1e3c3e3ffff8f

def z128 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xd70e1e1c1f001c06 0x7ae1c3c383e00380

def z129 : W := mkw 0x0046880418451040 0x0008d1008308a208 0xe8ce981c18e59067 0xbd19d303831cb20c

def z130 : W := mkw 0x04a0000004900000 0x0094000000920000 0x08f0000000f80000 0x811e0000001f0000

def z131 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x07f1e7e3e0000000 0xc0fe3cfc7c000000

def z132 : W := mkw 0x0846886cbb679af6 0xc108d10d976cf35e 0xf8ce99fcffe79fff 0xbf19d33f9ffcf3ff

def z133 : W := mkw 0x0b4f9c7ebb679af6 0xc169f38fd76cf35e 0xffcf9fffffe79fff 0xfff9f3fffffcf3ff

def z134 : W := mkw 0x15b017a004b80703 0x02b602f4009700e0 0xcff01fe000f80382 0xf9fe03fc001f0070

def z135 : W := mkw 0x3ffffffffdfd9fe7 0x47ffffffffbfb3fc 0xfffffffffffd9fe7 0xffffffffffffb3fc

def z136 : W := mkw 0x0b4f9c7eb86592e2 0x4169f38fd70cb25c 0xefcf9ffff8e593e7 0xfdf9f3ffff1cb27c

def z137 : W := mkw 0x10102b216db8bfaf 0x220205642db717f5 0xb831e703ffffffff 0xd7063ce07fffffff

def z138 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0x47c018e01fe00000 0x28f8031c03fc0000

def z139 : W := mkw 0x0002080418041040 0x0000410083008208 0xe00e181c18041067 0x3c01c3038300820c

def z140 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xd70f181c1f060005 0x7ae1e30383e0c000

def z141 : W := mkw 0x0010230140000000 0x0002046028000000 0xb031e703e0061c7f 0xd6063ce07c00c38f

def z142 : W := mkw 0x35f4ffe9cdb81f07 0x06be9ffd39b703e0 0xdff0ffe0fff81f86 0xfbfe1ffc1fff03f0

def z143 : W := mkw 0x04a0000004900000 0x0094000000920000 0x9ff000001ff80004 0xf3fe000003ff0000

def z144 : W := mkw 0x06efc04896d74000 0x00ddf80912dae800 0xfffff9fcffffe007 0xffffff3f9ffffc00

def z145 : W := mkw 0x224de05be000a0a8 0x2449bc0b7c001415 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z146 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x280e801cf8e593e5 0x0501d0039f1cb27c

def z147 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xf7ffffffe0061c7f 0xfefffffffc00c38f

def z148 : W := mkw 0x000208041fd75854 0x8000410083faeb0a 0x180000001ffffc7c 0x0300000003ffff8f

def z149 : W := mkw 0x2ffffffff86592e2 0x45ffffffff0cb25c 0xeffffffff8e593e7 0xfdffffffff1cb27c

def z150 : W := mkw 0x100008202db8bfaf 0x2200010405b717f5 0x180000001ffffffc 0x0300000003ffffff

def z151 : W := mkw 0x17ffd78017df4d05 0x02fffaf002fbe9a0 0x9fffe6001fffec05 0xf3fffcc003fffd80

def z152 : W := mkw 0x10100b200db81f07 0x0202016401b703e0 0x983007001ff81f86 0xd30600e003ff03f0

def z153 : W := mkw 0x034d945a80000000 0x0069b28b50000000 0xe7cf9fffe0000003 0xfcf9f3fffc000000

def z154 : W := mkw 0x08000824282092e2 0x410001048504125c 0x00000000000013e0 0x000000000000027c

def z155 : W := mkw 0x2ffff7dff04580e0 0x45fffefbfe08b01c 0xe7ffffffe0058063 0xfcfffffffc00b00c

def z156 : W := mkw 0x06ffe30176dfe5a8 0x20dffc602edbfcb5 0xbfffe703ffffffff 0xf7fffce07fffffff

def z157 : W := mkw 0x0100141200000000 0x0020028240000000 0x60001e1f00000002 0x0c0003c3e0000000

def z158 : W := mkw 0x231937dbc0000000 0x046326fb78000000 0xe70f1fffe0000003 0x7ce1e3fffc000000

def z159 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x1f3006001ff81f84 0x43e600c003ff03f0

def z160 : W := mkw 0x020b000012060000 0x004160000240c000 0x070e00001f000000 0x20e1c00003e00000

def z161 : W := mkw 0x15b03fa14db83f0f 0x22b607f429b707e1 0xdff17fe31ffa7f9e 0xfbfe2ffc63ff4ff3

def z162 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x570e181c1f061c7c 0x2ae1c30383e0c38f

def z163 : W := mkw 0x0002000010450000 0x000040000208a000 0x0800000018e58004 0x01000000031cb000

def z164 : W := mkw 0x225de35be008a5a8 0x244bbc6b7c0114b5 0xb83fe71fe01fffff 0xd707fce3fc03ffff

def z165 : W := mkw 0x020b000012060000 0x004160000240c000 0x9f3fe0001f1fe005 0xf3e7fc0003e3fc00

def z166 : W := mkw 0x024fc00012474000 0x0049f8000248e800 0x983fe000001fe005 0xd307fc000003fc00

def z167 : W := mkw 0x0309141200000000 0x0061228240000000 0xe70f1e1f00000003 0x7ce1e3c3e0000000

def z168 : W := mkw 0x180208243dfd9fe7 0x4300410487bfb3fc 0x180000001ffd9fe4 0x0300000003ffb3fc

def z169 : W := mkw 0x00000000200080a0 0x0000000004001014 0x08000000000593e4 0x010000000000b27c

def z170 : W := mkw 0x0b5fbf7ffb6fbffe 0xe16bf7efff6df7ff 0xffffffffffffffff 0xffffffffffffffff

def z171 : W := mkw 0x14b003a004b80703 0x02960074009700e0 0x9ff001e01ff80384 0xf3fe003c03ff0070

def z172 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x08ffe00000ffe001 0x811ffc00001ffc00

def z173 : W := mkw 0x27fdf7dbc4900000 0x04ffbefb78920000 0xfffffffffff80007 0xffffffffffff0000

def z174 : W := mkw 0x0eefc86c9ef75242 0x41ddf90d93deea48 0xdffff8fc1fffe005 0xfbffff1f83fffc00

def z175 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xbfffe6031ffffc7f 0xf7fffcc063ffff8f

def z176 : W := mkw 0x0010230140082508 0x20020460280104a1 0x0030600000186000 0x00060c0000030c00

def z177 : W := mkw 0x24f4e3c9e008a5a8 0x249e9c793c0114b5 0x08f0e1e0e019e380 0x811e1c3c1c033c70

def z178 : W := mkw 0x27fdf7dbc6924000 0x04ffbefb78d24800 0xf7ffffffe71a6003 0xfefffffffce34c00

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000060300001c7a 0x040000c06000038f

def z180 : W := mkw 0x01101f0009081d04 0x002203e0012103a0 0xdf301f001f181f86 0xfbe603e003e303f0

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x0830e0000019e000 0x81061c0000033c00

def z182 : W := mkw 0x000020016000a0a8 0x200004002c001415 0x2001e003e007e079 0x04003c007c00fc0f

def z183 : W := mkw 0x100008200db01a07 0x0200010401b60340 0x000000001fe00000 0x0000000003fc0000

def z184 : W := mkw 0x27b9779340000000 0x04f72ef268000000 0x0731660300000000 0x40e62cc060000000

def z185 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x470e181c1f000000 0x28e1c30383e00000

def z186 : W := mkw 0x0010230140082508 0x20020460280104a1 0x10316603001a6c18 0x42062cc060034d83

def z187 : W := mkw 0x27fdf7dbc4d14000 0x04ffbefb789a2800 0xefffffffe0f9e003 0xfdfffffffc1f3c00

def z188 : W := mkw 0x020b08161b061854 0x80416102c360c30a 0x300f001f1f061c7d 0x0601e003e3e0c38f

def z189 : W := mkw 0x001023016000a0a8 0x200204602c001415 0xa031e703e007e07b 0xd4063ce07c00fc0f

def z190 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001000300060079 0x040020006000c00f

def z191 : W := mkw 0x24f4e3c9c0000000 0x049e9c7938000000 0xe0fef9fce0000003 0xbc1fdf3f9c000000

def z192 : W := mkw 0x0846804cb04580e0 0x4108d0099608b01c 0x200e801ce0058061 0x0401d0039c00b00c

def z193 : W := mkw 0x37fffffbdfff5f07 0x06ffffff7bffebe0 0xffffffffffffff87 0xfffffffffffffff0

def z194 : W := mkw 0x14a008200db81f07 0x0294010401b703e0 0x9ff000001ff81f84 0xf3fe000003ff03f0

def z195 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x00000100e0000380 0x000000201c000070

def z196 : W := mkw 0x07efdc161fd75854 0x80fdfb82c3faeb0a 0xf7cf1e1f1fe61c7f 0x7ef9e3c3e3fcc38f

def z197 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x98ffe00018ffe005 0xf31ffc00031ffc00

def z198 : W := mkw 0x27fdd7da80000000 0x04ffbafb50000000 0xc7fe1ffc00000002 0xf8ffc3ff80000000

def z199 : W := mkw 0x0846804cb04580e0 0x4108d0099608b01c 0xa80e811ce00593e7 0x9501d0239c00b27c

def z200 : W := mkw 0x08448068a06182a2 0x4108900d140c3054 0xe8ce99fce0e18383 0xbd19d33f9c1c3070

def z201 : W := mkw 0x00000000200080a0 0x0000000004001014 0x08008100e0018380 0x810010201c003070

def z202 : W := mkw 0x0309141200000000 0x0061228240000000 0x470e181c00000000 0x28e1c30380000000

def z203 : W := mkw 0x2ffdf7fbe06182a2 0x45ffbeff7c0c3054 0xefffffffe0e18383 0xfdfffffffc1c3070

def z204 : W := mkw 0x0046882018651202 0x0008d104030ca240 0xc8ce99e018e59387 0xb919d33c031cb270

def z205 : W := mkw 0x0010030000080500 0x00020060000100a0 0x0000070000001f82 0x000000e0000003f0

def z206 : W := mkw 0x27b9779340082508 0x24f72ef2680104a1 0x17316603001a6c18 0x42e62cc060034d83

def z207 : W := mkw 0x27fdffdfc9001854 0x84ffbffbf920030a 0xe7ffffffe0001c7b 0xfcfffffffc00038f

def z208 : W := mkw 0x06efc00010450000 0x00ddf8000208a000 0x8fffe00018e58005 0xf1fffc00031cb000

def z209 : W := mkw 0x04a2000016d74000 0x0094400002dae800 0x9ff000001fffe004 0xf3fe000003fffc00

def z210 : W := mkw 0x020b000012060000 0x004160000240c000 0x970f00001f060005 0x72e1e00003e0c000

def z211 : W := mkw 0x07efdc161fd75854 0x80fdfb82c3faeb0a 0xfffffe1f1ffffc7f 0xffffffc3e3ffff8f

def z212 : W := mkw 0x25b037dbc0000000 0x04b606fb78000000 0xe7f01fffe0000002 0xfcfe03fffc000000

def z213 : W := mkw 0x37fdfffbcdb81f07 0x06ffbfff79b703e0 0xfffffffffff81f87 0xffffffffffff03f0

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z215 : W := mkw 0x020b001612060050 0x80416002c240c00a 0xb00f061f00061c7f 0x5601e0c3e000c38f

def z216 : W := mkw 0x101003a000280703 0x02020074000500e0 0x000001e000000380 0x0000003c00000070

def z217 : W := mkw 0x27ffffdfd8041040 0x04fffffbfb008208 0xe7fffffff8041067 0xfcffffffff00820c

def z218 : W := mkw 0x24f4e3c9c0000000 0x049e9c7938000000 0x00f0e1e0e0000000 0x801e1c3c1c000000

def z219 : W := mkw 0x0800004ca00080e0 0x410000099400101c 0x2000001ce0000060 0x040000039c00000c

def z220 : W := mkw 0x27fff7dbd2474000 0x04fffefb7a48e800 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z221 : W := mkw 0x0854a369e069a7aa 0x610a946d3c0d34f5 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z222 : W := mkw 0x07ffd78016d74000 0x00fffaf002dae800 0xdfffffe01fffe007 0xfbfffffc03fffc00

def z223 : W := mkw 0x14b003a004b80703 0x02960074009700e0 0x98f007e000f81f86 0xd31e00fc001f03f0

def z224 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x570f1e1f1f020c18 0x6ae1e3c3e3e04183

def z225 : W := mkw 0x01103f016908bdac 0x202207e02d2117b5 0xff31ff03ff1fffff 0xffe63fe07fe3ffff

def z226 : W := mkw 0x04e4c00004d14000 0x009c9800009a2800 0x00c0000000e00000 0x00180000001c0000

def z227 : W := mkw 0x26fde3dbc0000000 0x04dfbc7b78000000 0x20ffe1ffe0000001 0x841ffc3ffc000000

def z228 : W := mkw 0x0209001200000000 0x0041200240000000 0x200f001f00000001 0x0401e003e0000000

def z229 : W := mkw 0x24f4e3c9e008a5a8 0x249e9c793c0114b5 0xb8f1e7e3e01fffff 0xd71e3cfc7c03ffff

def z230 : W := mkw 0x26efe05bd6d74000 0x04ddfc0b7adae800 0xbfffe01fffffe005 0xf7fffc03fffffc00

def z231 : W := mkw 0x06ffe30176dfe5a8 0x20dffc602edbfcb5 0x9fffe100ffffe385 0xf3fffc201ffffc70

def z232 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x0ffee0001ff9e000 0xa1ffdc0003ff3c00

def z233 : W := mkw 0x15b03fa14db81f07 0x02b607f429b703e0 0xfff1ffe3fff81f87 0xfffe3ffc7fff03f0

def z234 : W := mkw 0x0002000412060050 0x800040008240c00a 0x0000000000060078 0x000000000000c00f

def z235 : W := mkw 0x27b9779343020814 0x84f72ef268604102 0x1731660307020c18 0x42e62cc060e04183

def z236 : W := mkw 0x2cf6ebedf86592e2 0x459edd7dbf0cb25c 0xe8fef9fcf8e593e7 0xbd1fdf3f9f1cb27c

def z237 : W := mkw 0x0b4f9c7ebb679af6 0xc169f38fd76cf35e 0xefce99fcffe593e7 0xbdf9d33f9ffcb27c

def z238 : W := mkw 0x0a4f886cba6792e2 0x4149f10d974cf25c 0xffcf99fcffe793e7 0xfff9f33f9ffcf27c

def z239 : W := mkw 0x27ffffdfdb061854 0x84fffffbfb60c30a 0xf7ffffffff061c7f 0xfeffffffffe0c38f

def z240 : W := mkw 0x01021c1619041854 0x80204382c320830a 0xe00e1e1f18041c7f 0x3c01c3c3e300838f

def z241 : W := mkw 0x37fddffa8db81f07 0x06ffbbff51b703e0 0xdffe1ffc1ff81f86 0xfbffc3ff83ff03f0

def z242 : W := mkw 0x000020016000a0a8 0x200004002c001415 0xb831e003e01fe07d 0xd7063c007c03fc0f

def z243 : W := mkw 0x0010230140082508 0x20020460280104a1 0xb0316603001e7c7f 0x56062cc06003cf8f

def z244 : W := mkw 0x14a000a004b00203 0x0294001400960040 0x00c000e000e00000 0x0018001c001c0000

def z245 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0xcfc019e01fe01386 0xb9f8033c03fc0270

def z246 : W := mkw 0x00468000304580a0 0x0008d0000608b014 0xa8ce8100f8e593e7 0xb519d0201f1cb27c

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0xb831e603001ffc7f 0xd7063cc06003ff8f

def z248 : W := mkw 0x235df7dbc0000000 0x046bbefb78000000 0x600fffffe0000003 0x0c01fffffc000000

def z249 : W := mkw 0x020b20177206a0f8 0xa0416402ee40d41f 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z250 : W := mkw 0x020b08041a061040 0x004161008340c208 0xf70f181c1f061067 0x7ee1e30383e0c20c

def z251 : W := mkw 0x0000082008201202 0x0000010401040240 0x400019e000001382 0x0800033c00000270

def z252 : W := mkw 0x04f4e30164d9e5a8 0x209e9c602c9b3cb5 0xb8f1e703e0ffffff 0xd71e3ce07c1fffff

def z253 : W := mkw 0x0000000003020814 0x8000000000604102 0x1000000007020c18 0x0200000000e04183

def z254 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x9830e700e019ff86 0xd3061ce01c033ff0

def z255 : W := mkw 0x2209601340000000 0x04412c0268000000 0x0001600300000000 0x00002c0060000000

def z256 : W := mkw 0x06a9400006924000 0x00d5280000d24800 0x0700000007000000 0x00e0000000e00000

def z257 : W := mkw 0x0000000000080500 0x00000000000100a0 0x1800000000181f84 0x03000000000303f0

def z258 : W := mkw 0x27fdfffbc8201202 0x04ffbfff79040240 0xeffffffff8e01387 0xfdffffffff1c0270

def z259 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x9831e100e01fe385 0xd3063c201c03fc70

def z260 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xb0010703e0061fff 0x560020e07c00c3ff

def z261 : W := mkw 0x01001c2009201a06 0x0020038401240340 0xdfc01fe01fe01f86 0xfbf803fc03fc03f0

def z262 : W := mkw 0x04e4c00004d14000 0x009c9800009a2800 0x9ff0e0001ff9e004 0xf3fe1c0003ff3c00

def z263 : W := mkw 0x0319371340000000 0x006326e268000000 0xe73fff1fe0000003 0xfce7ffe3fc000000

def z264 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0xc7fff8fc00000001 0xf8ffff1f80000000

def z265 : W := mkw 0x00000000200080a0 0x0000000004001014 0xb8018703e0079fff 0xd70030e07c00f3ff

def z266 : W := mkw 0x31103ffbc9281f07 0x062207ff792503e0 0x60001fffe0001f82 0x0c0003fffc0003f0

def z267 : W := mkw 0x11103fa16928bfaf 0x222207f42d2517f5 0x60001fe3e0001ffa 0x0c0003fc7c0003ff

def z268 : W := mkw 0x01103f176908bdfc 0xa02207e2ed2117bf 0x60001f1fe0001ffa 0x0c0003e3fc0003ff

def z269 : W := mkw 0x020b001612060050 0x80416002c240c00a 0xb70f001f1f06007d 0x76e1e003e3e0c00f

def z270 : W := mkw 0x0846886c98651242 0x4108d10d930ca248 0xe0ce18fc18e41067 0x3c19c31f831c820c

def z271 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0xe7ce99fce0000003 0xbcf9d33f9c000000

def z272 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x60ce98fcf8e58061 0x2c19d31f9f1cb00c

def z273 : W := mkw 0x0846886cbef7d2e2 0x4108d10d97defa5c 0xf8ce99fcfffff3e7 0xbf19d33f9ffffe7c

def z274 : W := mkw 0x0eefc04cb6d7c0e0 0x41ddf80996daf81c 0xbfffe01cffffe065 0xf7fffc039ffffc0c

def z275 : W := mkw 0x0010230140082508 0x20020460280104a1 0xb031e703e01a6c1b 0xd6063ce07c034d83

def z276 : W := mkw 0x0846886c98651242 0x4108d10d930ca248 0xc8ce98fc18e58005 0xb919d31f831cb000

def z277 : W := mkw 0x17b91792079a0d15 0x82f722f240f341a2 0x17310603071a0c18 0x42e620c060e34183

def z278 : W := mkw 0x1cf68becbcfd97e3 0x439ed17d979fb2fc 0xe8fe99fcf8fd93e7 0xbd1fd33f9f1fb27c

def z279 : W := mkw 0x03091c160b021854 0x80612382c160430a 0x77011e1f07021c7a 0x4ee023c3e0e0438f

def z280 : W := mkw 0x17bb1fa01fbe1f07 0x02f763f403f7c3e0 0xdfff1fe01ffe1f87 0xfbffe3fc03ffc3f0

def z281 : W := mkw 0x06fde3016008a5a8 0x20dfbc602c0114b5 0xbfffe703e01fffff 0xf7fffce07c03ffff

def z282 : W := mkw 0x0044804880000000 0x0008900910000000 0x200e801ce0000001 0x0401d0039c000000

def z283 : W := mkw 0x0309141203020814 0x8061228240604102 0xf70f1e1f07020c1b 0x7ee1e3c3e0e04183

def z284 : W := mkw 0x15b01fa02db8bfaf 0x22b603f405b717f5 0xdff01fe01ffffffe 0xfbfe03fc03ffffff

def z285 : W := mkw 0x14b00ba00cb81703 0x02960174019702e0 0xc8f019e018f81386 0xb91e033c031f0270

def z286 : W := mkw 0x034f9c161b471854 0x8069f382c368e30a 0xffcf9e1f1fe79c7f 0xfff9f3c3e3fcf38f

def z287 : W := mkw 0x0eefc86cb86592e2 0x41ddf90d970cb25c 0xeffff9fcf8e593e7 0xfdffff3f9f1cb27c

def z288 : W := mkw 0x0a4f805eb24780f0 0xc149f00bd648f01e 0x200f801fe0078079 0x0401f003fc00f00f

def z289 : W := mkw 0x06b96301669ae5a8 0x20d72c602cd35cb5 0xbf31e703e71fffff 0xd7e63ce07ce3ffff

def z290 : W := mkw 0x16efc8201fff5f07 0x02ddf90403ffebe0 0x9fffe0001fffff85 0xf3fffc0003fffff0

def z291 : W := mkw 0x0002000012474000 0x000040000248e800 0x000000000007e000 0x000000000000fc00

def z292 : W := mkw 0x0002080418041040 0x0000410083008208 0x400e181c18000000 0x2801c30383000000

def z293 : W := mkw 0x211037dbc0000000 0x042206fb78000000 0xe031ffffe0000003 0xdc063ffffc000000

def z294 : W := mkw 0x0fefdc7ebff7daf6 0xc1fdfb8fd7fefb5e 0xffffffffffffffff 0xffffffffffffffff

def z295 : W := mkw 0x06edc00006924000 0x00ddb80000d24800 0x97ffe000071a6001 0xf2fffc0000e34c00

def z296 : W := mkw 0x04f4e30164d9e5a8 0x209e9c602c9b3cb5 0x08f0e100e0f9e380 0x811e1c201c1f3c70

def z297 : W := mkw 0x0002000012060000 0x000040000240c000 0x100000001f060004 0x0200000003e0c000

def z298 : W := mkw 0x14b0038004980501 0x02960070009300a0 0x0030000000180000 0x0006000000030000

def z299 : W := mkw 0x000000002008a5a8 0x20000000040114b5 0x080000000019e380 0x0100000000033c70

def z300 : W := mkw 0x17b95780079a4d05 0x02f72af000f349a0 0x17316600071a6c00 0x42e62cc000e34d80

def z301 : W := mkw 0x0000004880000000 0x0000000910000000 0x600019fce0000002 0x0c00033f9c000000

def z302 : W := mkw 0x07a9541207924814 0x80f52a8240f24902 0x17316603071a6c18 0x42e62cc060e34d83

def z303 : W := mkw 0x27fdf7dbc3020814 0x84ffbefb78604102 0xf7ffffffe7020c1b 0xfefffffffce04183

def z304 : W := mkw 0x08020004304580e0 0x410040008608b01c 0x0000000000058060 0x000000000000b00c

def z305 : W := mkw 0x0002000016d74000 0x0000400002dae800 0x9831e0001fffe005 0xd3063c0003fffc00

def z306 : W := mkw 0x0a4fc04cb247c0e0 0x4149f8099648f81c 0x200fe01ce007e061 0x0401fc039c00fc0c

def z307 : W := mkw 0x030b1c361b261a56 0x80616386c364c34a 0xffcf1fff1fe61fff 0xfff9e3ffe3fcc3ff

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00e181c00000003 0x3c01c30380000000

def z309 : W := mkw 0x15b01f800d981d05 0x02b603f001b303a0 0xd7301e001f181c06 0x7ae603c003e30380

def z310 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x170106031f061c7c 0x42e020c063e0c38f

def z311 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x47fef9fce0000000 0xa8ffdf3f9c000000

def z312 : W := mkw 0x27ffffdfdfd75854 0x84fffffbfbfaeb0a 0xfffffffffffffc7f 0xffffffffffffff8f

def z313 : W := mkw 0x06ab000016960000 0x00d5600002d2c000 0x9fff00001ffe0005 0xf3ffe00003ffc000

def z314 : W := mkw 0x0046884c98041040 0x0008d10993008208 0xe0ce99fcf8041067 0xbc19d33f9f00820c

def z315 : W := mkw 0x19101feca9289fe7 0x432203fd952513fc 0x60001ffce0001fe2 0x0c0003ff9c0003fc

def z316 : W := mkw 0x030b1c1618041040 0x00616382c3008208 0xe70f1e1f18041067 0x7ce1e3c3e300820c

def z317 : W := mkw 0x05b0178000000000 0x00b602f000000000 0xc7f01fe000000002 0xf8fe03fc00000000

def z318 : W := mkw 0x0846804cb04580e0 0x4108d0099608b01c 0xe0ce99fce0058063 0xbc19d33f9c00b00c

def z319 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfff11fe31ffe1fff 0xfffe23fc63ffc3ff

def z320 : W := mkw 0x08468824386592e2 0x4108d104870cb25c 0x88ce800018e593e5 0xb119d000031cb27c

def z321 : W := mkw 0x27b977936008a5a8 0x24f72ef26c0114b5 0xbf31e703e01fffff 0xd7e63ce07c03ffff

def z322 : W := mkw 0x27fdf7dbc0080500 0x04ffbefb780100a0 0xffffffffe0181f87 0xfffffffffc0303f0

def z323 : W := mkw 0x0002000010040000 0x0000400002008000 0x800e000018040005 0x3001c00003008000

def z324 : W := mkw 0x034f9c5e9b061854 0x8069f38bd360c30a 0xf7cf9fffff061c7f 0xfef9f3ffffe0c38f

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x10316000001a6000 0x42062c0000034c00

def z326 : W := mkw 0x17b91fb20db81f07 0x02f723f641b703e0 0xffff1fff1ff81f87 0xffffe3ffe3ff03f0

def z327 : W := mkw 0x17efdca01ff75a07 0x02fdfb9403feeb40 0x47ce18e01fe00000 0x28f9c31c03fc0000

def z328 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xb8300703e0181ffe 0xd70600e07c0303ff

def z329 : W := mkw 0x00102301600080a0 0x000204602c001014 0xa831e703e00593e7 0xd5063ce07c00b27c

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800800000058005 0x910010000000b000

def z331 : W := mkw 0x05b0378140000000 0x00b606f028000000 0xe7f1ffe3e0000003 0xfcfe3ffc7c000000

def z332 : W := mkw 0x17bb1fb61fbe1f57 0x82f763f6c3f7c3ea 0xffff1fff1ffe1fff 0xffffe3ffe3ffc3ff

def z333 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xa031e703e0001ffb 0xd4063ce07c0003ff

def z334 : W := mkw 0x07efdc161fd75854 0x80fdfb82c3faeb0a 0xdffff81c1fffe005 0xfbffff0383fffc00

def z335 : W := mkw 0x37b97fb34db81f07 0x06f72ff669b703e0 0xdff17fe31ff81f86 0xfbfe2ffc63ff03f0

def z336 : W := mkw 0x15f4dfa00df95f07 0x02be9bf401bf2be0 0xdff0ffe01ff9ff86 0xfbfe1ffc03ff3ff0

def z337 : W := mkw 0x0b0b1c7ebb269af6 0xc161638fd764d35e 0xf70f1fffff061fff 0x7ee1e3ffffe0c3ff

def z338 : W := mkw 0x11101fa009281f07 0x022203f4012503e0 0x40001fe000001f82 0x080003fc000003f0

def z339 : W := mkw 0x211037dbe008a5a8 0x242206fb7c0114b5 0xf831ffffe01fffff 0xdf063ffffc03ffff

def z340 : W := mkw 0x06ffc30016df4500 0x00dff86002dbe8a0 0x9fffe7001fffff87 0xf3fffce003fffff0

def z341 : W := mkw 0x0ce4c068a4f1c2a2 0x419c980d149e3854 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z342 : W := mkw 0x0856a34df04da5e8 0x610ad469be09b4bd 0xb83fe71fe01fffff 0xd707fce3fc03ffff

def z343 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x57f01ee01ff80c00 0x6afe03dc03ff0180

def z344 : W := mkw 0x021b2301720ea5a8 0x204364602e41d4b5 0xbf3fe703ff1fffff 0xf7e7fce07fe3ffff

def z345 : W := mkw 0x04a0000004900000 0x0094000000920000 0x1730000007180000 0x42e6000000e30000

def z346 : W := mkw 0x025fe301724fe5a8 0x204bfc602e49fcb5 0xb83fe703e01fffff 0xd707fce07c03ffff

def z347 : W := mkw 0x131b1fb61b2e1f57 0x826363f6c365c3ea 0xf70f1fff1f061fff 0x7ee1e3ffe3e0c3ff

def z348 : W := mkw 0x0209001202020010 0x8041200240404002 0x0001000300020018 0x0000200060004003

def z349 : W := mkw 0x17ab1cb61fb61a57 0x82f56396c3f6c34a 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z350 : W := mkw 0x000000002008a5a8 0x20000000040114b5 0x0000000000001ff8 0x00000000000003ff

def z351 : W := mkw 0x0844886ca86192e2 0x4108910d950c325c 0x68c099fce0e193e2 0x8d18133f9c1c327c

def z352 : W := mkw 0x14f4c3a004f94703 0x029e9874009f28e0 0x08f0e1e000f9e380 0x811e1c3c001f3c70

def z353 : W := mkw 0x15b01fa02db89fa7 0x02b603f405b713f4 0xfff09fe0fffd9fe7 0xfffe13fc1fffb3fc

def z354 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xe70e181c1f041067 0x3ce1c30383e0820c

def z355 : W := mkw 0x2ffdffffe82092e2 0x45ffbffffd04125c 0xe7ffffffe00013e3 0xfcfffffffc00027c

def z356 : W := mkw 0x000000002008a5a8 0x20000000040114b5 0xb8008100e01fffff 0x970010201c03ffff

def z357 : W := mkw 0x01001c0009001804 0x0020038001200300 0xf7011e031f061c7f 0x7ee023c063e0c38f

def z358 : W := mkw 0x0846a86df865b2ea 0x6108d50dbf0cb65d 0xe8cff9fff8e7f3ff 0xbd19ff3fff1cfe7f

def z359 : W := mkw 0x0000080008001000 0x0000010001000200 0xc000180018001006 0x3800030003000200

def z360 : W := mkw 0x07efdc001fd75804 0x00fdfb8003faeb00 0xdffffe001ffffc07 0xfbffffc003ffff80

def z361 : W := mkw 0x0000200140002008 0x2000040028000401 0x0001600300026018 0x00002c0060004c03

def z362 : W := mkw 0x001003002008a5a8 0x20020060040114b5 0x98300700001ffffe 0xd30600e00003ffff

def z363 : W := mkw 0x17bb1fb61fbe1f57 0x82f763f6c3f7c3ea 0xdffe1ffc1ff81f86 0xfbffc3ff83ff03f0

def z364 : W := mkw 0x0002080418041040 0x0000410083008208 0xf00f1e1f18061c7f 0x7e01e3c3e300c38f

def z365 : W := mkw 0x201023c9c0000000 0x0402047938000000 0x000001e0e0000000 0x0000003c1c000000

def z366 : W := mkw 0x07fdd78000000000 0x00ffbaf000000000 0xc7ffffe000000003 0xf8fffffc00000000

def z367 : W := mkw 0x27ffffdfdb061854 0x84fffffbfb60c30a 0xe7ffffffff000003 0xfcffffffffe00000

def z368 : W := mkw 0x17efdca01ff75a07 0x02fdfb9403feeb40 0xdffff8e01fffe005 0xfbffff1c03fffc00

def z369 : W := mkw 0x000000002008a5a8 0x20000000040114b5 0xb8010603001fffff 0x570020c06003ffff

def z370 : W := mkw 0x0802086cb86592e2 0x4100410d970cb25c 0x680019fcf8e593e6 0x0d00033f9f1cb27c

def z371 : W := mkw 0x0000082008201202 0x0000010401040240 0x0800000018e01384 0x01000000031c0270

def z372 : W := mkw 0x0846a04df045a0e8 0x6108d409be08b41d 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z373 : W := mkw 0x15b21fa41dbc1f47 0x02b643f483b783e8 0xfffe1ffc1ffc1fe7 0xffffc3ff83ff83fc

def z374 : W := mkw 0x0854a369e069a7aa 0x610a946d3c0d34f5 0xb8f1e7e3e0ffffff 0xd71e3cfc7c1fffff

def z375 : W := mkw 0x030b141213060814 0x806162824260c102 0x970f06031f060c1d 0x72e1e0c063e0c183

def z376 : W := mkw 0x0b4f9c7e9b671a56 0xc169f38fd36ce34a 0xf7cf1eff1fe61c7f 0x7ef9e3dfe3fcc38f

def z377 : W := mkw 0x0056a301704da5a8 0x200ad4602e09b4b5 0xb8ffe703f8ffffff 0xf71ffce07f1fffff

def z378 : W := mkw 0x06edc00004900000 0x00ddb80000920000 0x9fffe0001ff80005 0xf3fffc0003ff0000

def z379 : W := mkw 0x0856ab6df86db7ea 0x610ad56dbf0db6fd 0xe8ce9ffff8e59fff 0xbd19d3ffff1cb3ff

def z380 : W := mkw 0x0846804cb04580e0 0x4108d0099608b01c 0xa8ce801cf8e58065 0xb519d0039f1cb00c

def z381 : W := mkw 0x0856ab6df86db7ea 0x610ad56dbf0db6fd 0xe8fef9fcf8fdf3e7 0xbd1fdf3f9f1fbe7c

def z382 : W := mkw 0x04e4c00004d14000 0x009c9800009a2800 0x98f1e00000ffe005 0xd31e3c00001ffc00

def z383 : W := mkw 0x0846804c90450040 0x4108d0099208a008 0x000e001c00000000 0x0001c00380000000

def z384 : W := mkw 0x06efc01616d74050 0x80ddf802c2dae80a 0xbfffe01f1fffe07d 0xf7fffc03e3fffc0f

def z385 : W := mkw 0x04b023016498a5a8 0x209604602c9314b5 0xbff1e703ffffffff 0xf7fe3ce07fffffff

def z386 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x173fe000071fe001 0x42e7fc0000e3fc00

def z387 : W := mkw 0x06ffe30156df6508 0x20dffc602adbeca1 0x9fffe6031fffec1d 0xf3fffcc063fffd83

def z388 : W := mkw 0x08448068a06182a2 0x4108900d140c3054 0xa8c081e0e0e593e7 0x9518103c1c1cb27c

def z389 : W := mkw 0x0846886c98651242 0x4108d10d930ca248 0xc8ce19fc18e01386 0xb919c33f831c0270

def z390 : W := mkw 0x03091c1609001854 0x80612382c120030a 0xe70f1e1f00001c7b 0x7ce1e3c3e000038f

def z391 : W := mkw 0x0eefc8243ef7d2e2 0x41ddf90487defa5c 0x9fffe0001ffff3e5 0xf3fffc0003fffe7c

def z392 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xffffffffe01fe007 0xfffffffffc03fc00

def z393 : W := mkw 0x17ab1cb61fb61a57 0x82f56396c3f6c34a 0xf7cf1eff1fe61c7f 0x7ef9e3dfe3fcc38f

def z394 : W := mkw 0x020b001612060050 0x80416002c240c00a 0x000e001c00000000 0x0001c00380000000

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800010000001386 0x9100002000000270

def z396 : W := mkw 0x0044800000410000 0x0008900000082000 0x08c0800000e18000 0x81181000001c3000

def z397 : W := mkw 0x0002000410040040 0x0000400082008008 0x200e001c00040061 0x0401c0038000800c

def z398 : W := mkw 0x0b4f9c7e9b671a56 0xc169f38fd36ce34a 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z399 : W := mkw 0x15b21fa01fff5f07 0x02b643f403ffebe0 0xdff01fe01fffff86 0xfbfe03fc03fffff0

def z400 : W := mkw 0x04a008200cb01202 0x0094010401960240 0xdff019e01ff81386 0xfbfe033c03ff0270

def z401 : W := mkw 0x06b96301469a6508 0x20d72c6028d34ca1 0x17316603071a6c18 0x42e62cc060e34d83

def z402 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x2001e703e007fffb 0x04003ce07c00ffff

def z403 : W := mkw 0x01021c0419041844 0x0020438083208308 0xf70e1e1c1f041c67 0x7ee1c3c383e0838c

def z404 : W := mkw 0x08102b6de828b7ea 0x6102056dbd0516fd 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z405 : W := mkw 0x0846886c98651242 0x4108d10d930ca248 0xe0ce99fcf8e00003 0xbc19d33f9f1c0000

def z406 : W := mkw 0x0044c00000414000 0x0008980000082800 0x0000e0000001e000 0x00001c0000003c00

def z407 : W := mkw 0x11101fa009281f07 0x022203f4012503e0 0xd7001fe01f001f86 0x7ae003fc03e003f0

def z408 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x97cf00001fe60005 0x72f9e00003fcc000

def z409 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xe70f1e1f1f000003 0x7ce1e3c3e3e00000

def z410 : W := mkw 0x08122b25786db7ea 0x61024564af0db6fd 0xb831e703f8ffffff 0xd7063ce07f1fffff

def z411 : W := mkw 0x15b01fb60db81f57 0x82b603f6c1b703ea 0xfff01fff1ff81ffe 0xfffe03ffe3ff03ff

def z412 : W := mkw 0x1000082009281f07 0x02000104012503e0 0x0000000000001f80 0x00000000000003f0

def z413 : W := mkw 0x06a9400006924000 0x00d5280000d24800 0x9f31e000071fe005 0xd3e63c0000e3fc00

def z414 : W := mkw 0x08000020206182a2 0x41000004040c3054 0x0800000000e18380 0x01000000001c3070

def z415 : W := mkw 0x00122b057b0ebdfc 0xa0024560af61d7bf 0xb831e703ff1fffff 0xd7063ce07fe3ffff

def z416 : W := mkw 0x000000002008a5a8 0x20000000040114b5 0x9831e000001ffffd 0xd3063c000003ffff

def z417 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xa830e100e01df3e7 0x95061c201c03be7c

def z418 : W := mkw 0x1db21fa43dfd9fe7 0x43b643f487bfb3fc 0xdff01fe01ffd9fe6 0xfbfe03fc03ffb3fc

def z419 : W := mkw 0x0010230140080500 0x00020460280100a0 0xb831e703e0181f87 0xd7063ce07c0303f0

def z420 : W := mkw 0x15b03fa16db8bfaf 0x22b607f42db717f5 0xfff01fe3fff81ffe 0xfffe03fc7fff03ff

def z421 : W := mkw 0x06efc8201ef75202 0x00ddf90403deea40 0xdffff9e01ffff387 0xfbffff3c03fffe70

def z422 : W := mkw 0x0044800000000000 0x0008900000000000 0x80ce800000000001 0xb019d00000000000

def z423 : W := mkw 0x0000080408001040 0x0000010081000208 0x6000181c00001062 0x0c0003038000020c

def z424 : W := mkw 0x27fff7dbd6d74000 0x04fffefb7adae800 0xe7ffffffffe00003 0xfcfffffffffc0000

def z425 : W := mkw 0x231b3fdfdb061854 0x846367fbfb60c30a 0xf70f1fffff061c7f 0x7ee1e3ffffe0c38f

def z426 : W := mkw 0x130b1c361fbe1f57 0x82616386c3f7c3ea 0xff0f1e1f1ffe1fff 0x7fe1e3c3e3ffc3ff

def z427 : W := mkw 0x08468068b06582a2 0x4108d00d160cb054 0x88ce81e0f8e58385 0xb119d03c1f1cb070

def z428 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x000e800000058001 0x0001d0000000b000

def z429 : W := mkw 0x09001c7ea9209af6 0xc120038fd524135e 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z430 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xff3ffe1f1f1ffc7f 0xffe7ffc3e3e3ff8f

def z431 : W := mkw 0x2fefdcfeb86592e2 0x45fdfb9fd70cb25c 0xefce99fcf8e593e7 0xbdf9d33f9f1cb27c

def z432 : W := mkw 0x0002080418041040 0x0000410083008208 0x0000000018041064 0x000000000300820c

def z433 : W := mkw 0x030b141613060854 0x80616282c260c10a 0x370f061f07060c79 0x46e1e0c3e0e0c18f

def z434 : W := mkw 0x37fdf7dbc5980d05 0x06ffbefb78b301a0 0xf7ffffffe7180c03 0xfefffffffce30180

def z435 : W := mkw 0x00000000200080a0 0x0000000004001014 0x20008000e0058061 0x040010001c00b00c

def z436 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0xd7c01ee01fe01c06 0x7af803dc03fc0380

def z437 : W := mkw 0x0846886cb86db7ea 0x6108d10d970db6fd 0xf8ce99fcf8ffffff 0xbf19d33f9f1fffff

def z438 : W := mkw 0x11101fb609281f57 0x822203f6c12503ea 0x60001fff00001ffa 0x0c0003ffe00003ff

def z439 : W := mkw 0x224fe05fd2060050 0x8449fc0bfa40c00a 0x200fe01fe0060079 0x0401fc03fc00c00f

def z440 : W := mkw 0x27b9779346924000 0x04f72ef268d24800 0x17316603071a6000 0x42e62cc060e34c00

def z441 : W := mkw 0x024f800012470000 0x0049f0000248e000 0x9fcf80001fe78005 0xf3f9f00003fcf000

def z442 : W := mkw 0x03193713630aadbc 0xa06326e26c6155b7 0xbf31e703e71fffff 0xd7e63ce07ce3ffff

def z443 : W := mkw 0x0010030000080500 0x00020060000100a0 0x9831e700001fff87 0xd3063ce00003fff0

def z444 : W := mkw 0x0046800016d74000 0x0008d00002dae800 0x98ce80001fffe005 0xb319d00003fffc00

def z445 : W := mkw 0x06efc00036dfe5a8 0x20ddf80006dbfcb5 0x9fffe0001ffffffd 0xf3fffc0003ffffff

def z446 : W := mkw 0x09469c6cb9659ae6 0x4128d38d972cb35c 0xffce9ffcffe59fe7 0xfff9d3ff9ffcb3fc

def z447 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x1830e100e01ffffc 0x83061c201c03ffff

def z448 : W := mkw 0x15b0178005980d05 0x02b602f000b301a0 0x9ff006001ff80c04 0xf3fe00c003ff0180

def z449 : W := mkw 0x01103f176908bdfc 0xa02207e2ed2117bf 0xf831ff1fe01fffff 0xdf063fe3fc03ffff

def z450 : W := mkw 0x0844886ca82092e2 0x4108910d9504125c 0xe0ce99fce00013e3 0xbc19d33f9c00027c

def z451 : W := mkw 0x2a4fe87ff86592e2 0x4549fd0fff0cb25c 0xe8cff9fff8e593e7 0xbd19ff3fff1cb27c

def z452 : W := mkw 0x27fdf7dbe008a5a8 0x24ffbefb7c0114b5 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z453 : W := mkw 0x0010030000080500 0x00020060000100a0 0x0830010000180380 0x8106002000030070

def z454 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x670e1e1f1f001c7a 0x2ce1c3c3e3e0038f

def z455 : W := mkw 0x080208243b679af6 0xc1004104876cf35e 0x180000001fe79ffc 0x0300000003fcf3ff

def z456 : W := mkw 0x024fc00012474000 0x0049f8000248e800 0x970fe0001f07e005 0x72e1fc0003e0fc00

def z457 : W := mkw 0x11101fa00db81f07 0x022203f401b703e0 0x58001fe01ff81f86 0x0b0003fc03ff03f0

def z458 : W := mkw 0x000020016008a5a8 0x200004002c0114b5 0x3801e003e01ffffd 0x07003c007c03ffff

def z459 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x67ce1fffe0000002 0x2cf9c3fffc000000

def z460 : W := mkw 0x06ffe30156d74000 0x00dffc602adae800 0xbfffe703ffffe007 0xf7fffce07ffffc00

def z461 : W := mkw 0x04a0400004904000 0x0094080000920800 0x0030600000186000 0x00060c0000030c00

def z462 : W := mkw 0x0000080009001804 0x0000010001200300 0x100000001f001c04 0x0200000003e00380

def z463 : W := mkw 0x1db01fecadb89fe7 0x43b603fd95b713fc 0xfff01ffcfff81fe6 0xfffe03ff9fff03fc

def z464 : W := mkw 0x07ab1c161f961854 0x80f56382c3f2c30a 0xffff1e1f1ffe1c7f 0xffffe3c3e3ffc38f

def z465 : W := mkw 0x0044886888201202 0x0008910d11040240 0xe8ce99fcf8e01387 0xbd19d33f9f1c0270

def z466 : W := mkw 0x030b1c163b0ebdfc 0xa0616382c761d7bf 0xff0f1e1f1f1fffff 0x7fe1e3c3e3e3ffff

def z467 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xa831e703e019e383 0xd5063ce07c033c70

def z468 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x18316603001ffffc 0x43062cc06003ffff

def z469 : W := mkw 0x27fff7dbd2060000 0x04fffefb7a40c000 0xf7ffffffff060007 0xfeffffffffe0c000

def z470 : W := mkw 0x0802086cb82492e2 0x4100410d9704925c 0xe00e19fcf80413e7 0x3c01c33f9f00827c

def z471 : W := mkw 0x06ab400016964000 0x00d5680002d2c800 0x973f60001f1e6005 0x72e7ec0003e3cc00

def z472 : W := mkw 0x2ffffffffef7d2e2 0x45ffffffffdefa5c 0xfffffffffffff3e7 0xfffffffffffffe7c

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000060000001c06 0x520000c000000380

def z474 : W := mkw 0x0000082008201202 0x0000010401040240 0x40c018e018e00000 0x2818031c031c0000

def z475 : W := mkw 0x06edc00006d34000 0x00ddb80000da6800 0x1ff1e00007fbe000 0xc3fe3c0000ff7c00

def z476 : W := mkw 0x1000002004b80703 0x02000004009700e0 0x0800000000f80380 0x01000000001f0070

def z477 : W := mkw 0x05b0178004900000 0x00b602f000920000 0xdff01fe01ff80006 0xfbfe03fc03ff0000

def z478 : W := mkw 0x05b037816008a5a8 0x20b606f02c0114b5 0xfff1ffe3e01fffff 0xfffe3ffc7c03ffff

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x9001000000060005 0x520020000000c000

def z480 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x87ffe0001fe00001 0xf0fffc0003fc0000

def z481 : W := mkw 0x0000000006924000 0x0000000000d24800 0x10000000071a6000 0x0200000000e34c00

def z482 : W := mkw 0x100208201fff5f07 0x0200410403ffebe0 0x180000001fffff84 0x0300000003fffff0

def z483 : W := mkw 0x1de69cec9df51a47 0x43bcd39d93bea348 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z484 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x47c01fe01fe01f82 0x28f803fc03fc03f0

def z485 : W := mkw 0x211037dbe008a5a8 0x242206fb7c0114b5 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z486 : W := mkw 0x01001c0009001804 0x0020038001200300 0x40001e0000001c02 0x080003c000000380

def z487 : W := mkw 0x0a4fc86cba67d2e2 0x4149f90d974cfa5c 0xe8cff9fcf8e7f3e7 0xbd19ff3f9f1cfe7c

def z488 : W := mkw 0x024fc01612474050 0x8049f802c248e80a 0x200fe01f0007e079 0x0401fc03e000fc0f

def z489 : W := mkw 0x27b9779340000000 0x04f72ef268000000 0xe73f7e1f00000003 0x7ce7efc3e0000000

def z490 : W := mkw 0x1110178001080d05 0x022202f0002101a0 0x0000060000000c00 0x000000c000000180

def z491 : W := mkw 0x0010030000000000 0x0002006000000000 0x8030070000000002 0xd00600e000000000

def z492 : W := mkw 0x15a01ca00db81f07 0x02b4039401b703e0 0x5fc018e01ff81f84 0x2bf8031c03ff03f0

def z493 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x1831e703e01bef98 0xc3063ce07c037df3

def z494 : W := mkw 0x07efd41216d74000 0x00fdfa8242dae800 0xfffffe1f1fffe007 0xffffffc3e3fffc00

def z495 : W := mkw 0x27fdf79340000000 0x04ffbef268000000 0x87ffe60300000001 0xf0fffcc060000000

def z496 : W := mkw 0x1cf483e8a4f987a3 0x439e907d149f30f4 0x08f081e0e0f98380 0x811e103c1c1f3070

def z497 : W := mkw 0x0100141201000814 0x8020028240200102 0x0000060300000c18 0x000000c060000183

def z498 : W := mkw 0x00000000200080a0 0x0000000004001014 0x20000100e00013e2 0x040000201c00027c

def z499 : W := mkw 0x25f4f7dbc0000000 0x04be9efb78000000 0x60f0ffffe0000002 0x8c1e1ffffc000000

def z500 : W := mkw 0x26fde3c9c0000000 0x04dfbc7938000000 0x87ffe1e0e0000001 0xf0fffc3c1c000000

def z501 : W := mkw 0x00122b05780cb5e8 0x20024560af0196bd 0xf83fff1ff81fffff 0xff07ffe3ff03ffff

def z502 : W := mkw 0x0a4f887eba6792f2 0xc149f10fd74cf25e 0xe8cf99fff8e793ff 0xbd19f33fff1cf27f

def z503 : W := mkw 0x0ce6c86cbcf5d2e2 0x419cd90d979eba5c 0xe8fef9fcf8fdf3e7 0xbd1fdf3f9f1fbe7c

def z504 : W := mkw 0x27b9779340000000 0x04f72ef268000000 0xc7f17fe300000002 0xf8fe2ffc60000000

def z505 : W := mkw 0x27ffffdffb0ebdfc 0xa4fffffbff61d7bf 0xffffffffff1fffff 0xffffffffffe3ffff

def z506 : W := mkw 0x031b1f161b0e1d54 0x806363e2c361c3aa 0xff3f1f1f1f1e1fff 0xffe7e3e3e3e3c3ff

def z507 : W := mkw 0x2ffffffff86db7ea 0x65ffffffff0db6fd 0xfffffffff8ffffff 0xffffffffff1fffff

def z508 : W := mkw 0x0000002000200202 0x0000000400040040 0x08c001e000e00380 0x8118003c001c0070

def z509 : W := mkw 0x27fff79356d74000 0x04fffef26adae800 0x9fffe6031fffe005 0xf3fffcc063fffc00

def z510 : W := mkw 0x0209000002020000 0x0041200000404000 0x1701000007020000 0x42e0200000e04000

def z511 : W := mkw 0x27bb7f975b061854 0x84f76ff2eb60c30a 0xf73f7e1f1f061c7f 0x7ee7efc3e3e0c38f

def z512 : W := mkw 0x37fdfffbcdb01a07 0x06ffbfff79b60340 0xe7ffffffffe00003 0xfcfffffffffc0000

def z513 : W := mkw 0x17ffdfa01fff5f07 0x02fffbf403ffebe0 0xdffe1fe01ff81f86 0xfbffc3fc03ff03f0

def z514 : W := mkw 0x06efc00036d7c0a0 0x00ddf80006daf814 0xbfffe100fffff3e7 0xf7fffc201ffffe7c

def z515 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x47ff7eff00000000 0x68ffefdfe0000000

def z516 : W := mkw 0x0010030000080500 0x00020060000100a0 0xb8310703001e1fff 0xd70620e06003c3ff

def z517 : W := mkw 0x06efc8041fd75854 0x80ddf90083faeb0a 0x9fffe0001ffffc7d 0xf3fffc0003ffff8f

def z518 : W := mkw 0x07b9179200000000 0x00f722f240000000 0xe7ff1fff00000003 0xfcffe3ffe0000000

def z519 : W := mkw 0x024fc00012474000 0x0049f8000248e800 0x88cfe00018e7e005 0xb119fc00031cfc00

def z520 : W := mkw 0x01021c041b061854 0x802043808360c30a 0xd7001e001f061c7e 0x7ae003c003e0c38f

def z521 : W := mkw 0x04a0000004900000 0x0094000000920000 0x07c000001fe00000 0x20f8000003fc0000

def z522 : W := mkw 0x05a01c000d901804 0x00b4038001b20300 0xdff01e001ff81c06 0xfbfe03c003ff0380

def z523 : W := mkw 0x2044e049c0000000 0x04089c0938000000 0x0000e000e0000000 0x00001c001c000000

def z524 : W := mkw 0x34f4e3e9c4b80703 0x069e9c7d389700e0 0x08f0e1e0e0f80380 0x811e1c3c1c1f0070

def z525 : W := mkw 0x0010030000080500 0x00020060000100a0 0x1030060000180c00 0x420600c000030180

def z526 : W := mkw 0x2110379340000000 0x042206f268000000 0x0000060300000000 0x000000c060000000

def z527 : W := mkw 0x030b1c001b061804 0x006163800360c300 0xd70f1e001f061c07 0x7ae1e3c003e0c380

def z528 : W := mkw 0x27efd4da96d74000 0x04fdfa9b52dae800 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z529 : W := mkw 0x00020804380490e0 0x000041008700921c 0xe80e991cf80593e7 0xbd01d3239f00b27c

def z530 : W := mkw 0x11103fa16928bfaf 0x222207f42d2517f5 0xf831ffe3e01fffff 0xdf063ffc7c03ffff

def z531 : W := mkw 0x17b91fb20fba1f17 0x82f723f641f743e2 0xdff11fe31ffa1f9e 0xfbfe23fc63ff43f3

def z532 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0xc8c019e018e593e6 0xb918033c031cb27c

def z533 : W := mkw 0x01001c0009001804 0x0020038001200300 0x470018001f000000 0x28e0030003e00000

def z534 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0xdff018e01ff80004 0xfbfe031c03ff0000

def z535 : W := mkw 0x29103fffe82092e2 0x452207fffd04125c 0x60001fffe00013e2 0x0c0003fffc00027c

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0x9830000000180004 0xd306000000030000

def z537 : W := mkw 0x21103fdfc9001854 0x842207fbf920030a 0x60001fffe0001c7a 0x0c0003fffc00038f

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x8031e00000000001 0xd0063c0000000000

def z539 : W := mkw 0x17ffffa17fffffaf 0x22fffff42ffffff5 0xffffffe3ffffffff 0xfffffffc7fffffff

def z540 : W := mkw 0x2fffffffd8651242 0x45fffffffb0ca248 0xe7fffffff8e00003 0xfcffffffff1c0000

def z541 : W := mkw 0x06efc8041ed75040 0x00ddf90083daea08 0xfffff81c1ffff067 0xffffff0383fffe0c

def z542 : W := mkw 0x2956bffff86592e2 0x452ad7ffff0cb25c 0xe8ce9ffff8e593e7 0xbd19d3ffff1cb27c

def z543 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0xe7cf1eff00000003 0x7cf9e3dfe0000000

def z544 : W := mkw 0x06edc00000000000 0x00ddb80000000000 0x07ce000000000000 0x20f9c00000000000

def z545 : W := mkw 0x15f49fe88db81f07 0x02be93fd11b703e0 0xfffe9ffcfff81f87 0xffffd3ff9fff03f0

def z546 : W := mkw 0x06a9400006924000 0x00d5280000d24800 0x9ff160001ffa6004 0xf3fe2c0003ff4c00

def z547 : W := mkw 0x37eddcfa8db01a07 0x06fdbb9f51b60340 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z548 : W := mkw 0x06edc00004d14000 0x00ddb800009a2800 0x8fffe00000f9e001 0xf1fffc00001f3c00

def z549 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x57301fe007181f82 0x4ae603fc00e303f0

def z550 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x600f1e1f00061c7b 0x0c01e3c3e000c38f

def z551 : W := mkw 0x0010230140082508 0x20020460280104a1 0x0000060300000c18 0x000000c060000183

def z552 : W := mkw 0x15f69fa01dfd1f07 0x02bed3f403bfa3e0 0xdffe9fe01ffd9f87 0xfbffd3fc03ffb3f0

def z553 : W := mkw 0x1fff9ffebfff9ff7 0xc3fff3ffd7fff3fe 0xffff9fffffff9fff 0xfffff3fffffff3ff

def z554 : W := mkw 0x0100140000000000 0x0020028000000000 0xc7001e0000000002 0x78e003c000000000

def z555 : W := mkw 0x17bb3fb77fbebfff 0xa2f767f6eff7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z556 : W := mkw 0x030b1c163b0698f4 0x80616382c760d31e 0xff0f9f1fff079fff 0xffe1f3e3ffe0f3ff

def z557 : W := mkw 0x06efe00176d7e0a8 0x20ddfc002edafc15 0xbfffe003ffffe07d 0xf7fffc007ffffc0f

def z558 : W := mkw 0x37ffffffdfbe1f57 0x86fffffffbf7c3ea 0xfffffffffffe1fff 0xffffffffffffc3ff

def z559 : W := mkw 0x00000000200080a0 0x0000000004001014 0xb831e100e01ff3e7 0xd7063c201c03fe7c

def z560 : W := mkw 0x27fff7dbf6dfe5a8 0x24fffefb7edbfcb5 0xffffffffffffffff 0xffffffffffffffff

def z561 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x07cfe0001fe7e001 0x20f9fc0003fcfc00

def z562 : W := mkw 0x27efd4da96d74000 0x04fdfa9b52dae800 0xdffff8fc1fffe005 0xfbffff1f83fffc00

def z563 : W := mkw 0x0000080409001854 0x800001008120030a 0x0000000000001c78 0x000000000000038f

def z564 : W := mkw 0x234df45bc0000000 0x0469be8b78000000 0xe70ffe1fe0000003 0x7ce1ffc3fc000000

def z565 : W := mkw 0x0000000004900000 0x0000000000920000 0x180000001ff80004 0x0300000003ff0000

def z566 : W := mkw 0x0044804880000000 0x0008900910000000 0x00c081e0e0000000 0x8018103c1c000000

def z567 : W := mkw 0x000208043b0ebdfc 0xa00041008761d7bf 0x180000001f1ffffc 0x0300000003e3ffff

def z568 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9ffe00001ff80004 0xf3ffc00003ff0000

def z569 : W := mkw 0x0844806880610202 0x4108900d100c2040 0x00c000e000e00000 0x0018001c001c0000

def z570 : W := mkw 0x27efdcde9b061854 0x84fdfb9bd360c30a 0xf7cf1eff1f061c7f 0x7ef9e3dfe3e0c38f

def z571 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x08c081e0f8e593e4 0x8118103c1f1cb27c

def z572 : W := mkw 0x15b21fa41fbe1f57 0x82b643f483f7c3ea 0xdff01fe01ffe1ffe 0xfbfe03fc03ffc3ff

def z573 : W := mkw 0x031b3f175b0e3d5c 0xa06367e2eb61c7ab 0xf73f7e1f1f1e7c7f 0x7ee7efc3e3e3cf8f

def z574 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x38000703e01ffffe 0x070000e07c03ffff

def z575 : W := mkw 0x0309141200000000 0x0061228240000000 0x0701060300000000 0x40e020c060000000

def z576 : W := mkw 0x031937136008a5a8 0x206326e26c0114b5 0xff3fff1fe01fffff 0xffe7ffe3fc03ffff

def z577 : W := mkw 0x07bb1f961b061854 0x80f763f2c360c30a 0xf7ff1fff1f061c7f 0xfeffe3ffe3e0c38f

def z578 : W := mkw 0x2fefdcfe98651242 0x45fdfb9fd30ca248 0x47ce18fc18e00000 0x28f9c31f831c0000

def z579 : W := mkw 0x01001c1609001854 0x80200382c120030a 0xf0011e1f00061c7f 0x5e0023c3e000c38f

def z580 : W := mkw 0x15b0378145982d0d 0x22b606f028b305a1 0x17316603071a6c18 0x42e62cc060e34d83

def z581 : W := mkw 0x1fffdfecbfffdfe7 0x43fffbfd97fffbfc 0xfffffffcffffffe7 0xffffffff9ffffffc

def z582 : W := mkw 0x000208041b061854 0x800041008360c30a 0xf00e181c1f061c7f 0x3e01c30383e0c38f

def z583 : W := mkw 0x020b08041b061854 0x804161008360c30a 0x970f00001f061c7d 0x72e1e00003e0c38f

def z584 : W := mkw 0x1846886cbdfd9fe7 0x4308d10d97bfb3fc 0xf8ce99fcfffd9fe7 0xbf19d33f9fffb3fc

def z585 : W := mkw 0x1de69cecbdf59ae7 0x43bcd39d97beb35c 0xefce99fcffe593e7 0xbdf9d33f9ffcb27c

def z586 : W := mkw 0x000020016000a0a8 0x200004002c001415 0xa801e103e007f3ff 0x95003c207c00fe7f

def z587 : W := mkw 0x234ffc5fdb061854 0x8469ff8bfb60c30a 0xf70ffe1fff061c7f 0x7ee1ffc3ffe0c38f

def z588 : W := mkw 0x000020016000a0a8 0x200004002c001415 0x0000e000e001e000 0x00001c001c003c00

def z589 : W := mkw 0x06fde30140000000 0x00dfbc6028000000 0xa7ffe703e0000003 0xf4fffce07c000000

def z590 : W := mkw 0x0309141203020814 0x8061228240604102 0xb701060307061c7f 0x56e020c060e0c38f

def z591 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0xa8008100f8e593e7 0x950010201f1cb27c

def z592 : W := mkw 0x0800086ca82092e2 0x4100010d9504125c 0xe80099fce00593e7 0x9d00133f9c00b27c

def z593 : W := mkw 0x05b01f8009001804 0x00b603f001200300 0xd7f01fe01f001c06 0xfafe03fc03e00380

def z594 : W := mkw 0x08102b6de828b7ea 0x6102056dbd0516fd 0xf831ffffe01fffff 0xdf063ffffc03ffff

def z595 : W := mkw 0x034fdc161b475854 0x8069fb82c368eb0a 0xf70ffe1f1f07fc7f 0x7ee1ffc3e3e0ff8f

def z596 : W := mkw 0x0309141203020814 0x8061228240604102 0x0700000007000000 0x00e0000000e00000

def z597 : W := mkw 0x0002000036dfe5a8 0x2000400006dbfcb5 0x180000001ffffffc 0x0300000003ffffff

def z598 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x8fce80001fe58005 0xb1f9d00003fcb000

def z599 : W := mkw 0x04e4c00000000000 0x009c980000000000 0x00f0e00000000000 0x801e1c0000000000

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x88c0000018e00004 0xb1180000031c0000

def z601 : W := mkw 0x0044804880000000 0x0008900910000000 0x40ce18fc00000000 0x2819c31f80000000

def z602 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x670f181f1f060079 0x2ce1e303e3e0c00f

def z603 : W := mkw 0x05a0148000000000 0x00b4029000000000 0x47c018e000000000 0x28f8031c00000000

def z604 : W := mkw 0x031b3f177b0ebdfc 0xa06367e2ef61d7bf 0xf70f1f1fff061fff 0x7ee1e3e3ffe0c3ff

def z605 : W := mkw 0x07ffff177fdffdfc 0xa0ffffe2effbffbf 0xffffff1fffffffff 0xffffffe3ffffffff

def z606 : W := mkw 0x225de35bc0000000 0x044bbc6b78000000 0xa03fe71fe0000003 0xd407fce3fc000000

def z607 : W := mkw 0x0010230140082508 0x20020460280104a1 0x9831e603001fec1d 0xd3063cc06003fd83

def z608 : W := mkw 0x224dc05a80000000 0x0449b80b50000000 0x000e001c00000000 0x0001c00380000000

def z609 : W := mkw 0x0209000000000000 0x0041200000000000 0x870f000000000001 0x70e1e00000000000

def z610 : W := mkw 0x24b0638140000000 0x04960c7028000000 0x0030600000000000 0x00060c0000000000

def z611 : W := mkw 0x0df69fecb86592e2 0x41bed3fd970cb25c 0xeffe9ffcf8e593e7 0xfdffd3ff9f1cb27c

def z612 : W := mkw 0x26ffe3c9d6d74000 0x04dffc793adae800 0x9fffe1e0ffffe005 0xf3fffc3c1ffffc00

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000041067 0x140000000000820c

def z614 : W := mkw 0x0110178000000000 0x002202f000000000 0x40001fe000000002 0x080003fc00000000

def z615 : W := mkw 0x030b3c177b06b8fc 0xa0616782ef60d71f 0xf70ffe1fff07fc7f 0x7ee1ffc3ffe0ff8f

def z616 : W := mkw 0x2000205bc0000000 0x0400040b78000000 0x2000001fe0000000 0x04000003fc000000

def z617 : W := mkw 0x01001c1609001854 0x80200382c120030a 0xf7001e1f1f001c7e 0x7ee003c3e3e0038f

def z618 : W := mkw 0x0effeb6dfefff7ea 0x61dffd6dbfdffefd 0xffffffffffffffff 0xffffffffffffffff

def z619 : W := mkw 0x07edd41200000000 0x00fdba8240000000 0xe7fffe1f00000003 0xfcffffc3e0000000

def z620 : W := mkw 0x04e6c00014d54000 0x009cd800029aa800 0x88fee00018fde005 0xb11fdc00031fbc00

def z621 : W := mkw 0x020b000016d74000 0x0041600002dae800 0x9f0f00001fffe005 0x73e1e00003fffc00

def z622 : W := mkw 0x05b0178000000000 0x00b602f000000000 0x0730060000000000 0x40e600c000000000

def z623 : W := mkw 0x030b141612060050 0x80616282c240c00a 0xe70f1e1f0006007b 0x7ce1e3c3e000c00f

def z624 : W := mkw 0x03091c1209001804 0x0061238241200300 0xf70f1e1f1f001c07 0x7ee1e3c3e3e00380

def z625 : W := mkw 0x07efd41217d74814 0x80fdfa8242fae902 0x9fffe6031fffec1d 0xf3fffcc063fffd83

def z626 : W := mkw 0x0846884cb84590e0 0x4108d1099708b21c 0xe00e981cf8059067 0x3c01d3039f00b20c

def z627 : W := mkw 0x04a0000004900000 0x0094000000920000 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z628 : W := mkw 0x100208241fbe1f57 0x8200410483f7c3ea 0x180000001ffe1ffc 0x0300000003ffc3ff

def z629 : W := mkw 0x2cf4e3e9e06182a2 0x459e9c7d3c0c3054 0x08f0e1e0e0e18380 0x811e1c3c1c1c3070

def z630 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x2830e703e019fffa 0x85061ce07c033fff

def z631 : W := mkw 0x1df49fe8adf99fa7 0x43be93fd15bf33f4 0xdff09fe0fff99f86 0xfbfe13fc1fff33f0

def z632 : W := mkw 0x15b03fa16db8bfaf 0x22b607f42db717f5 0xdff0ffe0fff9ff86 0xfbfe1ffc1fff3ff0

def z633 : W := mkw 0x11101fa009281f07 0x022203f4012503e0 0xc8c01fe018e01f86 0xb91803fc031c03f0

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0008100e0000003 0x940010201c000000

def z635 : W := mkw 0x0856ab6df86592e2 0x410ad56dbf0cb25c 0xe8fffffff8e593e7 0xfd1fffffff1cb27c

def z636 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x2831e103e01fe3f9 0x85063c207c03fc7f

def z637 : W := mkw 0x020b000012060000 0x004160000240c000 0xb70f06031f061c7f 0x76e1e0c063e0c38f

def z638 : W := mkw 0x37fdfffbedb8bfaf 0x26ffbfff7db717f5 0xffffffffffffffff 0xffffffffffffffff

def z639 : W := mkw 0x15b0178005980d05 0x02b602f000b301a0 0x9f30070007181f86 0xd3e600e000e303f0

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000061c7c 0x020000000000c38f

def z641 : W := mkw 0x14b00ba00db81f07 0x0296017401b703e0 0x18f001e01ff81f84 0x831e003c03ff03f0

def z642 : W := mkw 0x024fc00012474000 0x0049f8000248e800 0x000e000000000000 0x0001c00000000000

def z643 : W := mkw 0x1df69fec9dfd1f47 0x43bed3fd93bfa3e8 0xdffe1ffc1ff81f86 0xfbffc3ff83ff03f0

def z644 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x1fce00001fffe004 0x23f9c00003fffc00

def z645 : W := mkw 0x0100140001000804 0x0020028000200100 0x1700060007000c00 0x42e000c000e00180

def z646 : W := mkw 0x0002082418241242 0x0000410483048248 0xe8ce19fc18e413e7 0xbd19c33f831c827c

def z647 : W := mkw 0x11001c200db81f07 0x0220038401b703e0 0xdf001e001ff81f86 0x7be003c003ff03f0

def z648 : W := mkw 0x000020016000a0a8 0x200004002c001415 0xb001e603e007fc7f 0x56003cc07c00ff8f

def z649 : W := mkw 0x37b9779345980d05 0x06f72ef268b301a0 0x1731660307180c00 0x42e62cc060e30180

def z650 : W := mkw 0x19569fecb96d9fe7 0x432ad3fd972db3fc 0xe8ce9ffcf8e59fe7 0xbd19d3ff9f1cb3fc

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001060300000003 0x540020c060000000

def z652 : W := mkw 0x000020016000a0a8 0x200004002c001415 0x20000003e0000078 0x040000007c00000f

def z653 : W := mkw 0x27fdf7dbe000a0a8 0x24ffbefb7c001415 0xe7ffffffe007e07b 0xfcfffffffc00fc0f

def z654 : W := mkw 0x031b3f175b061854 0x806367e2eb60c30a 0xf73fff1fff061c7f 0xfee7ffe3ffe0c38f

def z655 : W := mkw 0x00448048a00080a0 0x0008900914001014 0xe8ce99fce00593e7 0xbd19d33f9c00b27c

def z656 : W := mkw 0x0846806cb06582e2 0x4108d00d960cb05c 0x28ce81fce0e583e1 0x8519d03f9c1cb07c

def z657 : W := mkw 0x07ab5c161f965854 0x80f56b82c3f2cb0a 0xf73f7e1f1f1e7c7f 0x7ee7efc3e3e3cf8f

def z658 : W := mkw 0x24f4e3c9c0000000 0x049e9c7938000000 0xa0f1e7e3e0000003 0xd41e3cfc7c000000

def z659 : W := mkw 0x2ffffffffb679af6 0xc5ffffffff6cf35e 0xffffffffffe79fff 0xfffffffffffcf3ff

def z660 : W := mkw 0x24e4c0c880000000 0x049c981910000000 0x00c000e000000000 0x0018001c00000000

def z661 : W := mkw 0x15a0148005900805 0x02b4029000b20100 0x0700000007000000 0x00e0000000e00000

def z662 : W := mkw 0x0eefc86c9ef75242 0x41ddf90d93deea48 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z663 : W := mkw 0x0010230140082508 0x20020460280104a1 0x98316703001a7f9e 0xd3062ce060034ff3

def z664 : W := mkw 0x15b017a005b80f07 0x02b602f400b701e0 0x1ff007e007f80f80 0xc3fe00fc00ff01f0

def z665 : W := mkw 0x35b03ffbcdb81f07 0x06b607ff79b703e0 0xfff01ffffff81f86 0xfffe03ffffff03f0

def z666 : W := mkw 0x1df6bfedfdfdbfef 0x63bed7fdbfbfb7fd 0xffffffffffffffff 0xffffffffffffffff

def z667 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x00ce000018e00000 0x2019c000031c0000

def z668 : W := mkw 0x0309141200000000 0x0061228240000000 0xf70f1e1f00061c7f 0x7ee1e3c3e000c38f

def z669 : W := mkw 0x05b01fa008201202 0x00b603f401040240 0xcff01fe018e01386 0xf9fe03fc031c0270

def z670 : W := mkw 0x07efdc161b061854 0x80fdfb82c360c30a 0xf7fffe1f1f061c7f 0xfeffffc3e3e0c38f

def z671 : W := mkw 0x024fe0017247e0a8 0x2049fc002e48fc15 0x200fe003e007e079 0x0401fc007c00fc0f

def z672 : W := mkw 0x0eefc86cbef7d2e2 0x41ddf90d97defa5c 0xefce99fcffe593e7 0xbdf9d33f9ffcb27c

def z673 : W := mkw 0x14b023a164b8a7ab 0x229604742c9714f5 0xb8f1e7e3e0ffffff 0xd71e3cfc7c1fffff

def z674 : W := mkw 0x27fdf7dbe008a5a8 0x24ffbefb7c0114b5 0xefffffffe019e383 0xfdfffffffc033c70

def z675 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x17ff60001ffa6000 0x62ffec0003ff4c00

def z676 : W := mkw 0x06a9400000000000 0x00d5280000000000 0x0731600000000000 0x40e62c0000000000

def z677 : W := mkw 0x04e6800014d50000 0x009cd000029aa000 0x9ffe80001ffd8005 0xf3ffd00003ffb000

def z678 : W := mkw 0x15b037816598adad 0x22b606f02cb315b5 0xbf31e703e71fffff 0xd7e63ce07ce3ffff

def z679 : W := mkw 0x000208041b061854 0x800041008360c30a 0x000000001f000000 0x0000000003e00000

def z680 : W := mkw 0x06edc00000000000 0x00ddb80000000000 0x9fffe000001fe005 0xf3fffc000003fc00

def z681 : W := mkw 0x15b01fa00db01a07 0x02b603f401b60340 0xc7f01fe01fe00002 0xf8fe03fc03fc0000

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0x1001060300020c18 0x420020c060004183

def z683 : W := mkw 0x00000820282092a2 0x0000010405041254 0xe8c099e0f8e593e7 0xbd18133c1f1cb27c

def z684 : W := mkw 0x000000002000a0a8 0x2000000004001415 0x000000000007e078 0x000000000000fc0f

def z685 : W := mkw 0x27efdcde9b061854 0x84fdfb9bd360c30a 0x47ce18fc1f000000 0x28f9c31f83e00000

def z686 : W := mkw 0x00102b216828b7aa 0x200205642d0516f5 0xf8f1ffe3f8ffffff 0xff1e3ffc7f1fffff

def z687 : W := mkw 0x0b4f9c5ebb4798f4 0xc169f38bd768f31e 0xf70f9e1fff079c7f 0x7ee1f3c3ffe0f38f

def z688 : W := mkw 0x0010230140000000 0x0002046028000000 0x20000703e0000002 0x040000e07c000000

def z689 : W := mkw 0x04b0030004980500 0x00960060009300a0 0x9ff007001ff81f86 0xf3fe00e003ff03f0

def z690 : W := mkw 0x09469c7eb9659af6 0xc128d38fd72cb35e 0xe8ce9ffff8e59fff 0xbd19d3ffff1cb3ff

def z691 : W := mkw 0x030b141212060000 0x006162824240c000 0xf70f1e1f1f060007 0x7ee1e3c3e3e0c000

def z692 : W := mkw 0x04b0038000000000 0x0096007000000000 0x00f001e000000000 0x801e003c00000000

def z693 : W := mkw 0x17fddfa00db81f07 0x02ffbbf401b703e0 0xdfffffe01ff81f87 0xfbfffffc03ff03f0

def z694 : W := mkw 0x14b023a164b8a7ab 0x229604742c9714f5 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z695 : W := mkw 0x0800086ca82092e2 0x4100010d9504125c 0xe8c019fcf8e013e6 0xbd18033f9f1c027c

def z696 : W := mkw 0x024dc00000000000 0x0049b80000000000 0x000fe00000000001 0x0001fc0000000000

def z697 : W := mkw 0x27fdf7dbe00080a0 0x04ffbefb7c001014 0xefffffffe00593e7 0xfdfffffffc00b27c

def z698 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x3031e603e01fec79 0x46063cc07c03fd8f

def z699 : W := mkw 0x11101fa009281f07 0x022203f4012503e0 0xd8301fe000181f86 0xdb0603fc000303f0

def z700 : W := mkw 0x04e6c00016d74000 0x009cd80002dae800 0x18f0e0001fffe004 0x831e1c0003fffc00

def z701 : W := mkw 0x03193713430a2d1c 0xa06326e2686145a3 0x17316603071a6c18 0x42e62cc060e34d83

def z702 : W := mkw 0x17b95fa00fba5f07 0x02f72bf401f74be0 0xdff17fe01ffa7f86 0xfbfe2ffc03ff4ff0

def z703 : W := mkw 0x024fc00016d74000 0x0049f80002dae800 0x180fe0001fffe005 0x0301fc0003fffc00

def z704 : W := mkw 0x08568b6cb86d97e2 0x410ad16d970db2fc 0xf8fe9ffcf8fd9fe7 0xff1fd3ff9f1fb3fc

def z705 : W := mkw 0x0000000004d14000 0x00000000009a2800 0x0800000000f9e000 0x01000000001f3c00

def z706 : W := mkw 0x17bb1f961f9e1d55 0x82f763f2c3f3c3aa 0xf73f1e1f1f1e1c7f 0x7ee7e3c3e3e3c38f

def z707 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9fffe0001ffffc7d 0xf3fffc0003ffff8f

def z708 : W := mkw 0x020b000016d74000 0x0041600002dae800 0x9f3fe0001fffe005 0xf3e7fc0003fffc00

def z709 : W := mkw 0x15a03ca16db0baaf 0x22b407942db61755 0x67c1f8e3ffe7e079 0x2cf83f1c7ffcfc0f

def z710 : W := mkw 0x0b4d947aa3638ab6 0xc169b28f546c7156 0x1fc187e3e7e38f98 0xc3f830fc7cfc71f3

def z711 : W := mkw 0x0b0b1c363b679af6 0xc1616386c76cf35e 0x1f0106031fe79ffc 0x43e020c063fcf3ff

def z712 : W := mkw 0x27fdf7dbc7924814 0x84ffbefb78f24902 0xf7ffffffe71a6c1b 0xfefffffffce34d83

def z713 : W := mkw 0x211237dbd6d74000 0x042246fb7adae800 0x78001fffffffe006 0x0f0003fffffffc00

def z714 : W := mkw 0x27fdf7dbc4d14000 0x04ffbefb789a2800 0xffffffffe0ffe007 0xfffffffffc1ffc00

def z715 : W := mkw 0x135fdfa01b6f5f07 0x026bfbf4036debe0 0x400fffe00007ff83 0x0801fffc0000fff0

def z716 : W := mkw 0x06ab400016d74000 0x00d5680002dae800 0x9f3f60001fffe005 0x73e7ec0003fffc00

def z717 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0x67ce19fce0000002 0x2cf9c33f9c000000

def z718 : W := mkw 0x37fdf7dbc5980d05 0x06ffbefb78b301a0 0xfffffffffff80c07 0xffffffffffff0180

def z719 : W := mkw 0x1df697ccb5dd8de5 0x43bed2f996bbb1bc 0x373e861ce71d8c61 0x46e7d0c39ce3b18c

def z720 : W := mkw 0x034d945a80000000 0x0069b28b50000000 0xe7ce99fce0000003 0xbcf9d33f9c000000

def z721 : W := mkw 0x15b01fa40db81f47 0x02b603f481b703e8 0xfff01ffc1ff81fe6 0xfffe03ff83ff03fc

def z722 : W := mkw 0x16bb03b616be0753 0x82d76076c2d7c0ea 0x28ff01ff00fe03f9 0x851fe03fe01fc07f

def z723 : W := mkw 0x06ab400016d74000 0x00d5680002dae800 0x9f31e0001fffe005 0xd3e63c0003fffc00

def z724 : W := mkw 0x324de87bcdb81f07 0x0649bd0f79b703e0 0x380fe01ffff81f85 0x0701fc03ffff03f0

def z725 : W := mkw 0x0856ab6dd86d374a 0x610ad56dbb0da6e9 0x50ff7eff18fa6c18 0x6a1fefdfe31f4d83

def z726 : W := mkw 0x27fdf7dbc69a6508 0x24ffbefb78d34ca1 0xf7ffffffe71a6c1b 0xfefffffffce34d83

def z727 : W := mkw 0x06edc00004900000 0x00ddb80000920000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z728 : W := mkw 0x0044804880000000 0x0008900910000000 0x600e99fce0000003 0x0c01d33f9c000000

def z729 : W := mkw 0x27edd4daa008a5a8 0x24fdba9b540114b5 0x5fce18fc001ffffc 0x2bf9c31f8003ffff

def z730 : W := mkw 0x180208243dfdbfef 0x6300410487bfb7fd 0x180000001ffffffc 0x0300000003ffffff

def z731 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z732 : W := mkw 0x05a01c200db01a06 0x00b4038401b60340 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z733 : W := mkw 0x0046886898651202 0x0008d10d130ca240 0xe8ce99fcf8e59387 0xbd19d33f9f1cb270

def z734 : W := mkw 0x0fefdc7e9ff75a56 0xc1fdfb8fd3feeb4a 0x47ce18fc1fe00000 0x28f9c31f83fc0000

def z735 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0xdff019e01ff81386 0xfbfe033c03ff0270

def z736 : W := mkw 0x0802086cb82492e2 0x4100410d9704925c 0xe8ce19fcf8e413e7 0xbd19c33f9f1c827c

def z737 : W := mkw 0x37b9779344980501 0x06f72ef2689300a0 0x0731660300180000 0x40e62cc060030000

def z738 : W := mkw 0x04e4804884900000 0x009c900910920000 0xfffe99fcfff80007 0xffffd33f9fff0000

def z739 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf70ffe1f1f07fc7f 0x7ee1ffc3e3e0ff8f

def z740 : W := mkw 0x234df45bc0000000 0x0469be8b78000000 0xe7cfffffe0000003 0xfcf9fffffc000000

def z741 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xeffffffff8e00007 0xfdffffffff1c0000

def z742 : W := mkw 0x07edd45a80000000 0x00fdba8b50000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z743 : W := mkw 0x15b017a004b80703 0x02b602f4009700e0 0xdff01fe01ff80386 0xfbfe03fc03ff0070

def z744 : W := mkw 0x06efc00416d74050 0x80ddf80082dae80a 0x9fffe0001fffe07d 0xf3fffc0003fffc0f

def z745 : W := mkw 0x03091c160b021854 0x80612382c160430a 0xf70f1e1f07021c7b 0x7ee1e3c3e0e0438f

def z746 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf70e1e1f1f001c7e 0x7ee1c3c3e3e0038f

def z747 : W := mkw 0x08468824386592e2 0x4108d104870cb25c 0x08c0800018e593e4 0x81181000031cb27c

def z748 : W := mkw 0x37b97793479a0d15 0x86f72ef268f341a2 0x17316603071a0c18 0x42e62cc060e34183

def z749 : W := mkw 0x05e4dc160dd15854 0x80bc9b82c1ba2b0a 0x68f0fe1f00f9fc7a 0x8d1e1fc3e01f3f8f

def z750 : W := mkw 0x0144945a80000000 0x0028928b50000000 0xe0ce9fffe0000003 0xbc19d3fffc000000

def z751 : W := mkw 0x06ab000016960000 0x00d5600002d2c000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z752 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9fffe1001ffff387 0xf3fffc2003fffe70

def z753 : W := mkw 0x0846886cb9659ae6 0x4108d10d972cb35c 0xf8ce99fcffe59fe7 0xbf19d33f9ffcb3fc

def z754 : W := mkw 0x080208243cf592e2 0x41004104879eb25c 0x180000001ffd93e4 0x0300000003ffb27c

def z755 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff11fe31ffa1f9e 0xfbfe23fc63ff43f3

def z756 : W := mkw 0x25f4b7dbc0000000 0x04be96fb78000000 0xe7fe9fffe0000003 0xfcffd3fffc000000

def z757 : W := mkw 0x235df7dbc0000000 0x046bbefb78000000 0x600e1fffe0000002 0x0c01c3fffc000000

def z758 : W := mkw 0x37fdf7dbc5982d0d 0x26ffbefb78b305a1 0xf7ffffffe71a6c1b 0xfefffffffce34d83

def z759 : W := mkw 0x27fdf7dbc0080500 0x04ffbefb780100a0 0xffffffffe01fff87 0xfffffffffc03fff0

def z760 : W := mkw 0x06efc04896d74000 0x00ddf80912dae800 0xbfffe01cffffe005 0xf7fffc039ffffc00

def z761 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xfffff81c1fffe007 0xffffff0383fffc00

def z762 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfffe1ffc1ff81f87 0xffffc3ff83ff03f0

def z763 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7ffffffe006007b 0xfcfffffffc00c00f

def z764 : W := mkw 0x15b03fa14db83f0f 0x22b607f429b707e1 0xdff07fe01ff87f86 0xfbfe0ffc03ff0ff0

def z765 : W := mkw 0x06ffe30176dfe5a8 0x20dffc602edbfcb5 0x27ce0703ffe01ffa 0x24f9c0e07ffc03ff

def z766 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x1ff007e01ff81f84 0xc3fe00fc03ff03f0

def z767 : W := mkw 0x24f6ebcddb061854 0x849edd79bb60c30a 0x10f0e1e0ff061c7c 0x821e1c3c1fe0c38f

def z768 : W := mkw 0x0a4fa05ff247a0f8 0xe149f40bfe48f41f 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z769 : W := mkw 0x0846c86cb865d2e2 0x4108d90d970cba5c 0xe8cef9fcf8e5f3e7 0xbd19df3f9f1cbe7c

def z770 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8cf99fcf8e793e7 0xff19f33f9f1cf27c

def z771 : W := mkw 0x06fde349c0000000 0x00dfbc6938000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z772 : W := mkw 0x080208243a6792f2 0xc1004104874cf25e 0x0800000018e793fc 0x01000000031cf27f

def z773 : W := mkw 0x06efc01616d74050 0x80ddf802c2dae80a 0x9fffe01c1fffe005 0xf3fffc0383fffc00

def z774 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xbf31e703ff1fffff 0xf7e63ce07fe3ffff

def z775 : W := mkw 0x030b1c161b471854 0x80616382c368e30a 0xff0f1e1f1fe79c7f 0x7fe1e3c3e3fcf38f

def z776 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe0ce99fcf8e013e3 0xbc19d33f9f1c027c

def z777 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x17ffe0001fffe001 0x62fffc0003fffc00

def z778 : W := mkw 0x0846886c98651242 0x4108d10d930ca248 0xe8ce99fcf8e01387 0xbd19d33f9f1c0270

def z779 : W := mkw 0x04e6c00014d54000 0x009cd800029aa800 0x9ffee0001ffde005 0xf3ffdc0003ffbc00

def z780 : W := mkw 0x0846886cb865b2ea 0x6108d10d970cb65d 0xe8ce99fcf8e7f3ff 0xbd19d33f9f1cfe7f

def z781 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9fffe6001ffffc07 0xf3fffcc003ffff80

def z782 : W := mkw 0x11103fb76928bfff 0xa22207f6ed2517ff 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z783 : W := mkw 0x15b05fa00db85f07 0x02b60bf401b70be0 0xdff07fe01ff87f86 0xfbfe0ffc03ff0ff0

def z784 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff01fe01ffe1ffe 0xfbfe03fc03ffc3ff

def z785 : W := mkw 0x0309141203020814 0x8061228240604102 0xf70f1e1f07061c7f 0x7ee1e3c3e0e0c38f

def z786 : W := mkw 0x0a4fc05eb247c0f0 0xc149f80bd648f81e 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z787 : W := mkw 0x17b93793479a2d1d 0xa2f726f268f345a3 0x17316603071a6c18 0x42e62cc060e34d83

def z788 : W := mkw 0x080208243a6792e2 0x41004104874cf25c 0x180000001fe793e4 0x0300000003fcf27c

def z789 : W := mkw 0x180208243fffdfe7 0x4300410487fffbfc 0x180000001fffffe4 0x0300000003fffffc

def z790 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff019e01ff80384 0xfbfe033c03ff0070

def z791 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x5ff019e01ff81f84 0xabfe033c03ff03f0

def z792 : W := mkw 0x15b01fa40db81f57 0x82b603f481b703ea 0xdff01fe01ff81ffe 0xfbfe03fc03ff03ff

def z793 : W := mkw 0x27fdf7dbc0414000 0x04ffbefb78082800 0xe7ffffffe001e003 0xfcfffffffc003c00

def z794 : W := mkw 0x2154b7dbc0000000 0x042a96fb78000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z795 : W := mkw 0x15b03fa14db83f0f 0x22b607f429b707e1 0xfff17fe31ffe7fff 0xfffe2ffc63ffcfff

def z796 : W := mkw 0x04e4c00004d14000 0x009c9800009a2800 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z797 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x1800000018fff3e4 0x03000000031ffe7c

def z798 : W := mkw 0x030b141212060000 0x006162824240c000 0xf70f1e1f1f061c7f 0x7ee1e3c3e3e0c38f

def z799 : W := mkw 0x27fdf7dbc0080500 0x04ffbefb780100a0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z800 : W := mkw 0x0802082439659af6 0xc1004104872cb35e 0x0800000018e59ffc 0x01000000031cb3ff

def z801 : W := mkw 0x0ea9486caeb2d2e2 0x41d5290d95d65a5c 0x773179fce71a73e2 0x4ee62f3f9ce34e7c

def z802 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x5ff01ee01ff81f84 0x6bfe03dc03ff03f0

def z803 : W := mkw 0x06efc04896d74000 0x00ddf80912dae800 0xdffff8fc1fffe005 0xfbffff1f83fffc00

def z804 : W := mkw 0x24f4e3c9c0000000 0x049e9c7938000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z805 : W := mkw 0x0044804880000000 0x0008900910000000 0xf0cf9fffe0061c7f 0xfe19f3fffc00c38f

def z806 : W := mkw 0x03091c1609001854 0x80612382c120030a 0xf70f1e1f1f001c7f 0x7ee1e3c3e3e0038f

def z807 : W := mkw 0x231937dbc0000000 0x046326fb78000000 0x670e1fffe0000002 0x2ce1c3fffc000000

def z808 : W := mkw 0x024d804880000000 0x0049b00910000000 0xe7cf99fce0000003 0xfcf9f33f9c000000

def z809 : W := mkw 0x27edf4dbc0000000 0x04fdbe9b78000000 0x67ce18ffe0000000 0x2cf9c31ffc000000

def z810 : W := mkw 0x15a01ca00db81f07 0x02b4039401b703e0 0xdff018e01ff81f84 0xfbfe031c03ff03f0

def z811 : W := mkw 0x24f4e3c9e4d9e5a8 0x249e9c793c9b3cb5 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z812 : W := mkw 0x06efc04896d74000 0x00ddf80912dae800 0x9fffe1e0ffffe005 0xf3fffc3c1ffffc00

def z813 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0xa800000018e593e7 0x15000000031cb27c

def z814 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xc7f01fe01fe01f82 0xf8fe03fc03fc03f0

def z815 : W := mkw 0x15f497c885980d05 0x02be92f910b301a0 0xf7fe9ffce7180c03 0xfeffd3ff9ce30180

def z816 : W := mkw 0x2fbb7fb7786592e2 0x45f76ff6ef0cb25c 0x0f31660318e593e4 0x41e62cc0631cb27c

def z817 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xc7fefffce0000002 0xf8ffdfff9c000000

def z818 : W := mkw 0x26efc0c896d74000 0x04ddf81912dae800 0x9fffe0e01fffe005 0xf3fffc1c03fffc00

def z819 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x60ce99fcf8e593e3 0x2c19d33f9f1cb27c

def z820 : W := mkw 0x15b03fa14db83f0f 0x22b607f429b707e1 0xdff01fe31ff81f9e 0xfbfe03fc63ff03f3

def z821 : W := mkw 0x04a2000016d74000 0x0094400002dae800 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z822 : W := mkw 0x035db75bc0000000 0x006bb6eb78000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z823 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe0ce19fcf8e413e7 0x3c19c33f9f1c827c

def z824 : W := mkw 0x08020824386d97e2 0x41004104870db2fc 0x1800000018fd9fe4 0x03000000031fb3fc

def z825 : W := mkw 0x0b0b1c361b671a56 0xc1616386c36ce34a 0xf70f1e1f1fe61c7f 0x7ee1e3c3e3fcc38f

def z826 : W := mkw 0x27fdf7dbc6924000 0x04ffbefb78d24800 0xe7ffffffe7000003 0xfcfffffffce00000

def z827 : W := mkw 0x15b01fa00db01a07 0x02b603f401b60340 0xcff01fe01fe01386 0xf9fe03fc03fc0270

def z828 : W := mkw 0x08120b24386d97e2 0x41024164870db2fc 0x9830070018fd9fe6 0xd30600e0031fb3fc

def z829 : W := mkw 0x27b937dbc0000000 0x04f726fb78000000 0xe7ff1fffe0000003 0xfcffe3fffc000000

def z830 : W := mkw 0x235df7dbc0000000 0x046bbefb78000000 0xe70fffffe0000003 0x7ce1fffffc000000

def z831 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x770f1e1f1f021c7a 0x6ee1e3c3e3e0438f

def z832 : W := mkw 0x04e4c00004d14000 0x009c9800009a2800 0x0ff0e0001ff9e000 0xa1fe1c0003ff3c00

def z833 : W := mkw 0x180208243df59ae7 0x4300410487beb35c 0x080000001fe593e4 0x0100000003fcb27c

def z834 : W := mkw 0x235df7dbc0000000 0x046bbefb78000000 0xe03fffffe0000003 0xdc07fffffc000000

def z835 : W := mkw 0x08020824382492e2 0x410041048704925c 0x00000000180413e4 0x000000000300827c

def z836 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x1fff60001fffe004 0x63ffec0003fffc00

def z837 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x1800000018e79ffc 0x03000000031cf3ff

def z838 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8fe99fcf8fd93e7 0xff1fd33f9f1fb27c

def z839 : W := mkw 0x0846886cbb679af6 0xc108d10d976cf35e 0xf8cf9fffffe79fff 0xff19f3fffffcf3ff

def z840 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8ce9ffff8e59fff 0xbd19d3ffff1cb3ff

def z841 : W := mkw 0x27fdf7dbc2024000 0x04ffbefb78404800 0xe7ffffffe0026003 0xfcfffffffc004c00

def z842 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8fef9fcf8fdf3e7 0xbd1fdf3f9f1fbe7c

def z843 : W := mkw 0x15b01fa00db83f0f 0x22b603f401b707e1 0xdff01fe01ffa7f9e 0xfbfe03fc03ff4ff3

def z844 : W := mkw 0x030b141613060854 0x80616282c260c10a 0xb70f061f1f060c7d 0x76e1e0c3e3e0c18f

def z845 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x1ff1e0001fffe004 0xc3fe3c0003fffc00

def z846 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x68ce19fcf8e593e6 0x2d19c33f9f1cb27c

def z847 : W := mkw 0x0044804880000000 0x0008900910000000 0xe8ce99fce0058007 0xbd19d33f9c00b000

def z848 : W := mkw 0x0044804880000000 0x0008900910000000 0x40ce99fce0000000 0xa819d33f9c000000

def z849 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff01fe01fffff86 0xfbfe03fc03fffff0

def z850 : W := mkw 0x0a4fe04df247e0e8 0x6149fc09be48fc1d 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z851 : W := mkw 0x0044804880000000 0x0008900910000000 0xe8ce99fcf8e00007 0xbd19d33f9f1c0000

def z852 : W := mkw 0x14b00ba00cb81703 0x02960174019702e0 0xdff019e01ff81386 0xfbfe033c03ff0270

def z853 : W := mkw 0x27fdf7dbc6d34000 0x04ffbefb78da6800 0xffffffffe7fbe003 0xfffffffffcff7c00

def z854 : W := mkw 0x27fdf7dbc1000804 0x04ffbefb78200100 0xf7ffffffe7000c03 0xfefffffffce00180

def z855 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x370f061f1f061c7d 0x46e1e0c3e3e0c38f

def z856 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x0000000018e58060 0x00000000031cb00c

def z857 : W := mkw 0x27fdf7dbc1000814 0x84ffbefb78200102 0xe7ffffffe0000c1b 0xfcfffffffc000183

def z858 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0cf9fffe0000003 0xfc19f3fffc000000

def z859 : W := mkw 0x180208243cfd97e3 0x43004104879fb2fc 0x0800000018fd93e4 0x01000000031fb27c

def z860 : W := mkw 0x06edc04886924000 0x00ddb80910d24800 0xf7fff9fce71a6003 0xfeffff3f9ce34c00

def z861 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x570f1e1f1f061c7c 0x6ae1e3c3e3e0c38f

def z862 : W := mkw 0x06efc01616d74050 0x80ddf802c2dae80a 0xbfffe61f1ffffc7f 0xf7fffcc3e3ffff8f

def z863 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x57f01fe01ff81f82 0x6afe03fc03ff03f0

def z864 : W := mkw 0x27fdd7da80000000 0x04ffbafb50000000 0xe7fe9ffce0000003 0xfcffd3ff9c000000

def z865 : W := mkw 0x020b08041a061040 0x004161008340c208 0xf70f1e1f1f061c7f 0x7ee1e3c3e3e0c38f

def z866 : W := mkw 0x07fd97da80000000 0x00ffb2fb50000000 0xe7ff9fffe0000003 0xfcfff3fffc000000

def z867 : W := mkw 0x030b1c361b261a56 0x80616386c364c34a 0xff0f1e1f1fe61fff 0x7fe1e3c3e3fcc3ff

def z868 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xff0f9e1f1f079c7f 0xffe1f3c3e3e0f38f

def z869 : W := mkw 0x01021c1619041854 0x80204382c320830a 0xf70e1e1f1f041c7f 0x7ee1c3c3e3e0838f

def z870 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf73ffe1f1f061c7f 0xfee7ffc3e3e0c38f

def z871 : W := mkw 0x27b97793469a6508 0x24f72ef268d34ca1 0x17316603071a6c18 0x42e62cc060e34d83

def z872 : W := mkw 0x37fdf7dbc5900805 0x06ffbefb78b20100 0xe7ffffffe7000003 0xfcfffffffce00000

def z873 : W := mkw 0x225de35bc0000000 0x044bbc6b78000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z874 : W := mkw 0x27fdf7dbc4900000 0x04ffbefb78920000 0xffffffffffffe007 0xfffffffffffffc00

def z875 : W := mkw 0x0ce6c8243cf5d2e2 0x419cd904879eba5c 0x08f0e00018fdf3e4 0x811e1c00031fbe7c

def z876 : W := mkw 0x180208243fff9ff7 0xc300410487fff3fe 0x180000001fff9ffc 0x0300000003fff3ff

def z877 : W := mkw 0x26fde3dbc0000000 0x04dfbc7b78000000 0xe0fff9ffe0000003 0xbc1fff3ffc000000

def z878 : W := mkw 0x0846886cba67d2e2 0x4108d10d974cfa5c 0xe8ce99fcf8e7f3e7 0xbd19d33f9f1cfe7c

def z879 : W := mkw 0x031b3f177b0ebdfc 0xa06367e2ef61d7bf 0x4f3ef91cff19e380 0xa9e7df239fe33c70

def z880 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0fff9fce0000003 0xfc1fff3f9c000000

def z881 : W := mkw 0x04a0002004b00202 0x0094000400960040 0x9ff001e01ff80384 0xf3fe003c03ff0070

def z882 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfff11fe31ff81f87 0xfffe23fc63ff03f0

def z883 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7ce9fffe0000003 0xbcf9d3fffc000000

def z884 : W := mkw 0x024d805a80000000 0x0049b00b50000000 0xe0cf99ffe0000003 0xbc19f33ffc000000

def z885 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x1f3fe0001fffe005 0x43e7fc0003fffc00

def z886 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff11fe01ffe1f87 0xfbfe23fc03ffc3f0

def z887 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xffffffffe0180007 0xfffffffffc030000

def z888 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xf83fff1fe01fffff 0xff07ffe3fc03ffff

def z889 : W := mkw 0x14a008200db81f07 0x0294010401b703e0 0xdff019e01ff81f86 0xfbfe033c03ff03f0

def z890 : W := mkw 0x030b141613060854 0x80616282c260c10a 0xf70f1e1f07060c7b 0x7ee1e3c3e0e0c18f

def z891 : W := mkw 0x27fdf7dbc0082508 0x24ffbefb780104a1 0xf7ffffffe01e7c7f 0xfefffffffc03cf8f

def z892 : W := mkw 0x030b1c361b261a56 0x80616386c364c34a 0xf7cf1eff1fe61c7f 0x7ef9e3dfe3fcc38f

def z893 : W := mkw 0x06edc00004d14000 0x00ddb800009a2800 0x9fffe0001ff9e005 0xf3fffc0003ff3c00

def z894 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xf8f1ffe3e01fffff 0xff1e3ffc7c03ffff

def z895 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8fff9fcf8e593e7 0xfd1fff3f9f1cb27c

def z896 : W := mkw 0x0044804880000000 0x0008900910000000 0x60ce98fce0000001 0x2c19d31f9c000000

def z897 : W := mkw 0x04e6800014d50000 0x009cd000029aa000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z898 : W := mkw 0x080208243b269af6 0xc10041048764d35e 0x100000001f061ffc 0x0200000003e0c3ff

def z899 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfff09fe0fff81f87 0xfffe13fc1fff03f0

def z900 : W := mkw 0x27fdf7dbc4900000 0x04ffbefb78920000 0xefffffffe0f80003 0xfdfffffffc1f0000

def z901 : W := mkw 0x030b5c161b065854 0x80616b82c360cb0a 0xf70f7e1f1f067c7f 0x7ee1efc3e3e0cf8f

def z902 : W := mkw 0x00020824382492e2 0x000041048704925c 0xe8ce99fcf8e593e7 0xbd19d33f9f1cb27c

def z903 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xff0f1f1f1f061fff 0xffe1e3e3e3e0c3ff

def z904 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x88c0000018e593e4 0xb1180000031cb27c

def z905 : W := mkw 0x05e494c880000000 0x00bc929910000000 0xe7ce99fce0000003 0xbcf9d33f9c000000

def z906 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0xb8f1e703f8ffffff 0xf71e3ce07f1fffff

def z907 : W := mkw 0x030b141613060854 0x80616282c260c10a 0xb70f061f07061c7f 0x56e1e0c3e0e0c38f

def z908 : W := mkw 0x04e4c04884d14000 0x009c9809109a2800 0xe8fef9fce0f9e003 0xbd1fdf3f9c1f3c00

def z909 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xf7ffffffe0001c07 0xfefffffffc000380

def z910 : W := mkw 0x15b03fa14db83f0f 0x22b607f429b707e1 0xdff1ffe31fffff9f 0xfbfe3ffc63fffff3

def z911 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x2831e703e01ffffb 0x85063ce07c03ffff

def z912 : W := mkw 0x080208243cf5d2e2 0x41004104879eba5c 0x0800000018fdf3e4 0x01000000031fbe7c

def z913 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x67feffffe0000002 0xacffdffffc000000

def z914 : W := mkw 0x27fdf7dbc4d14000 0x04ffbefb789a2800 0xfffffffffff9e007 0xffffffffffff3c00

def z915 : W := mkw 0x034d945a83020814 0x8069b28b50604102 0xf7cf9fffe7020c1b 0xfef9f3fffce04183

def z916 : W := mkw 0x27fdf7dbc4980500 0x04ffbefb789300a0 0xfffffffffff81f87 0xffffffffffff03f0

def z917 : W := mkw 0x2044e049c0000000 0x04089c0938000000 0xe0cef9fce0000003 0xbc19df3f9c000000

def z918 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfff01fe31ff81ffe 0xfffe03fc63ff03ff

def z919 : W := mkw 0x0eab48243ef7d2e2 0x41d5690487defa5c 0x1f3160001ffff3e4 0x43e62c0003fffe7c

def z920 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf7cf1fff1f061c7f 0xfef9e3ffe3e0c38f

def z921 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8cf9ffff8e593e7 0xfd19f3ffff1cb27c

def z922 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf70f9f1fff061c7f 0xfee1f3e3ffe0c38f

def z923 : W := mkw 0x235df7dbc0000000 0x046bbefb78000000 0xe0cfffffe0000003 0xbc19fffffc000000

def z924 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8ce9ffcf8e59fe7 0xff19d3ff9f1cb3fc

def z925 : W := mkw 0x08020824386db7ea 0x61004104870db6fd 0x0800000018fdf3e4 0x01000000031fbe7c

def z926 : W := mkw 0x27fdf7dbc6924000 0x04ffbefb78d24800 0xffffffffe71fe007 0xfffffffffce3fc00

def z927 : W := mkw 0x27fdf7dbc2020000 0x04ffbefb78404000 0xf7ffffffe7020003 0xfefffffffce04000

def z928 : W := mkw 0x09103f7fe928bffe 0xe12207effd2517ff 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z929 : W := mkw 0x27fdf7dbc2020010 0x84ffbefb78404002 0xe7ffffffe002001b 0xfcfffffffc004003

def z930 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x3831e603e01ffffd 0x47063cc07c03ffff

def z931 : W := mkw 0x14b003a004b80703 0x02960074009700e0 0x9ff007e01ff81f86 0xf3fe00fc03ff03f0

def z932 : W := mkw 0x2154b7dbc0000000 0x042a96fb78000000 0x60ce1fffe0000002 0x2c19c3fffc000000

def z933 : W := mkw 0x03091c1209001804 0x0061238241200300 0xf70f1e1f1f061c7f 0x7ee1e3c3e3e0c38f

def z934 : W := mkw 0x14b003a004b80703 0x02960074009700e0 0x0ff001e01ff80380 0xa1fe003c03ff0070

def z935 : W := mkw 0x34f4e3e9e4b8a7ab 0x269e9c7d3c9714f5 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z936 : W := mkw 0x08448068a06182a2 0x4108900d140c3054 0x48ce99fce0e18380 0xa919d33f9c1c3070

def z937 : W := mkw 0x00000000200080a0 0x0000000004001014 0xb831e703e01fffff 0xd7063ce07c03ffff

def z938 : W := mkw 0x04e6c00016d74000 0x009cd80002dae800 0x9ff0e0001fffe004 0xf3fe1c0003fffc00

def z939 : W := mkw 0x15b01fb60db81f57 0x82b603f6c1b703ea 0xdff01ffc1ff81f86 0xfbfe03ff83ff03f0

def z940 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xe70f1e1f1f001c7b 0x7ce1e3c3e3e0038f

def z941 : W := mkw 0x0044804880000000 0x0008900910000000 0xf8fff9fce01fe007 0xff1fff3f9c03fc00

def z942 : W := mkw 0x04a0000004900000 0x0094000000920000 0x9ff0e0001ff9e004 0xf3fe1c0003ff3c00

def z943 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x47ffffffe0000000 0xe8fffffffc000000

def z944 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x00000000000593e0 0x000000000000b27c

def z945 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xdffff9e01fffe007 0xfbffff3c03fffc00

def z946 : W := mkw 0x04b00b200cb81702 0x00960164019702e0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z947 : W := mkw 0x15b03fa14db81f07 0x02b607f429b703e0 0xfff01fe3fff81f86 0xfffe03fc7fff03f0

def z948 : W := mkw 0x08468068b06582a2 0x4108d00d160cb054 0xe8ce99fcf8e58387 0xbd19d33f9f1cb070

def z949 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x770e1e1f1f061c7e 0x2ee1c3c3e3e0c38f

def z950 : W := mkw 0x0044804880000000 0x0008900910000000 0xe8ce99fce0001387 0xbd19d33f9c000270

def z951 : W := mkw 0x35b07fa14db81f07 0x06b60ff429b703e0 0xdff07fe01ff81f86 0xfbfe0ffc03ff03f0

def z952 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x5ff01fe01ff80f80 0xebfe03fc03ff01f0

def z953 : W := mkw 0x0044804880000000 0x0008900910000000 0x60ce19fce0000002 0x2c19c33f9c000000

def z954 : W := mkw 0x224fe05bf247e0a8 0x2449fc0b7e48fc15 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z955 : W := mkw 0x27fdf7dbc0082508 0x24ffbefb780104a1 0xffffffffe01fec1f 0xfffffffffc03fd83

def z956 : W := mkw 0x030b1c161b475854 0x80616382c368eb0a 0xf70f1e1f1f07fc7f 0x7ee1e3c3e3e0ff8f

def z957 : W := mkw 0x0802082439659ae6 0x41004104872cb35c 0x180000001fe59fe4 0x0300000003fcb3fc

def z958 : W := mkw 0x37fdf7dbc79a4d05 0x06ffbefb78f349a0 0xf7ffffffe71a6c03 0xfefffffffce34d80

def z959 : W := mkw 0x27fdf7dbc6924000 0x04ffbefb78d24800 0xfffffffffffa6007 0xffffffffffff4c00

def z960 : W := mkw 0x024f800012470000 0x0049f0000248e000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z961 : W := mkw 0x080208243ff7daf6 0xc100410487fefb5e 0x180000001ffffffc 0x0300000003ffffff

def z962 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0xe7cf9fffe0000003 0xfcf9f3fffc000000

def z963 : W := mkw 0x0054834880000000 0x000a906910000000 0xe0fe9ffce0000003 0xfc1fd3ff9c000000

def z964 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x8800010018e593e6 0x91000020031cb27c

def z965 : W := mkw 0x00468048b04580a0 0x0008d0091608b014 0xe8ce99fcf8e593e7 0xbd19d33f9f1cb27c

def z966 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x4ff01fe01ff81f82 0xa9fe03fc03ff03f0

def z967 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xc8ce99fcf8e58385 0xb919d33f9f1cb070

def z968 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xcff01fe01ff80382 0xf9fe03fc03ff0070

def z969 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z970 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x770f1e1f1f060c79 0x6ee1e3c3e3e0c18f

def z971 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x9831e00018fff3e5 0xd3063c00031ffe7c

def z972 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xffffffffe01ffc7f 0xfffffffffc03ff8f

def z973 : W := mkw 0x15b01fb60db81f57 0x82b603f6c1b703ea 0xfff11fff1ffe1fff 0xfffe23ffe3ffc3ff

def z974 : W := mkw 0x080208243b6fbffe 0xe1004104876df7ff 0x180000001ffffffc 0x0300000003ffffff

def z975 : W := mkw 0x024dc04880000000 0x0049b80910000000 0xe0cff9fce0000003 0xbc19ff3f9c000000

def z976 : W := mkw 0x06ab400016d74000 0x00d5680002dae800 0x9ff160001fffe004 0xf3fe2c0003fffc00

def z977 : W := mkw 0x15b03fa14db83f0f 0x22b607f429b707e1 0xfff1ffe3fffa7f9f 0xfffe3ffc7fff4ff3

def z978 : W := mkw 0x27fdf7dbc0082508 0x24ffbefb780104a1 0xe7ffffffe0186003 0xfcfffffffc030c00

def z979 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x0000000018e013e0 0x00000000031c027c

def z980 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xf7ffffffff000007 0xfeffffffffe00000

def z981 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7cf1fffe0000003 0x7cf9e3fffc000000

def z982 : W := mkw 0x14b00ba00db81f07 0x0296017401b703e0 0x9ff001e01ff81f84 0xf3fe003c03ff03f0

def z983 : W := mkw 0x27edf4dbc0000000 0x04fdbe9b78000000 0x47cef8fce0000000 0x28f9df1f9c000000

def z984 : W := mkw 0x1cf4a3e9e4f9a7ab 0x639e947d3c9f34f5 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z985 : W := mkw 0x0846806cb06582e2 0x4108d00d960cb05c 0xe8ce99fce0e583e3 0xbd19d33f9c1cb07c

def z986 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0x600ff9ffe0000003 0x0c01ff3ffc000000

def z987 : W := mkw 0x11103fa16928bfaf 0x222207f42d2517f5 0x40001fe0e0001f82 0x080003fc1c0003f0

def z988 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff1ffe01ff81f87 0xfbfe3ffc03ff03f0

def z989 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x3031e703e01ffffb 0x46063ce07c03ffff

def z990 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8ce99fcf8e18383 0xbd19d33f9f1c3070

def z991 : W := mkw 0x0846886cbb679af6 0xc108d10d976cf35e 0xe8ce99fcffe593e7 0xbd19d33f9ffcb27c

def z992 : W := mkw 0x0eefc04c96d74040 0x41ddf80992dae808 0x9fffe01c1fffe005 0xf3fffc0383fffc00

def z993 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0ce99fce0041067 0xbc19d33f9c00820c

def z994 : W := mkw 0x234df4dbc0000000 0x0469be9b78000000 0x600ff8ffe0000001 0x0c01ff1ffc000000

def z995 : W := mkw 0x24f4e3c9c0000000 0x049e9c7938000000 0x40fef9fce0000000 0xa81fdf3f9c000000

def z996 : W := mkw 0x27fdf7dbc30a2d1c 0xa4ffbefb786145a3 0xf7ffffffe71a6c1b 0xfefffffffce34d83

def z997 : W := mkw 0x27fdf7dbc4900000 0x04ffbefb78920000 0xe7ffffffffe00003 0xfcfffffffffc0000

def z998 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7ffffffe0041067 0xfcfffffffc00820c

def z999 : W := mkw 0x27fdf7dbc0082508 0x24ffbefb780104a1 0xe7ffffffe0000c1b 0xfcfffffffc000183

def z1000 : W := mkw 0x214494da80000000 0x0428929b50000000 0xe0ce99fce0000003 0xbc19d33f9c000000

def z1001 : W := mkw 0x15b017a005b80f07 0x02b602f400b701e0 0x9ff007e01ff80f84 0xf3fe00fc03ff01f0

def z1002 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7fef9fce0000003 0xbcffdf3f9c000000

def z1003 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xff0f1e1f1f1ffc7f 0x7fe1e3c3e3e3ff8f

def z1004 : W := mkw 0x27fdf7dbc0080500 0x04ffbefb780100a0 0xf7ffffffe0180c03 0xfefffffffc030180

def z1005 : W := mkw 0x15a01ca00db81f07 0x02b4039401b703e0 0x47c018e01fe01f80 0x28f8031c03fc03f0

def z1006 : W := mkw 0x0844886ca82092e2 0x4108910d9504125c 0xe8ce99fcf8e013e7 0xbd19d33f9f1c027c

def z1007 : W := mkw 0x100208243fbebfff 0xa200410487f7d7ff 0x180000001ffffffc 0x0300000003ffffff

def z1008 : W := mkw 0x0044a049c0000000 0x0008940938000000 0xe0cff9ffe0000003 0xbc19ff3ffc000000

def z1009 : W := mkw 0x0a4f805eb24780f0 0xc149f00bd648f01e 0x200e801ce0058061 0x0401d0039c00b00c

def z1010 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0x4fc018e01fe01384 0x29f8031c03fc0270

def z1011 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x67ff7fffe0000002 0x6cffeffffc000000

def z1012 : W := mkw 0x05f4b7c9c0000000 0x00be96f938000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1013 : W := mkw 0x27fdf7dbc3020814 0x84ffbefb78604102 0xf7ffffffe7061c7f 0xfefffffffce0c38f

def z1014 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0x67ce98fce0000001 0x2cf9d31f9c000000

def z1015 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7ffffffe0001c7b 0xfcfffffffc00038f

def z1016 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xc8ce99fcf8e19386 0xb919d33f9f1c3270

def z1017 : W := mkw 0x130b1cb61b261a57 0x82616396c364c34a 0xf70f1eff1f061c7f 0x7ee1e3dfe3e0c38f

def z1018 : W := mkw 0x08020824386db7ea 0x61004104870db6fd 0x0800000018e59ffc 0x01000000031cb3ff

def z1019 : W := mkw 0x19103fede928bfef 0x632207fdbd2517fd 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z1020 : W := mkw 0x37fdf7dbc4980501 0x06ffbefb789300a0 0xe7ffffffe0180003 0xfcfffffffc030000

def z1021 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xbfffe100ffffe007 0xf7fffc201ffffc00

def z1022 : W := mkw 0x04a008200cb01202 0x0094010401960240 0xcfc019e01fe01386 0xb9f8033c03fc0270

def z1023 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0x60cff8ffe0000001 0x2c19ff1ffc000000

def z1024 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x770f1e1f07061c7b 0x4ee1e3c3e0e0c38f

def z1025 : W := mkw 0x01021c0419041844 0x0020438083208308 0xf70f1e1f1f061c7f 0x7ee1e3c3e3e0c38f

def z1026 : W := mkw 0x0054834880080500 0x000a9069100100a0 0xf8fe9ffce0181f87 0xff1fd3ff9c0303f0

def z1027 : W := mkw 0x080208243ef7d2e2 0x4100410487defa5c 0x080000001fe593e4 0x0100000003fcb27c

def z1028 : W := mkw 0x05b01fa00cb01202 0x00b603f401960240 0xdff01fe01ff81386 0xfbfe03fc03ff0270

def z1029 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xc7fff9fce0000001 0xf8ffff3f9c000000

def z1030 : W := mkw 0x235db7dbc0000000 0x046bb6fb78000000 0xe7cf9fffe0000003 0xfcf9f3fffc000000

def z1031 : W := mkw 0x37fdf7dbc79a0d15 0x86ffbefb78f341a2 0xf7ffffffe71a0c1b 0xfefffffffce34183

def z1032 : W := mkw 0x06edc00006d34000 0x00ddb80000da6800 0x9ff1e0001ffbe004 0xf3fe3c0003ff7c00

def z1033 : W := mkw 0x07fdd7c880000000 0x00ffbaf910000000 0xe7fffffce0000003 0xfcffffff9c000000

def z1034 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfff01fe01ffc1fe7 0xfffe03fc03ff83fc

def z1035 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0x47c019e01fe01382 0x28f8033c03fc0270

def z1036 : W := mkw 0x020b001612060050 0x80416002c240c00a 0xb70f061f1f061c7f 0x76e1e0c3e3e0c38f

def z1037 : W := mkw 0x0054a349c0082508 0x200a9469380104a1 0xf0ffffffe01a6c1b 0xfe1ffffffc034d83

def z1038 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xe70e1e1f1f041c7f 0x3ce1c3c3e3e0838f

def z1039 : W := mkw 0x211037dbc0000000 0x042206fb78000000 0xe00e1fffe0000003 0x3c01c3fffc000000

def z1040 : W := mkw 0x1db21fa43dfd9fe7 0x43b643f487bfb3fc 0x1f3006001ffd9fe4 0x43e600c003ffb3fc

def z1041 : W := mkw 0x2154b7dbc0000000 0x042a96fb78000000 0x600e9fffe0000003 0x0c01d3fffc000000

def z1042 : W := mkw 0x15b03fa14db81f07 0x02b607f429b703e0 0xdff0ffe0fff81f86 0xfbfe1ffc1fff03f0

def z1043 : W := mkw 0x0044804880410000 0x0008900910082000 0xe8ce99fce0e18003 0xbd19d33f9c1c3000

def z1044 : W := mkw 0x0054a349c0000000 0x000a946938000000 0xe0fef9fce0000003 0xbc1fdf3f9c000000

def z1045 : W := mkw 0x15b01fb20db81f07 0x02b603f641b703e0 0xfff01fff1ff81f86 0xfffe03ffe3ff03f0

def z1046 : W := mkw 0x06efc01216d74010 0x80ddf80242dae802 0x9fffe0031fffe01d 0xf3fffc0063fffc03

def z1047 : W := mkw 0x015497c880000000 0x002a92f910000000 0xe0ce9ffce0000003 0xbc19d3ff9c000000

def z1048 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xbfffe0031fffe07d 0xf7fffc0063fffc0f

def z1049 : W := mkw 0x08448068a06182a2 0x4108900d140c3054 0xe8ce99fce0e593e7 0xbd19d33f9c1cb27c

def z1050 : W := mkw 0x0846886cba6792f2 0xc108d10d974cf25e 0xe8ce99fcf8e793ff 0xbd19d33f9f1cf27f

def z1051 : W := mkw 0x2a4fe05ff247c0e0 0x4549fc0bfe48f81c 0x200fe01fe007e061 0x0401fc03fc00fc0c

def z1052 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xefffffffe019e003 0xfdfffffffc033c00

def z1053 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xefffffffe0058007 0xfdfffffffc00b000

def z1054 : W := mkw 0x26efc05a96d74000 0x04ddf80b52dae800 0x9fffe01c1fffe005 0xf3fffc0383fffc00

def z1055 : W := mkw 0x18020824396d9fe7 0x43004104872db3fc 0x0800000018e59fe4 0x01000000031cb3fc

def z1056 : W := mkw 0x27fdf7dbc0082508 0x24ffbefb780104a1 0xffffffffe01a7f9f 0xfffffffffc034ff3

def z1057 : W := mkw 0x08448868a86192a2 0x4108910d150c3254 0xe8ce99fcf8e19387 0xbd19d33f9f1c3270

def z1058 : W := mkw 0x0000082008201202 0x0000010401040240 0xdfc019e01fe01386 0xfbf8033c03fc0270

def z1059 : W := mkw 0x25f4f7c9c0000000 0x04be9ef938000000 0xe7fefffce0000003 0xfcffdfff9c000000

def z1060 : W := mkw 0x01001c2009201a06 0x0020038401240340 0xcfc019e01fe01386 0xb9f8033c03fc0270

def z1061 : W := mkw 0x080208243a67d2e2 0x41004104874cfa5c 0x0800000018e7f3e4 0x01000000031cfe7c

def z1062 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xcfc01fe01fe01f86 0xb9f803fc03fc03f0

def z1063 : W := mkw 0x04e4c04880000000 0x009c980910000000 0xe0fef9fce0000003 0xbc1fdf3f9c000000

def z1064 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0xe7fff9fce0000003 0xfcffff3f9c000000

def z1065 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xffce99fcffe593e7 0xfff9d33f9ffcb27c

def z1066 : W := mkw 0x0846886cba6792e2 0x4108d10d974cf25c 0xf8ce99fcffe793e7 0xbf19d33f9ffcf27c

def z1067 : W := mkw 0x2054a3c9c0000000 0x040a947938000000 0xe0ce99fce0000003 0xbc19d33f9c000000

def z1068 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff0ffe01ff9ff86 0xfbfe1ffc03ff3ff0

def z1069 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x67cfffffe0000003 0x2cf9fffffc000000

def z1070 : W := mkw 0x0046886c98241242 0x0008d10d93048248 0xe8ce99fcf8e413e7 0xbd19d33f9f1c827c

def z1071 : W := mkw 0x06efc01216d74000 0x00ddf80242dae800 0xbfffe01f1fffe005 0xf7fffc03e3fffc00

def z1072 : W := mkw 0x15b03fa14db81f07 0x02b607f429b703e0 0xfff1ffe3fffe1fff 0xfffe3ffc7fffc3ff

def z1073 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8ce99fcf8fff3e7 0xbf19d33f9f1ffe7c

def z1074 : W := mkw 0x0a4fc04cb247c0e0 0x4149f8099648f81c 0x200e801ce0058061 0x0401d0039c00b00c

def z1075 : W := mkw 0x11001c200db81f07 0x0220038401b703e0 0xdfc01fe01ff81f86 0xfbf803fc03ff03f0

def z1076 : W := mkw 0x0054a349c0000000 0x000a946938000000 0xe0ce9fffe0000003 0xbc19d3fffc000000

def z1077 : W := mkw 0x0846886cb9659af6 0xc108d10d972cb35e 0xe8ce99fcf8e59fff 0xbd19d33f9f1cb3ff

def z1078 : W := mkw 0x2044a05bc0000000 0x0408940b78000000 0xe0ce99ffe0000003 0xbc19d33ffc000000

def z1079 : W := mkw 0x37b9779345982d0d 0x26f72ef268b305a1 0x17316603071a6c18 0x42e62cc060e34d83

def z1080 : W := mkw 0x0000004880000000 0x0000000910000000 0xe00e19fce0000003 0x3c01c33f9c000000

def z1081 : W := mkw 0x37fdf7dbc1080d05 0x06ffbefb782101a0 0xe7ffffffe0000c03 0xfcfffffffc000180

def z1082 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xd7c01fe01fe01f86 0x7af803fc03fc03f0

def z1083 : W := mkw 0x27edf4dbc0000000 0x04fdbe9b78000000 0xe7cff9ffe0000003 0xbcf9ff3ffc000000

def z1084 : W := mkw 0x04f483c880000000 0x009e907910000000 0xe0fe99fce0000003 0xbc1fd33f9c000000

def z1085 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x47c019e01fe00380 0x28f8033c03fc0070

def z1086 : W := mkw 0x04e4804880000000 0x009c900910000000 0xe7fe99fce0000003 0xfcffd33f9c000000

def z1087 : W := mkw 0x08122b25786db7ea 0x61024564af0db6fd 0x1831660318fffffc 0x43062cc0631fffff

def z1088 : W := mkw 0x0844886ca86192e2 0x4108910d950c325c 0xe8ce99fce0e193e3 0xbd19d33f9c1c327c

def z1089 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x0800000018e18380 0x01000000031c3070

def z1090 : W := mkw 0x27fdf7dbc3020814 0x84ffbefb78604102 0xe7ffffffe7000003 0xfcfffffffce00000

def z1091 : W := mkw 0x15a01ca00db81f07 0x02b4039401b703e0 0xdfc019e01ff81f86 0xbbf8033c03ff03f0

def z1092 : W := mkw 0x05b0178004980500 0x00b602f0009300a0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z1093 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x68ce99fcf8e583e1 0xad19d33f9f1cb07c

def z1094 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x67fff9ffe0000001 0xacffff3ffc000000

def z1095 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0x5fc01fe01ff81f86 0x2bf803fc03ff03f0

def z1096 : W := mkw 0x06edc04880000000 0x00ddb80910000000 0xe7ce99fce0000003 0xbcf9d33f9c000000

def z1097 : W := mkw 0x07b9379340000000 0x00f726f268000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1098 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0x8800800018e593e5 0x91001000031cb27c

def z1099 : W := mkw 0x080208243865b2ea 0x61004104870cb65d 0x0800000018e7f3fc 0x01000000031cfe7f

def z1100 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x8ffee0001ffde005 0xb1ffdc0003ffbc00

def z1101 : W := mkw 0x27fdf7dbc4d14000 0x04ffbefb789a2800 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z1102 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xfff1ffe31fffffff 0xfffe3ffc63ffffff

def z1103 : W := mkw 0x0cf4e369e4f9e7aa 0x619e9c6d3c9f3cf5 0x08f0e1e0e0f9e380 0x811e1c3c1c1f3c70

def z1104 : W := mkw 0x31103ffbe928bfaf 0x262207ff7d2517f5 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z1105 : W := mkw 0x0a4f804cb24780e0 0x4149f0099648f01c 0x200f801ce0078061 0x0401f0039c00f00c

def z1106 : W := mkw 0x27fdf7dbc0410000 0x04ffbefb78082000 0xefffffffe0e18003 0xfdfffffffc1c3000

def z1107 : W := mkw 0x030b1c361b261a56 0x80616386c364c34a 0xf70f1fff1f061fff 0x7ee1e3ffe3e0c3ff

def z1108 : W := mkw 0x001023016008a5a8 0x200204602c0114b5 0x1831e703e01ffffc 0xc3063ce07c03ffff

def z1109 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0xdfc01fe01fe01f86 0xfbf803fc03fc03f0

def z1110 : W := mkw 0x27b977dbc0000000 0x04f72efb78000000 0xe73f7fffe0000003 0x7ce7effffc000000

def z1111 : W := mkw 0x15a01ca00db01a07 0x02b4039401b60340 0x4fc019e01fe00380 0xa9f8033c03fc0070

def z1112 : W := mkw 0x231937dbc0000000 0x046326fb78000000 0x600f1fffe0000003 0x0c01e3fffc000000

def z1113 : W := mkw 0x35b03fb34db81f07 0x06b607f669b703e0 0xdff01fe31ff81f86 0xfbfe03fc63ff03f0

def z1114 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x1ffee0001fffe004 0xa3ffdc0003fffc00

def z1115 : W := mkw 0x15b01fb20db81f17 0x82b603f641b703e2 0xdff01fe31ff81f9e 0xfbfe03fc63ff03f3

def z1116 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x48ce99fcf8e593e4 0xa919d33f9f1cb27c

def z1117 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xf73f7e1f1f1e7c7f 0x7ee7efc3e3e3cf8f

def z1118 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xff3f1e1f1f1e1c7f 0xffe7e3c3e3e3c38f

def z1119 : W := mkw 0x25f4f7dbc0000000 0x04be9efb78000000 0xe0feffffe0000003 0xbc1fdffffc000000

def z1120 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xbfffe6031fffe007 0xf7fffcc063fffc00

def z1121 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8cff9fcf8e7f3e7 0xbd19ff3f9f1cfe7c

def z1122 : W := mkw 0x06efc00416d74040 0x00ddf80082dae808 0xbfffe01c1fffe065 0xf7fffc0383fffc0c

def z1123 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x673fffffe0000003 0x4ce7fffffc000000

def z1124 : W := mkw 0x27fdf7dbc4900000 0x04ffbefb78920000 0xf7ffffffe7180003 0xfefffffffce30000

def z1125 : W := mkw 0x24e4c0c880000000 0x049c981910000000 0xe0ce99fce0000003 0xbc19d33f9c000000

def z1126 : W := mkw 0x15a01ca00db81f07 0x02b4039401b703e0 0xdfc01ee01ff81f86 0x7bf803dc03ff03f0

def z1127 : W := mkw 0x11101fa009281f07 0x022203f4012503e0 0xdfc01fe01fe01f86 0xfbf803fc03fc03f0

def z1128 : W := mkw 0x2a4fe05ff24780f0 0xc549fc0bfe48f01e 0x200fe01fe0078079 0x0401fc03fc00f00f

def z1129 : W := mkw 0x27edd4da80000000 0x04fdba9b50000000 0x47ce99fce0000000 0xa8f9d33f9c000000

def z1130 : W := mkw 0x27fdf7dbc0080500 0x04ffbefb780100a0 0xefffffffe0180383 0xfdfffffffc030070

def z1131 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0x670f1e1f1f061c7b 0x2ce1e3c3e3e0c38f

def z1132 : W := mkw 0x15a01ca00db81f07 0x02b4039401b703e0 0x4fc018e01ff80380 0x29f8031c03ff0070

def z1133 : W := mkw 0x27fdf7dbc0002008 0x24ffbefb78000401 0xe7ffffffe002601b 0xfcfffffffc004c03

def z1134 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x0fffe0001fffe001 0xa1fffc0003fffc00

def z1135 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff09fe01ffd9f87 0xfbfe13fc03ffb3f0

def z1136 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xf7ffffffe0060007 0xfefffffffc00c000

def z1137 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9ffee0001ff9e004 0xf3ffdc0003ff3c00

def z1138 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xf7ffffffe01a6003 0xfefffffffc034c00

def z1139 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x9fffe6031fffec1d 0xf3fffcc063fffd83

def z1140 : W := mkw 0x01101f2009281f06 0x002203e4012503e0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z1141 : W := mkw 0x00448868a82092a2 0x0008910d15041254 0xe8ce99fcf8e593e7 0xbd19d33f9f1cb27c

def z1142 : W := mkw 0x030b1c161b061854 0x80616382c360c30a 0xffcf1e1f1fe61c7f 0xfff9e3c3e3fcc38f

def z1143 : W := mkw 0x15b03fa14db81f07 0x02b607f429b703e0 0xfff1ffe3ffffff87 0xfffe3ffc7ffffff0

def z1144 : W := mkw 0x06a9400006924000 0x00d5280000d24800 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z1145 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x68ce99fcf8e193e2 0xad19d33f9f1c327c

def z1146 : W := mkw 0x37fdf7dbc5980d05 0x06ffbefb78b301a0 0xffffffffe7181f87 0xfffffffffce303f0

def z1147 : W := mkw 0x0ca208243cf592e2 0x41944104879eb25c 0x9ff000001ffd93e4 0xf3fe000003ffb27c

def z1148 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x8fffe0001ff9e001 0xf1fffc0003ff3c00

def z1149 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8ce19fcf8e013e6 0xbd19c33f9f1c027c

def z1150 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x47ce19fce0000000 0x28f9c33f9c000000

def z1151 : W := mkw 0x37b97793479a4d05 0x06f72ef268f349a0 0x17316603071a6c00 0x42e62cc060e34d80

def z1152 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xf7ffffffe0020c1b 0xfefffffffc004183

def z1153 : W := mkw 0x27edf4dbc0000000 0x04fdbe9b78000000 0xe7cffeffe0000003 0x7cf9ffdffc000000

def z1154 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xe7fe1fffe0000002 0xfcffc3fffc000000

def z1155 : W := mkw 0x15b03fa14db81f07 0x02b607f429b703e0 0xdff17fe31ff81f86 0xfbfe2ffc63ff03f0

def z1156 : W := mkw 0x26fde3c9c0000000 0x04dfbc7938000000 0xe7fff9fce0000003 0xfcffff3f9c000000

def z1157 : W := mkw 0x05b01fa009201a06 0x00b603f401240340 0xdff01fe01fe01f86 0xfbfe03fc03fc03f0

def z1158 : W := mkw 0x0044806880200202 0x0008900d10040040 0xe8ce99fce0e00383 0xbd19d33f9c1c0070

def z1159 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0x1fffe0001ffbe000 0xe3fffc0003ff7c00

def z1160 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xcff019e01ff81386 0xb9fe033c03ff0270

def z1161 : W := mkw 0x08020824386592e2 0x41004104870cb25c 0xb801060318e79fff 0x570020c0631cf3ff

def z1162 : W := mkw 0x080208243efff7ea 0x6100410487dffefd 0x180000001ffffffc 0x0300000003ffffff

def z1163 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0xefffffffe0001387 0xfdfffffffc000270

def z1164 : W := mkw 0x27fdf7dbc0000000 0x04ffbefb78000000 0x67fffeffe0000001 0x6cffffdffc000000

def z1165 : W := mkw 0x27fdf7dbc0080500 0x04ffbefb780100a0 0xffffffffe01e1fff 0xfffffffffc03c3ff

def z1166 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x68ce99fce0e593e3 0x8d19d33f9c1cb27c

def z1167 : W := mkw 0x0309145a80000000 0x0061228b50000000 0xe70f1fffe0000003 0x7ce1e3fffc000000

def z1168 : W := mkw 0x26ede05bc0000000 0x04ddbc0b78000000 0xe7fff9ffe0000003 0xfcffff3ffc000000

def z1169 : W := mkw 0x15b01fa00db81f07 0x02b603f401b703e0 0xdff17fe01ffa7f86 0xfbfe2ffc03ff4ff0

def z1170 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xe8cf99fff8e793ff 0xbd19f33fff1cf27f

def z1171 : W := mkw 0x231937dbc0000000 0x046326fb78000000 0xe73fffffe0000003 0xfce7fffffc000000

def z1172 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8ce99fcf8e79fff 0xbf19d33f9f1cf3ff

def z1173 : W := mkw 0x27edf4dbc0000000 0x04fdbe9b78000000 0xe7fff8ffe0000001 0xfcffff1ffc000000

def z1174 : W := mkw 0x0144944880000000 0x0028928910000000 0xe7ce9ffce0000003 0xfcf9d3ff9c000000

def z1175 : W := mkw 0x27fdf7dbc4904000 0x04ffbefb78920800 0xe7ffffffe0186003 0xfcfffffffc030c00

def z1176 : W := mkw 0x06efc00016d74000 0x00ddf80002dae800 0xbfffe0001ffff067 0xf7fffc0003fffe0c

def z1177 : W := mkw 0x080208243b679af6 0xc1004104876cf35e 0x080000001fe593e4 0x0100000003fcb27c

def z1178 : W := mkw 0x0a4fc048b247c0a0 0x4149f8091648f814 0x000fe000e007e001 0x0001fc001c00fc00

def z1179 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z1180 : W := mkw 0x0846886cb86592e2 0x4108d10d970cb25c 0x40ce19fcf8e00380 0x2819c33f9f1c0070

def z1181 : W := mkw 0x224dc05a80000000 0x0449b80b50000000 0xe0ce99fce0000003 0xbc19d33f9c000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z8,z9,z6]),(0,[z0,z10,z2,z8,z11,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z12])],[(0,[z7,z0,z1,z2,z8,z5,z13]),(0,[z0,z1,z2,z8,z5,z14,z6]),(0,[z0,z1,z2,z8,z5,z15,z6])],[(0,[z16,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z17,z5,z6]),(0,[z0,z18,z1,z2,z19,z5,z6])],[(0,[z20,z0,z1,z2,z21,z5,z6]),(0,[z22,z0,z23,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z24,z6]),(1,[z0,z1,z2,z8,z5,z25])],[(0,[z26,z0,z1,z2,z27,z5,z6]),(0,[z0,z28,z1,z2,z8,z5,z6]),(0,[z0,z29,z1,z8,z30,z5,z6]),(0,[z0,z1,z2,z8,z31,z5,z6]),(0,[z0,z1,z2,z32,z8,z33,z5])],[(0,[z0,z1,z2,z8,z34,z5,z6]),(1,[z35,z1,z36,z8,z5,z6]),(0,[z0,z37,z1,z2,z8,z38,z5]),(0,[z39,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z40]),(0,[z0,z1,z2,z32,z8,z41,z5])],[(0,[z42,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z43,z5,z6]),(0,[z0,z1,z2,z44,z8,z5,z6]),(0,[z45,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z46]),(0,[z47,z0,z1,z2,z32,z8,z5])],[(1,[z0,z1,z2,z21,z5,z6]),(0,[z48,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z49,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z6,z50]),(0,[z0,z1,z2,z8,z51,z5,z6]),(0,[z0,z1,z2,z52,z5,z53,z6])]],
   [[(0,[z26,z0,z1,z2,z54,z5,z6]),(1,[z0,z1,z2,z55,z8,z5]),(0,[z0,z1,z2,z8,z5,z56,z6]),(0,[z57,z0,z1,z2,z5,z53,z6]),(0,[z0,z58,z1,z2,z8,z5,z6]),(0,[z0,z59,z1,z2,z8,z5,z6])],[(0,[z60,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z61]),(0,[z0,z1,z62,z2,z8,z5,z6]),(0,[z63,z0,z1,z2,z8,z5,z6])],[(0,[z64,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z65,z8,z5,z6]),(0,[z0,z1,z2,z66,z8,z5,z6]),(0,[z0,z67,z1,z2,z8,z5,z6]),(0,[z0,z68,z1,z2,z8,z69,z6])],[(0,[z0,z70,z1,z2,z8,z5,z6]),(0,[z71,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z72,z8,z5,z6]),(0,[z0,z1,z73,z2,z8,z5,z53])],[(0,[z20,z0,z1,z2,z74,z5,z6]),(1,[z0,z1,z75,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z76,z6]),(0,[z77,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z78,z6]),(1,[z79,z1,z2,z38,z5,z6]),(0,[z0,z1,z2,z80,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z81,z6]),(1,[z0,z1,z2,z82,z8,z5]),(0,[z0,z1,z83,z2,z3,z5,z6]),(0,[z0,z1,z2,z8,z5,z84,z6]),(0,[z0,z1,z8,z5,z85,z6,z86])],[(0,[z0,z1,z2,z8,z5,z87,z6]),(0,[z88,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z89,z6])]],
   [[(0,[z0,z18,z1,z90,z2,z8,z5])],[(0,[z0,z91,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z92,z5,z6]),(0,[z0,z1,z2,z8,z93,z5,z94])],[(0,[z0,z1,z2,z95,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z30,z5])],[(0,[z96,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z97,z8,z5,z6]),(0,[z39,z0,z1,z2,z8,z5,z98]),(0,[z0,z99,z1,z2,z8,z5,z6]),(1,[z0,z49,z100,z8,z5,z6]),(0,[z101,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z102])],[(0,[z103,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z104,z8,z5,z6]),(0,[z105,z0,z1,z2,z8,z5,z6]),(0,[z0,z106,z1,z2,z8,z5,z6]),(0,[z107,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z108,z6])],[(0,[z109,z0,z1,z110,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z111,z6]),(0,[z112,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z113,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z114,z5,z6])],[(0,[z0,z1,z115,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z116,z5,z6]),(0,[z0,z117,z2,z19,z8,z5,z6]),(0,[z0,z118,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z110,z2,z8,z5]),(0,[z0,z119,z1,z2,z8,z5,z6])]],
   [[(1,[z120,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z8,z5,z122,z6]),(0,[z0,z123,z1,z2,z8,z5,z6]),(0,[z0,z1,z124,z2,z8,z5,z6])],[(1,[z0,z1,z2,z8,z5,z125]),(0,[z0,z1,z2,z126,z8,z5,z6]),(0,[z0,z1,z127,z2,z8,z5,z6])],[(0,[z0,z128,z1,z2,z8,z5,z6]),(0,[z0,z129,z1,z2,z8,z5,z6]),(0,[z0,z1,z130,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z131,z6]),(0,[z0,z1,z2,z8,z132,z5,z6])],[(0,[z0,z2,z19,z8,z133,z5,z6]),(0,[z0,z1,z2,z8,z134,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z135])],[(0,[z7,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z136,z5,z6]),(0,[z0,z1,z2,z8,z137,z5,z6])],[(0,[z0,z1,z2,z8,z93,z138,z6]),(0,[z139,z0,z1,z2,z32,z8,z5]),(0,[z109,z0,z18,z1,z2,z8,z5])],[(0,[z0,z140,z1,z2,z8,z5,z6]),(0,[z141,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z142])],[(0,[z0,z1,z143,z2,z8,z69,z6])]],
   [[(0,[z0,z29,z1,z83,z8,z5,z6]),(0,[z0,z18,z1,z144,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z145,z6]),(0,[z0,z1,z100,z2,z32,z8,z5]),(0,[z0,z1,z2,z32,z8,z30,z5]),(0,[z0,z1,z2,z146,z8,z5,z6])],[(1,[z0,z1,z2,z8,z5,z147]),(0,[z148,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z5,z6,z149]),(0,[z0,z1,z2,z8,z93,z5,z6])],[(0,[z0,z1,z2,z8,z150,z5,z6]),(0,[z0,z1,z2,z8,z5,z151,z6])],[(0,[z0,z1,z2,z8,z152,z5,z6]),(0,[z0,z1,z153,z2,z8,z133,z5]),(0,[z0,z1,z2,z154,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z155])],[(0,[z22,z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z100,z156,z8,z5,z6]),(0,[z35,z0,z18,z1,z2,z8,z5]),(0,[z0,z157,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z158]),(1,[z0,z1,z73,z2,z8,z5]),(0,[z0,z18,z1,z2,z8,z159,z5])],[(0,[z0,z160,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z161,z6]),(0,[z0,z162,z1,z2,z8,z5,z6]),(0,[z163,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z164,z6])],[(0,[z0,z165,z1,z2,z8,z5,z6]),(0,[z0,z166,z1,z2,z8,z5,z6]),(0,[z0,z167,z1,z2,z8,z5,z86]),(1,[z0,z1,z2,z8,z5,z76]),(0,[z0,z18,z1,z2,z8,z5,z86]),(0,[z0,z1,z2,z8,z5,z168,z6])]],
   [[(0,[z169,z0,z1,z2,z8,z5,z6])],[(0,[z22,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z170,z5,z6]),(0,[z0,z1,z2,z8,z171,z5,z6]),(0,[z0,z1,z172,z2,z8,z5,z6]),(0,[z0,z1,z143,z2,z8,z5,z173])],[(0,[z0,z1,z2,z8,z174,z5,z6])],[(0,[z0,z1,z2,z175,z8,z5,z6]),(0,[z0,z1,z2,z8,z38,z5,z6]),(1,[z0,z1,z2,z132,z5,z6])],[(0,[z176,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z36,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z177,z6])],[(0,[z0,z1,z83,z2,z8,z5,z178])],[(0,[z179,z0,z1,z2,z8,z5,z6]),(0,[z0,z180,z1,z2,z8,z5,z6]),(0,[z181,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z4,z8,z5]),(0,[z182,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z183,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z94]),(1,[z0,z1,z2,z32,z5,z184])],[(0,[z0,z49,z185,z2,z8,z5,z6]),(0,[z186,z1,z2,z4,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z187]),(0,[z0,z1,z83,z8,z5,z6,z86]),(0,[z0,z1,z2,z8,z5,z184,z6]),(0,[z0,z188,z1,z2,z8,z5,z6]),(0,[z189,z0,z1,z2,z8,z5,z6])]],
   [[(0,[z190,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z133,z5,z184,z6]),(0,[z0,z1,z2,z8,z5,z191,z6]),(0,[z0,z10,z1,z2,z192,z8,z6]),(0,[z0,z1,z2,z8,z5,z6,z193])],[(0,[z0,z1,z1,z2,z8,z5,z6]),(0,[z182,z1,z2,z8,z138,z5,z6]),(0,[z0,z1,z2,z8,z194,z5,z6]),(1,[z57,z0,z1,z2,z53,z6])],[(0,[z195,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z196,z8,z5,z6]),(0,[z0,z197,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z198,z6]),(0,[z0,z1,z2,z199,z8,z5,z6]),(0,[z0,z1,z8,z30,z5,z6,z86]),(0,[z0,z1,z2,z32,z8,z5,z69])],[(0,[z47,z0,z1,z2,z200,z5,z6]),(0,[z0,z68,z1,z2,z192,z8,z6]),(0,[z0,z18,z1,z2,z8,z8,z5])],[(0,[z201,z0,z1,z2,z8,z5,z6]),(0,[z0,z202,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z203]),(0,[z0,z204,z1,z2,z8,z5,z6]),(1,[z0,z1,z144,z8,z5,z6])],[(0,[z205,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z206,z6]),(0,[z0,z1,z2,z8,z5,z6,z207]),(0,[z0,z1,z2,z200,z8,z5,z6]),(0,[z0,z1,z208,z2,z8,z5,z6]),(0,[z0,z1,z209,z2,z8,z5,z6])],[(0,[z0,z1,z2,z54,z8,z5,z6]),(0,[z0,z210,z1,z2,z32,z8,z5]),(0,[z0,z18,z1,z2,z211,z8,z5]),(0,[z0,z1,z2,z8,z5,z212,z6]),(0,[z0,z18,z1,z2,z8,z5,z213])],[(0,[z214,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z9,z6,z213]),(0,[z0,z215,z1,z2,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z74,z8,z5,z6]),(0,[z79,z186,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z216,z5,z6]),(1,[z139,z0,z2,z133,z5,z6]),(1,[z0,z1,z2,z8,z5,z168]),(0,[z0,z18,z1,z2,z192,z8,z5])],[(0,[z0,z1,z2,z8,z5,z6,z217]),(0,[z0,z1,z2,z32,z8,z5,z218]),(0,[z0,z1,z2,z219,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z220]),(0,[z0,z1,z2,z8,z5,z168,z53])],[(0,[z22,z0,z185,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z221,z5,z6]),(0,[z0,z1,z2,z4,z133,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z9]),(0,[z0,z1,z2,z192,z8,z138,z6]),(0,[z39,z0,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z222,z8,z5,z6])],[(0,[z0,z49,z23,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z223,z5,z6]),(0,[z0,z224,z1,z2,z8,z5,z6]),(0,[z0,z225,z1,z2,z8,z5,z6]),(0,[z0,z1,z110,z2,z32,z8,z5]),(0,[z0,z18,z1,z2,z8,z52,z5])],[(0,[z0,z1,z226,z2,z8,z5,z6]),(0,[z57,z0,z1,z2,z8,z52,z6])],[(0,[z0,z1,z2,z8,z5,z227,z6]),(0,[z0,z228,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z229,z6]),(0,[z0,z68,z1,z143,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z230,z6])],[(0,[z0,z1,z2,z231,z8,z5,z6])],[(0,[z0,z1,z232,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z233,z6]),(1,[z0,z210,z211,z8,z5,z6]),(0,[z234,z0,z1,z2,z8,z5,z6]),(0,[z0,z167,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z235,z6]),(0,[z0,z1,z2,z8,z5,z6,z236]),(0,[z0,z18,z1,z2,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z8,z237,z5,z6]),(0,[z0,z1,z2,z8,z5,z98,z213]),(0,[z0,z117,z1,z2,z32,z8,z5]),(0,[z0,z10,z1,z2,z32,z8,z5]),(1,[z47,z0,z2,z8,z5,z218])],[(0,[z0,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z238,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z239]),(0,[z0,z240,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z178])],[(0,[z0,z1,z2,z8,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z98,z239]),(0,[z0,z1,z2,z8,z5,z6,z241])],[(0,[z0,z167,z1,z2,z8,z5,z85]),(0,[z0,z18,z1,z143,z2,z8,z5]),(0,[z0,z68,z1,z2,z32,z8,z5]),(0,[z242,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z85])],[(0,[z39,z0,z18,z1,z2,z8,z5]),(0,[z243,z0,z1,z2,z8,z5,z6]),(0,[z57,z0,z1,z143,z2,z8,z6])],[(0,[z0,z1,z2,z8,z244,z5,z6]),(0,[z26,z0,z1,z36,z8,z5,z6]),(0,[z186,z0,z1,z2,z8,z245,z6]),(0,[z47,z0,z1,z2,z8,z5,z218])],[(0,[z0,z246,z1,z2,z8,z5,z6]),(0,[z247,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z143,z2,z8,z5,z248])],[(0,[z0,z249,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z239]),(0,[z0,z250,z1,z2,z8,z5,z6]),(0,[z251,z0,z1,z2,z8,z5,z6]),(0,[z109,z0,z1,z2,z32,z8,z5])]],
   [[(0,[z0,z1,z252,z2,z8,z5,z6]),(0,[z253,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z19,z8,z5]),(0,[z254,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z143,z2,z192,z8,z6]),(0,[z0,z1,z2,z8,z5,z255,z6])],[(0,[z35,z0,z1,z143,z8,z5,z6]),(0,[z0,z1,z256,z2,z8,z5,z6]),(0,[z257,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z258]),(0,[z57,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z192,z8,z53,z6])],[(1,[z39,z1,z2,z8,z5,z98]),(0,[z259,z0,z1,z2,z8,z5,z6]),(0,[z260,z0,z1,z2,z8,z5,z6]),(0,[z0,z261,z1,z2,z8,z5,z6]),(0,[z0,z1,z262,z2,z8,z5,z6])],[(0,[z185,z1,z23,z2,z8,z5,z6]),(0,[z0,z1,z263,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z264,z6]),(0,[z0,z1,z83,z2,z8,z5,z76])],[(0,[z0,z49,z1,z2,z8,z171,z6]),(0,[z265,z0,z1,z2,z8,z5,z6]),(0,[z0,z261,z1,z2,z8,z133,z6]),(0,[z0,z1,z2,z8,z5,z6,z266])],[(1,[z0,z1,z8,z267,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z98]),(0,[z0,z1,z2,z8,z5,z85,z213]),(0,[z88,z0,z18,z1,z2,z8,z5])],[(0,[z0,z1,z23,z2,z8,z5,z6]),(0,[z0,z268,z1,z2,z8,z5,z6]),(0,[z26,z35,z1,z2,z8,z5,z6]),(0,[z0,z269,z1,z2,z8,z5,z6])],[(0,[z20,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z270,z8,z5,z6]),(0,[z35,z0,z1,z2,z32,z8,z5]),(0,[z186,z0,z1,z2,z8,z5,z271]),(0,[z0,z1,z2,z272,z8,z5,z6]),(0,[z0,z167,z2,z8,z5,z6,z239]),(1,[z0,z18,z1,z2,z8,z5])]],
   [[(0,[z20,z0,z1,z2,z8,z34,z6]),(0,[z0,z1,z2,z8,z273,z5,z6]),(0,[z0,z1,z2,z8,z274,z5,z6]),(0,[z275,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z276,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z125]),(0,[z186,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z277,z6]),(0,[z0,z1,z2,z8,z5,z278,z6]),(0,[z0,z279,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z53])],[(0,[z0,z1,z2,z8,z5,z280,z6]),(1,[z0,z117,z2,z19,z5,z6])],[(1,[z0,z1,z2,z8,z5,z6]),(0,[z35,z0,z1,z156,z8,z5,z6]),(0,[z47,z0,z1,z2,z8,z5,z239]),(0,[z0,z1,z2,z281,z8,z5,z6]),(0,[z0,z282,z1,z2,z8,z5,z6]),(0,[z0,z283,z1,z2,z8,z5,z6])],[(1,[z0,z1,z2,z8,z34,z6]),(0,[z0,z1,z2,z8,z5,z284,z6]),(0,[z0,z1,z2,z8,z285,z5,z6]),(0,[z0,z1,z286,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z287,z5,z6])],[(0,[z0,z1,z2,z8,z11,z138,z6]),(1,[z0,z1,z2,z8,z288,z6]),(0,[z0,z1,z289,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z290,z6])],[],[(0,[z0,z1,z2,z55,z8,z5,z6]),(0,[z291,z0,z1,z2,z8,z5,z6]),(1,[z0,z18,z1,z2,z52,z5])]],
   [[(0,[z292,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z36,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z293,z6]),(0,[z0,z1,z2,z8,z294,z5,z6]),(0,[z0,z1,z143,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z94,z86]),(0,[z0,z1,z2,z8,z52,z5,z25]),(0,[z0,z1,z295,z2,z8,z5,z6])],[(0,[z0,z1,z296,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z38,z5]),(0,[z297,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z298,z5,z6])],[(0,[z0,z1,z2,z8,z5,z6,z147]),(0,[z299,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z11,z5,z6]),(0,[z0,z1,z2,z8,z5,z300,z6]),(0,[z301,z0,z18,z1,z2,z8,z5])],[(0,[z0,z1,z2,z302,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z303]),(0,[z0,z1,z2,z304,z32,z8,z5])],[(0,[z20,z1,z23,z2,z8,z5,z6])],[(0,[z305,z0,z1,z2,z8,z5,z6]),(0,[z0,z29,z1,z2,z8,z5,z6])],[(0,[z0,z18,z185,z1,z2,z8,z5]),(1,[z0,z1,z2,z8,z306,z6]),(0,[z301,z0,z1,z2,z8,z5,z6]),(1,[z0,z307,z2,z8,z5,z6])],[(0,[z22,z185,z1,z2,z8,z5,z6]),(0,[z308,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z309,z5,z6]),(1,[z109,z0,z1,z8,z5,z85]),(0,[z0,z18,z310,z1,z2,z8,z5])]],
   [[(0,[z20,z0,z185,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z311,z6]),(0,[z0,z23,z2,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z312]),(0,[z0,z1,z313,z2,z8,z5,z6]),(0,[z0,z314,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z315,z6]),(0,[z0,z316,z1,z2,z8,z5,z6]),(0,[z0,z1,z317,z2,z32,z8,z5]),(0,[z0,z1,z2,z318,z8,z5,z6])],[(0,[z20,z0,z1,z2,z8,z319,z6]),(0,[z20,z0,z1,z2,z8,z5,z147]),(0,[z0,z1,z8,z267,z5,z9,z6]),(0,[z0,z49,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z320,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z321,z6])],[(0,[z0,z1,z2,z8,z5,z6,z322]),(0,[z0,z1,z2,z8,z5,z94,z121]),(0,[z0,z210,z1,z211,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z11,z5])],[(0,[z323,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z324,z2,z8,z5,z6])],[(0,[z325,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z156,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z326,z6]),(0,[z0,z1,z2,z8,z5,z327,z6]),(0,[z328,z0,z1,z2,z8,z5,z6]),(0,[z329,z0,z1,z2,z8,z5,z6])],[(1,[z0,z1,z2,z8,z319,z6]),(0,[z330,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z331,z2,z8,z5,z6]),(0,[z0,z106,z2,z8,z5,z332,z6]),(0,[z333,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z334,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z335])],[(1,[z0,z1,z232,z8,z5,z6]),(0,[z0,z49,z1,z100,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z336,z6]),(0,[z0,z1,z2,z8,z337,z5,z6]),(0,[z0,z18,z1,z2,z8,z338,z5])]],
   [[(0,[z0,z1,z2,z8,z5,z339,z6])],[(0,[z0,z1,z2,z340,z8,z5,z6]),(0,[z0,z1,z2,z8,z288,z133,z6]),(0,[z0,z1,z2,z8,z341,z5,z6]),(1,[z0,z1,z83,z3,z5,z6]),(0,[z0,z1,z2,z8,z342,z5,z6])],[(0,[z0,z1,z2,z8,z343,z5,z6]),(0,[z0,z344,z1,z2,z8,z5,z6]),(0,[z0,z1,z345,z2,z8,z5,z6]),(0,[z0,z346,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z347,z5,z6]),(0,[z0,z1,z2,z8,z5,z53,z6])],[(0,[z0,z1,z2,z156,z8,z5,z6]),(0,[z0,z1,z100,z36,z8,z5,z6]),(0,[z186,z0,z1,z2,z8,z161,z6]),(0,[z0,z1,z2,z8,z5,z271,z6]),(0,[z0,z348,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z349,z6]),(1,[z0,z167,z2,z8,z5,z239])],[(0,[z20,z0,z23,z2,z8,z5,z6]),(0,[z350,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z351,z8,z5,z6]),(0,[z0,z1,z2,z8,z352,z5,z6])],[(0,[z0,z1,z2,z8,z5,z353,z6]),(0,[z0,z354,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z355]),(0,[z0,z18,z68,z1,z2,z8,z5]),(0,[z356,z0,z1,z2,z8,z5,z6])],[(0,[z0,z357,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z358,z5,z6]),(0,[z39,z0,z1,z2,z32,z8,z5]),(0,[z359,z0,z1,z2,z8,z5,z6]),(0,[z0,z2,z8,z133,z5,z332,z6]),(0,[z0,z1,z2,z360,z8,z5,z6]),(0,[z0,z1,z2,z3,z32,z8,z5]),(0,[z57,z0,z68,z1,z2,z8,z6])],[(0,[z361,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z93,z9,z6]),(0,[z120,z0,z18,z1,z2,z8,z5]),(0,[z0,z18,z1,z90,z8,z5,z6]),(0,[z362,z0,z1,z2,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z8,z5,z363,z6]),(0,[z364,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z365,z6]),(0,[z0,z1,z2,z8,z5,z94,z6])],[(0,[z0,z1,z2,z55,z8,z38,z5]),(1,[z0,z1,z262,z8,z5,z6]),(0,[z0,z1,z2,z366,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z6,z367]),(0,[z0,z1,z2,z8,z5,z368,z6]),(0,[z0,z1,z143,z2,z8,z11,z6]),(0,[z369,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z370,z8,z5,z6]),(1,[z0,z1,z110,z8,z5,z86]),(0,[z371,z0,z1,z2,z32,z8,z5])],[(0,[z0,z1,z2,z8,z372,z5,z6]),(0,[z120,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z373,z6]),(0,[z0,z10,z1,z2,z8,z332,z6]),(0,[z0,z1,z2,z8,z5,z6,z86])],[(0,[z0,z18,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z8,z5,z98,z86]),(0,[z0,z1,z2,z8,z374,z5,z6]),(0,[z0,z375,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z376,z5,z6]),(0,[z0,z49,z210,z2,z8,z5,z6]),(0,[z47,z0,z1,z2,z132,z5,z6]),(0,[z0,z377,z1,z2,z8,z5,z6]),(0,[z0,z1,z378,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z379,z5,z6]),(0,[z0,z1,z2,z380,z8,z5,z6]),(0,[z214,z0,z18,z1,z2,z8,z5])],[(0,[z0,z185,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z381,z5,z6]),(0,[z0,z1,z382,z2,z8,z5,z6]),(0,[z139,z0,z1,z2,z19,z5,z6]),(0,[z139,z0,z2,z8,z133,z5,z6]),(0,[z0,z1,z83,z2,z8,z5,z6]),(0,[z0,z1,z143,z2,z8,z338,z6])]],
   [[(0,[z0,z1,z2,z383,z8,z5,z6]),(1,[z0,z1,z384,z8,z5,z6]),(1,[z0,z29,z1,z30,z5,z6]),(0,[z0,z1,z385,z2,z8,z5,z6])],[(0,[z79,z0,z1,z2,z38,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z86]),(0,[z109,z0,z1,z8,z5,z85,z6]),(0,[z0,z1,z386,z2,z8,z5,z6])],[(0,[z0,z1,z2,z387,z8,z5,z6]),(0,[z0,z1,z2,z8,z9,z332,z6]),(1,[z0,z18,z1,z144,z8,z5])],[(0,[z0,z1,z2,z388,z8,z5,z6]),(0,[z0,z1,z2,z389,z8,z5,z6]),(1,[z0,z1,z153,z2,z8,z5]),(0,[z0,z390,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z391,z5])],[(0,[z20,z0,z1,z175,z8,z5,z6]),(0,[z26,z0,z1,z2,z8,z5,z392]),(0,[z0,z1,z2,z8,z5,z393,z6]),(0,[z0,z1,z2,z97,z32,z8,z5])],[(0,[z0,z394,z1,z2,z8,z5,z6]),(1,[z26,z1,z156,z8,z5,z6]),(0,[z395,z0,z1,z2,z8,z5,z6]),(0,[z182,z0,z1,z2,z8,z138,z6]),(0,[z0,z396,z1,z2,z8,z5,z6]),(0,[z397,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z82,z8,z30,z5]),(0,[z0,z18,z1,z324,z2,z8,z5])],[(0,[z0,z1,z2,z8,z5,z94,z98]),(0,[z0,z1,z2,z8,z398,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z332]),(0,[z0,z1,z83,z3,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z399,z6]),(0,[z0,z18,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z32,z5,z184,z6])],[(0,[z0,z1,z2,z8,z5,z158,z6]),(0,[z0,z106,z10,z2,z8,z5,z6]),(0,[z0,z1,z400,z2,z8,z5,z6]),(0,[z0,z1,z307,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z41,z5,z6])]],
   [[(1,[z0,z1,z175,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z392]),(0,[z0,z1,z401,z2,z8,z5,z6]),(1,[z0,z37,z1,z2,z8,z5]),(0,[z0,z1,z2,z32,z4,z8,z5]),(0,[z402,z0,z1,z2,z8,z5,z6]),(0,[z0,z403,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z94])],[(0,[z0,z1,z2,z404,z8,z5,z6]),(0,[z120,z0,z1,z2,z8,z5,z98]),(0,[z0,z1,z2,z405,z8,z5,z6]),(1,[z0,z1,z2,z8,z171,z6]),(0,[z0,z406,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z407,z5,z6]),(0,[z0,z18,z1,z317,z2,z8,z5]),(0,[z0,z18,z1,z2,z8,z93,z5])],[(0,[z0,z1,z408,z2,z8,z5,z6]),(0,[z0,z409,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z332,z6]),(0,[z0,z1,z2,z192,z8,z5,z6]),(0,[z0,z1,z2,z32,z410,z8,z5]),(0,[z0,z1,z2,z8,z5,z6,z213])],[(0,[z1,z2,z8,z138,z5,z9,z6]),(1,[z0,z1,z2,z8,z411,z6]),(1,[z0,z1,z400,z2,z8,z6]),(0,[z0,z1,z2,z8,z412,z5,z6]),(1,[z0,z1,z90,z8,z5,z6])],[(0,[z0,z1,z413,z2,z8,z5,z6]),(0,[z0,z1,z143,z211,z8,z5,z6]),(0,[z0,z1,z2,z414,z8,z5,z6]),(1,[z0,z10,z2,z8,z11,z6]),(0,[z0,z415,z1,z2,z8,z5,z6]),(0,[z416,z0,z1,z2,z8,z5,z6])],[(0,[z417,z0,z1,z2,z8,z5,z6]),(0,[z47,z0,z1,z2,z8,z5,z86]),(0,[z109,z0,z1,z8,z30,z5,z6]),(0,[z0,z1,z8,z338,z5,z69,z6]),(0,[z0,z1,z2,z32,z8,z8,z5]),(0,[z0,z1,z2,z8,z5,z418,z6]),(0,[z419,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z420,z6])],[(0,[z0,z1,z2,z421,z8,z5,z6]),(0,[z0,z422,z18,z1,z2,z8,z5])]],
   [[(0,[z0,z1,z2,z4,z8,z5,z6]),(0,[z423,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z85,z94]),(0,[z0,z1,z2,z32,z8,z5,z213])],[(0,[z26,z0,z1,z8,z338,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z424]),(0,[z0,z117,z1,z2,z133,z5,z6]),(0,[z0,z18,z117,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z425,z6]),(0,[z0,z1,z2,z52,z5,z184,z6]),(0,[z0,z1,z2,z8,z426,z5,z6])],[(0,[z7,z0,z1,z2,z8,z5,z322]),(0,[z0,z210,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z427,z8,z5,z6]),(0,[z0,z1,z100,z2,z8,z5,z158]),(0,[z0,z428,z1,z2,z8,z5,z6]),(0,[z0,z1,z110,z8,z5,z6,z86]),(0,[z57,z0,z1,z2,z5,z184,z6]),(0,[z0,z1,z2,z32,z192,z8,z5])],[(0,[z0,z1,z2,z8,z5,z6,z6]),(0,[z0,z1,z2,z8,z429,z5,z6]),(0,[z0,z1,z143,z2,z8,z332,z6]),(0,[z0,z422,z1,z2,z8,z5,z6])],[(1,[z0,z430,z2,z8,z5,z6]),(0,[z0,z1,z2,z192,z8,z9,z6]),(0,[z0,z1,z2,z32,z8,z5,z9]),(0,[z0,z1,z2,z8,z138,z332,z6]),(0,[z0,z1,z2,z8,z138,z6,z213]),(0,[z0,z1,z2,z8,z5,z98,z6]),(0,[z0,z1,z2,z8,z5,z6,z431]),(0,[z432,z0,z1,z2,z8,z5,z6]),(1,[z0,z433,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z434])],[(0,[z435,z0,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z173]),(0,[z0,z1,z2,z32,z8,z52,z5]),(0,[z0,z1,z2,z154,z32,z8,z5])],[(0,[z20,z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z436,z5,z6]),(0,[z26,z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z437,z5,z6]),(0,[z0,z1,z2,z8,z438,z5,z6]),(0,[z0,z1,z2,z8,z5,z439,z6])],[(0,[z0,z1,z2,z8,z5,z440,z6])]],
   [[(0,[z1,z36,z2,z156,z8,z5,z6]),(0,[z79,z0,z1,z2,z8,z5,z6]),(0,[z0,z210,z1,z100,z8,z5,z6]),(0,[z0,z441,z1,z2,z8,z5,z6]),(0,[z0,z1,z442,z2,z8,z5,z6]),(0,[z443,z0,z1,z2,z8,z5,z6]),(0,[z0,z444,z1,z2,z8,z5,z6])],[(1,[z182,z1,z2,z8,z138,z6]),(0,[z0,z1,z2,z445,z8,z5,z6]),(0,[z0,z49,z1,z2,z8,z411,z6]),(0,[z0,z1,z2,z8,z446,z5,z6]),(0,[z447,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z448,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z6]),(0,[z169,z0,z1,z2,z32,z8,z5])],[(0,[z22,z0,z1,z2,z32,z8,z5]),(0,[z26,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z121,z213]),(0,[z0,z449,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z450,z8,z5,z6]),(0,[z0,z282,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z6,z451])],[(0,[z0,z1,z2,z8,z5,z6,z452]),(0,[z0,z18,z1,z36,z2,z8,z5]),(1,[z7,z1,z2,z8,z9,z6]),(0,[z39,z1,z2,z8,z5,z98,z6]),(0,[z0,z1,z2,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z303]),(0,[z0,z1,z317,z2,z8,z6,z213])],[(0,[z453,z0,z1,z2,z8,z5,z6]),(1,[z0,z454,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z121,z239]),(0,[z0,z1,z100,z2,z8,z5,z187]),(0,[z0,z117,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z455,z8,z5]),(0,[z0,z456,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z457,z5,z6]),(0,[z458,z0,z1,z2,z8,z5,z6])],[(0,[z20,z22,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z459]),(0,[z0,z1,z2,z460,z8,z5,z6]),(0,[z0,z1,z461,z2,z8,z5,z6]),(0,[z462,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z463,z6]),(0,[z0,z1,z2,z464,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z85]),(1,[z0,z465,z1,z2,z5,z6])],[(0,[z0,z1,z466,z2,z8,z5,z6]),(0,[z467,z0,z1,z2,z8,z5,z6]),(0,[z468,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z149])],[(0,[z0,z18,z1,z2,z8,z138,z5]),(0,[z0,z1,z2,z8,z5,z6,z469]),(0,[z0,z1,z2,z8,z33,z5,z6])]],
   [[(0,[z57,z0,z1,z2,z8,z138,z6]),(0,[z0,z1,z2,z470,z8,z5,z6]),(0,[z0,z1,z471,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z472])],[(0,[z473,z0,z1,z2,z8,z5,z6]),(0,[z35,z0,z1,z36,z8,z5,z6]),(0,[z1,z2,z4,z8,z38,z5,z6]),(0,[z47,z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z85,z6]),(0,[z0,z1,z317,z2,z8,z93,z6])],[(0,[z474,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z475,z2,z8,z5,z6]),(0,[z0,z10,z2,z8,z133,z5,z6]),(0,[z0,z1,z2,z455,z8,z5,z6]),(0,[z0,z117,z1,z2,z19,z5,z6]),(0,[z0,z1,z2,z8,z476,z5,z6]),(0,[z0,z1,z477,z2,z8,z5,z6]),(0,[z0,z1,z478,z2,z8,z5,z6])],[(0,[z479,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z480,z2,z8,z5,z6]),(0,[z481,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z482,z5,z6]),(0,[z0,z1,z2,z8,z5,z483,z6])],[(0,[z0,z1,z2,z8,z484,z5,z6]),(1,[z57,z0,z18,z1,z2,z5])],[(0,[z0,z1,z2,z19,z38,z5,z6]),(0,[z0,z1,z2,z8,z5,z485,z6]),(0,[z0,z486,z1,z2,z8,z5,z6]),(0,[z0,z10,z1,z2,z8,z11,z6]),(0,[z47,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z487,z5,z6]),(0,[z57,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z211,z8,z338,z5,z6]),(0,[z0,z488,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z133,z5]),(0,[z308,z0,z18,z1,z2,z8,z5])],[(0,[z0,z1,z2,z32,z8,z5,z98])]],
   [[(0,[z0,z1,z2,z8,z5,z489,z6]),(0,[z0,z68,z1,z2,z8,z11,z6]),(0,[z0,z1,z2,z8,z490,z5,z6])],[(0,[z491,z0,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z13]),(0,[z0,z1,z2,z8,z492,z5,z6]),(0,[z0,z1,z2,z19,z5,z184,z6]),(0,[z47,z0,z1,z2,z8,z5,z85]),(0,[z0,z1,z75,z2,z8,z30,z5]),(0,[z109,z0,z1,z83,z8,z5,z6])],[(0,[z493,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z494,z8,z5,z6]),(0,[z0,z18,z29,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z306,z5,z6]),(0,[z0,z1,z2,z8,z5,z495,z6]),(0,[z57,z0,z1,z2,z192,z5,z6])],[(1,[z20,z23,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z5,z6]),(0,[z0,z18,z1,z83,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z496,z6]),(0,[z0,z1,z2,z32,z8,z5,z53]),(0,[z0,z1,z317,z2,z8,z5,z94])],[(0,[z0,z18,z210,z1,z2,z8,z5]),(0,[z0,z497,z1,z2,z8,z5,z6])],[(0,[z498,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z38,z30,z5,z6]),(0,[z7,z1,z2,z8,z5,z9,z6]),(0,[z0,z1,z2,z8,z5,z499,z6]),(0,[z0,z1,z2,z8,z5,z500,z6]),(0,[z0,z49,z100,z2,z8,z5,z6]),(0,[z0,z501,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z502,z5,z6]),(0,[z0,z1,z2,z8,z30,z5,z6]),(0,[z0,z68,z1,z2,z8,z338,z6]),(0,[z0,z18,z1,z2,z52,z5,z6]),(0,[z0,z18,z1,z2,z8,z5,z184])],[(0,[z20,z0,z1,z232,z8,z5,z6]),(0,[z0,z1,z2,z8,z503,z5,z6]),(0,[z0,z1,z2,z8,z5,z504,z6])],[(0,[z0,z1,z2,z8,z5,z6,z505]),(0,[z0,z1,z506,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z11,z9,z6]),(0,[z0,z1,z2,z8,z5,z85,z98]),(0,[z57,z0,z1,z2,z8,z53,z6])]],
   [[(0,[z0,z1,z2,z8,z5,z6,z507]),(0,[z0,z1,z2,z4,z30,z5,z6]),(0,[z120,z0,z1,z2,z8,z5,z121]),(0,[z0,z167,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z52,z5,z6]),(0,[z0,z18,z1,z2,z32,z8,z5])],[(0,[z139,z0,z1,z2,z133,z5,z6]),(0,[z508,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z509])],[(1,[z22,z185,z2,z8,z5,z6]),(0,[z0,z510,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z187]),(0,[z0,z1,z2,z8,z288,z5,z6]),(0,[z0,z1,z2,z8,z5,z511,z6])],[(0,[z35,z1,z36,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z38,z5]),(0,[z0,z1,z2,z8,z5,z6,z512]),(1,[z0,z68,z1,z8,z338,z6]),(0,[z0,z1,z317,z2,z8,z5,z213])],[(0,[z0,z1,z2,z8,z5,z513,z6]),(0,[z0,z1,z2,z514,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z515,z6]),(1,[z0,z1,z2,z8,z233,z6]),(0,[z516,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z517,z8,z5,z6]),(0,[z0,z1,z143,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z93,z94,z6])],[(0,[z0,z1,z430,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z138,z5,z6]),(0,[z0,z1,z2,z8,z338,z138,z6]),(1,[z0,z1,z2,z8,z492,z6]),(0,[z0,z1,z2,z518,z8,z5,z6]),(0,[z0,z519,z1,z2,z8,z5,z6])],[(0,[z186,z0,z1,z2,z8,z5,z125]),(0,[z7,z0,z1,z2,z8,z138,z6]),(0,[z0,z520,z1,z2,z8,z5,z6])],[(1,[z0,z1,z2,z8,z484,z6]),(0,[z0,z1,z521,z2,z8,z5,z6]),(0,[z0,z1,z2,z19,z4,z5,z6]),(0,[z0,z1,z522,z2,z8,z5,z6]),(0,[z0,z1,z100,z8,z338,z5,z6]),(0,[z0,z1,z2,z8,z5,z523,z6]),(0,[z0,z1,z2,z304,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z524])]],
   [[(1,[z0,z1,z2,z8,z5,z311]),(0,[z525,z0,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z245,z6]),(1,[z0,z1,z2,z8,z5,z191]),(0,[z0,z106,z1,z2,z192,z8,z6]),(0,[z0,z1,z2,z8,z5,z526,z6]),(0,[z0,z527,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z528,z6])],[(0,[z529,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z218,z121]),(0,[z0,z1,z2,z8,z530,z5,z6])],[(0,[z0,z1,z143,z100,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z531,z6]),(0,[z0,z1,z400,z2,z8,z30,z6]),(0,[z0,z1,z2,z8,z5,z86,z213]),(0,[z0,z1,z2,z532,z8,z5,z6])],[(0,[z7,z0,z1,z2,z8,z5,z6])],[(0,[z0,z533,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z27,z5,z6]),(0,[z0,z1,z2,z8,z534,z5,z6]),(0,[z139,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z19,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z11,z5]),(1,[z0,z1,z2,z192,z52,z6]),(0,[z0,z1,z2,z8,z159,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z535]),(0,[z0,z1,z2,z32,z8,z5,z184]),(0,[z0,z1,z317,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z319,z6]),(0,[z536,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z267,z5,z6]),(1,[z0,z261,z1,z2,z8,z6]),(0,[z0,z1,z2,z8,z5,z537,z6]),(0,[z0,z310,z1,z2,z8,z5,z6])],[(0,[z538,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z539,z6]),(0,[z0,z1,z2,z8,z5,z6,z540]),(0,[z0,z1,z2,z541,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z542])],[(0,[z0,z1,z23,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z543,z6]),(0,[z0,z1,z544,z2,z8,z5,z6])]],
   [[(0,[z20,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z6,z392]),(0,[z182,z7,z1,z2,z8,z5,z6]),(0,[z0,z1,z100,z2,z8,z5,z6]),(0,[z0,z18,z10,z1,z2,z8,z5]),(0,[z0,z18,z1,z2,z8,z5,z545])],[(0,[z26,z0,z1,z2,z8,z78,z6]),(0,[z0,z68,z1,z2,z8,z332,z6]),(0,[z0,z10,z1,z384,z8,z5,z6]),(0,[z57,z0,z10,z1,z2,z8,z6]),(0,[z0,z1,z2,z32,z8,z338,z5]),(0,[z0,z1,z546,z2,z8,z5,z6]),(0,[z275,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z6,z547])],[(1,[z0,z1,z2,z8,z5,z271]),(1,[z0,z18,z1,z2,z133,z5]),(0,[z0,z1,z548,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z549,z5,z6]),(0,[z0,z550,z1,z2,z8,z5,z6]),(0,[z0,z1,z110,z2,z8,z5,z86])],[(0,[z551,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z552,z6])],[(0,[z26,z1,z2,z156,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z553,z6]),(0,[z0,z554,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z32,z8,z5]),(0,[z0,z283,z1,z2,z32,z8,z5])],[(0,[z0,z1,z2,z8,z5,z555,z6]),(1,[z0,z1,z2,z8,z78,z6]),(0,[z0,z1,z556,z2,z8,z5,z6]),(0,[z79,z1,z2,z8,z38,z5,z6]),(0,[z0,z1,z2,z557,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z558]),(0,[z163,z0,z1,z2,z8,z5,z6]),(0,[z559,z0,z1,z2,z8,z5,z6]),(0,[z0,z433,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z391,z5,z6])],[(0,[z0,z1,z2,z8,z5,z6,z560]),(0,[z0,z1,z561,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z562,z6]),(0,[z563,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z564,z6]),(0,[z565,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z218,z6]),(0,[z0,z566,z18,z1,z2,z8,z5])]],
   [[(0,[z567,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z568,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z121]),(0,[z0,z106,z1,z2,z32,z8,z5]),(0,[z0,z29,z1,z2,z30,z5,z6])],[(0,[z0,z1,z2,z569,z8,z5,z6]),(0,[z182,z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z570,z6]),(0,[z0,z1,z2,z571,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z572,z6]),(0,[z0,z1,z295,z2,z32,z8,z5])],[(0,[z0,z1,z573,z2,z8,z5,z6]),(0,[z574,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z36,z2,z8,z5,z6]),(0,[z0,z575,z1,z2,z8,z5,z6]),(0,[z0,z566,z1,z2,z8,z5,z6]),(0,[z0,z1,z576,z2,z8,z5,z6]),(0,[z0,z1,z2,z577,z8,z5,z6])],[(0,[z0,z1,z143,z8,z5,z69,z6]),(0,[z0,z1,z2,z8,z5,z6,z434]),(0,[z0,z1,z2,z8,z5,z6,z578])],[(1,[z0,z1,z2,z27,z5,z6]),(0,[z0,z579,z1,z2,z8,z5,z6]),(0,[z182,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z580,z6]),(0,[z0,z1,z153,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z581,z6]),(0,[z0,z1,z2,z8,z5,z6,z173]),(0,[z582,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z121,z86]),(0,[z0,z1,z2,z32,z8,z5,z121]),(0,[z0,z29,z1,z2,z32,z8,z5]),(1,[z0,z1,z2,z8,z5,z178]),(0,[z109,z0,z1,z2,z8,z5,z86]),(0,[z0,z583,z1,z2,z8,z5,z6]),(0,[z371,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z584,z6])],[(0,[z0,z1,z2,z8,z5,z585,z6])]],
   [[(0,[z586,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z144,z8,z5]),(0,[z0,z1,z2,z8,z5,z587,z6])],[(1,[z0,z1,z2,z54,z5,z6]),(0,[z0,z18,z1,z2,z3,z8,z5])],[(0,[z0,z49,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z32,z8,z5,z418])],[(0,[z26,z0,z430,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z9,z69,z6]),(0,[z0,z1,z2,z8,z5,z545,z6])],[(0,[z588,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z459,z6]),(0,[z0,z1,z2,z589,z8,z5,z6]),(0,[z120,z0,z1,z2,z8,z233,z6]),(0,[z0,z1,z2,z5,z184,z6,z149])],[(1,[z0,z1,z2,z74,z5,z6]),(0,[z0,z454,z1,z2,z8,z5,z6]),(0,[z0,z590,z1,z2,z8,z5,z6]),(0,[z120,z0,z1,z2,z8,z492,z6]),(0,[z0,z1,z2,z8,z5,z218,z98]),(0,[z0,z1,z2,z591,z8,z5,z6]),(0,[z0,z1,z2,z410,z8,z5,z6])],[(0,[z0,z1,z2,z592,z8,z5,z6]),(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z8,z5,z85,z121]),(0,[z0,z1,z593,z2,z8,z5,z6]),(0,[z0,z1,z75,z2,z8,z5,z6]),(0,[z0,z1,z2,z594,z8,z5,z6])],[(0,[z79,z0,z18,z1,z2,z8,z5]),(0,[z182,z0,z1,z2,z8,z9,z6]),(0,[z0,z1,z595,z2,z8,z5,z6])]],
   [[(0,[z0,z596,z1,z2,z8,z5,z6]),(0,[z597,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z598,z2,z8,z5,z6]),(0,[z0,z1,z599,z2,z8,z5,z6]),(0,[z0,z10,z117,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z332]),(0,[z600,z0,z1,z2,z8,z5,z6]),(0,[z0,z601,z18,z1,z2,z8,z5])],[(0,[z186,z0,z1,z2,z38,z5,z6]),(0,[z0,z602,z1,z2,z8,z5,z6]),(0,[z0,z1,z603,z2,z8,z5,z6]),(0,[z0,z68,z1,z8,z338,z5,z6])],[(0,[z0,z18,z1,z2,z156,z8,z5]),(0,[z0,z1,z604,z2,z8,z5,z6]),(0,[z0,z1,z110,z2,z8,z5,z6])],[(0,[z0,z1,z2,z605,z8,z5,z6]),(0,[z26,z0,z454,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z606,z6]),(0,[z0,z1,z2,z8,z5,z411,z6]),(0,[z607,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z69,z6]),(0,[z0,z1,z2,z32,z8,z93,z5])],[(0,[z26,z0,z1,z2,z8,z5,z459]),(0,[z0,z1,z2,z156,z32,z8,z5]),(0,[z0,z601,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z608,z6]),(0,[z0,z609,z1,z2,z8,z5,z6]),(0,[z0,z100,z2,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z610,z6]),(0,[z0,z1,z2,z8,z611,z5,z6])],[(0,[z0,z1,z2,z8,z5,z612,z6]),(0,[z0,z1,z2,z8,z306,z30,z6]),(0,[z468,z0,z18,z1,z2,z8,z5])],[(0,[z613,z0,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z161,z6]),(0,[z0,z614,z1,z2,z8,z5,z6]),(0,[z0,z1,z110,z2,z8,z5,z85]),(0,[z57,z0,z433,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z93,z5,z213]),(0,[z0,z1,z2,z8,z94,z6,z213])],[(0,[z0,z10,z1,z2,z8,z5,z6])]],
   [[(0,[z0,z1,z615,z2,z8,z5,z6]),(0,[z39,z120,z1,z2,z8,z5,z6]),(1,[z0,z106,z2,z8,z332,z6]),(0,[z0,z1,z2,z8,z5,z616,z6]),(0,[z0,z617,z1,z2,z8,z5,z6])],[(0,[z0,z185,z2,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z618,z5,z6]),(0,[z0,z1,z2,z619,z8,z5,z6]),(0,[z0,z1,z620,z2,z8,z5,z6]),(0,[z0,z621,z1,z2,z8,z5,z6]),(0,[z0,z1,z622,z2,z8,z5,z6]),(0,[z0,z623,z1,z2,z8,z5,z6])],[(0,[z0,z106,z1,z2,z8,z11,z6]),(0,[z0,z1,z83,z2,z30,z5,z6]),(0,[z0,z68,z1,z2,z8,z5,z6]),(0,[z0,z1,z90,z2,z8,z5,z6]),(0,[z0,z624,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z625,z8,z5,z6]),(0,[z0,z1,z2,z626,z8,z5,z6])],[(0,[z0,z1,z627,z8,z5,z9,z6]),(0,[z120,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z628,z5,z6]),(0,[z57,z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z6,z629])],[(0,[z35,z0,z1,z8,z338,z5,z6]),(0,[z0,z1,z2,z8,z138,z69,z6]),(0,[z630,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z631,z6])],[(0,[z0,z1,z2,z8,z5,z632,z6]),(0,[z0,z1,z2,z8,z633,z5,z6]),(0,[z109,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z192,z8,z52,z6]),(0,[z634,z0,z18,z1,z2,z8,z5])],[(0,[z0,z1,z2,z8,z635,z5,z6]),(0,[z0,z117,z1,z2,z8,z5,z303]),(0,[z636,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z144,z8,z5,z6])]],
   [[(0,[z0,z185,z1,z2,z32,z8,z5]),(0,[z0,z637,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z638]),(0,[z0,z1,z2,z384,z8,z5,z6]),(0,[z0,z1,z83,z2,z32,z8,z5]),(0,[z0,z18,z1,z2,z8,z5,z69])],[(0,[z0,z1,z2,z8,z639,z5,z6]),(0,[z0,z1,z2,z8,z52,z5,z434])],[(0,[z640,z0,z1,z2,z8,z5,z6]),(0,[z634,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z641,z5,z6]),(0,[z109,z0,z1,z2,z8,z5,z85]),(0,[z0,z1,z2,z8,z5,z6,z149])],[(0,[z0,z642,z1,z2,z8,z5,z6]),(0,[z186,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z8,z5,z643,z6]),(0,[z0,z1,z644,z2,z8,z5,z6]),(0,[z0,z645,z1,z2,z8,z5,z6]),(0,[z646,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z647,z5,z6]),(0,[z214,z0,z1,z2,z32,z8,z5])],[(0,[z186,z0,z18,z1,z2,z8,z5]),(1,[z0,z18,z1,z2,z19,z5]),(0,[z648,z0,z1,z2,z8,z5,z6]),(0,[z0,z18,z123,z1,z2,z8,z5]),(0,[z0,z1,z2,z5,z6,z649,z213]),(1,[z0,z1,z2,z8,z93,z94])],[(0,[z0,z1,z2,z8,z5,z13,z6]),(0,[z0,z117,z2,z8,z5,z332,z6])],[(0,[z35,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z245,z5,z6]),(0,[z0,z18,z1,z100,z2,z8,z5]),(1,[z0,z1,z143,z8,z69,z6]),(0,[z0,z1,z2,z8,z5,z650,z6])],[(0,[z651,z0,z1,z2,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z322]),(1,[z0,z1,z627,z8,z5,z6]),(0,[z0,z167,z1,z2,z8,z5,z218]),(0,[z0,z18,z1,z2,z8,z5,z218]),(0,[z0,z1,z2,z8,z5,z25,z6]),(0,[z0,z1,z2,z8,z5,z6,z649])]],
   [[(0,[z652,z0,z1,z2,z8,z5,z6]),(0,[z186,z0,z1,z2,z8,z5,z6]),(0,[z47,z0,z2,z8,z5,z218,z6]),(0,[z57,z0,z18,z1,z2,z5,z6]),(0,[z0,z1,z2,z192,z52,z5,z6]),(0,[z0,z1,z2,z32,z8,z5,z149])],[(0,[z0,z1,z2,z8,z5,z6,z653]),(0,[z0,z1,z2,z32,z8,z138,z5]),(0,[z0,z1,z654,z2,z8,z5,z6]),(0,[z0,z655,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z656,z8,z5,z6]),(1,[z0,z1,z2,z200,z5,z6]),(0,[z0,z1,z2,z657,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z658,z6]),(0,[z0,z1,z627,z2,z8,z5,z6]),(0,[z57,z0,z1,z2,z8,z9,z6]),(0,[z0,z1,z2,z8,z5,z6,z659])],[(0,[z0,z1,z2,z8,z5,z660,z6]),(0,[z0,z1,z2,z8,z661,z5,z6]),(0,[z0,z37,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z662,z5,z6]),(0,[z57,z0,z307,z2,z8,z5,z6]),(0,[z663,z0,z1,z2,z8,z5,z6])],[(0,[z0,z210,z2,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z664,z5,z6]),(0,[z0,z1,z2,z8,z5,z6,z665]),(1,[z0,z1,z317,z2,z8,z213])],[(0,[z0,z1,z2,z8,z5,z666,z6]),(0,[z0,z1,z2,z82,z8,z5,z6]),(1,[z0,z1,z2,z8,z5,z248]),(0,[z0,z1,z2,z414,z32,z8,z5])],[(0,[z0,z18,z1,z23,z2,z8,z5]),(0,[z26,z0,z1,z2,z8,z484,z6]),(0,[z0,z667,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z3,z38,z5,z6]),(0,[z0,z668,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z248,z6]),(0,[z0,z1,z669,z2,z8,z5,z6])],[(0,[z20,z0,z1,z2,z8,z5,z311]),(0,[z0,z1,z2,z670,z8,z5,z6]),(1,[z0,z18,z1,z90,z8,z5])]],
   [[(0,[z0,z671,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z672,z5,z6]),(0,[z0,z1,z2,z8,z5,z9,z6]),(0,[z139,z0,z117,z2,z8,z5,z6]),(0,[z0,z1,z2,z32,z8,z133,z5]),(0,[z0,z1,z2,z8,z673,z5,z6])],[(0,[z0,z1,z2,z8,z5,z6,z674]),(0,[z0,z1,z675,z2,z8,z5,z6]),(0,[z0,z117,z1,z2,z8,z5,z191]),(0,[z0,z1,z676,z2,z8,z5,z6]),(0,[z0,z1,z677,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z678,z6])],[(0,[z679,z0,z1,z2,z8,z5,z6]),(0,[z7,z0,z18,z1,z2,z8,z5]),(0,[z120,z1,z2,z8,z5,z6,z121]),(0,[z0,z1,z680,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z681,z5,z6]),(0,[z0,z18,z167,z1,z2,z8,z5])],[(0,[z682,z0,z1,z2,z8,z5,z6]),(0,[z683,z0,z1,z2,z8,z5,z6]),(0,[z684,z0,z1,z2,z8,z5,z6]),(0,[z139,z0,z18,z1,z2,z8,z5]),(0,[z0,z106,z1,z2,z8,z332,z6]),(0,[z0,z18,z106,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z685,z6]),(0,[z0,z29,z1,z2,z3,z5,z6]),(0,[z0,z686,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z687,z5,z6]),(1,[z0,z18,z1,z2,z32,z5])],[(0,[z688,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z38,z133,z5,z6]),(0,[z0,z1,z2,z8,z133,z5,z6]),(0,[z57,z0,z106,z1,z2,z8,z6]),(0,[z0,z2,z8,z5,z218,z6,z239])],[(0,[z26,z0,z1,z143,z8,z5,z6]),(0,[z0,z1,z689,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z690,z5,z6]),(0,[z0,z10,z1,z262,z8,z5,z6]),(0,[z0,z167,z1,z2,z8,z5,z239]),(0,[z0,z18,z1,z2,z8,z5,z239]),(0,[z0,z1,z2,z8,z338,z5,z6]),(0,[z0,z691,z1,z2,z8,z5,z6]),(1,[z0,z18,z1,z2,z5,z149]),(0,[z432,z0,z1,z2,z32,z8,z5])],[(0,[z0,z1,z2,z8,z21,z5,z6]),(1,[z186,z1,z2,z4,z5,z6]),(0,[z0,z49,z1,z211,z8,z5,z6]),(0,[z0,z18,z1,z2,z19,z8,z5]),(0,[z0,z1,z692,z2,z8,z5,z6])],[(0,[z0,z18,z1,z2,z32,z5,z6])]],
   [[(0,[z0,z1,z3,z8,z30,z5,z6]),(0,[z0,z1,z2,z8,z5,z693,z6]),(1,[z0,z1,z2,z5,z6,z649])],[(0,[z79,z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z694,z5,z6]),(0,[z1,z2,z8,z5,z98,z6,z121]),(0,[z0,z1,z2,z455,z8,z133,z5]),(0,[z0,z1,z2,z695,z8,z5,z6]),(0,[z0,z696,z1,z2,z8,z5,z6]),(0,[z0,z1,z73,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z6,z697]),(0,[z0,z1,z2,z32,z32,z8,z5]),(0,[z0,z465,z1,z2,z5,z6,z213])],[(0,[z26,z0,z1,z2,z32,z8,z5]),(0,[z698,z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z699,z5,z6]),(0,[z0,z1,z2,z211,z32,z8,z5]),(0,[z0,z1,z700,z2,z8,z5,z6])],[(0,[z0,z465,z1,z2,z8,z5,z6])],[(0,[z0,z1,z701,z2,z8,z5,z6]),(0,[z0,z1,z2,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z702,z6]),(0,[z0,z703,z1,z2,z8,z5,z6])],[(0,[z26,z0,z1,z156,z8,z5,z6]),(0,[z0,z1,z2,z8,z704,z5,z6]),(0,[z0,z1,z2,z8,z338,z9,z6]),(0,[z705,z0,z1,z2,z8,z5,z6]),(0,[z0,z2,z8,z11,z5,z332,z6]),(0,[z47,z0,z167,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z8,z5,z6]),(0,[z0,z708,z1,z8,z5,z6]),(0,[z26,z1,z156,z8,z484,z6]),(1,[z1,z2,z8,z709,z6]),(0,[z0,z18,z1,z2,z8,z411]),(0,[z0,z2,z8,z710,z5,z6]),(0,[z0,z1,z2,z711,z133,z5]),(0,[z0,z1,z2,z32,z273,z5])],[(0,[z0,z1,z2,z8,z5,z712]),(0,[z0,z1,z262,z32,z8,z5]),(0,[z0,z1,z8,z5,z85,z713]),(0,[z57,z0,z18,z1,z2,z52]),(0,[z0,z1,z2,z8,z33,z213])],[(0,[z0,z1,z2,z8,z5,z714]),(0,[z0,z68,z1,z8,z438,z6]),(0,[z0,z68,z1,z8,z715,z6]),(0,[z0,z18,z1,z716,z8,z5]),(0,[z0,z18,z1,z144,z32,z5])],[(0,[z0,z1,z83,z3,z5,z178]),(0,[z0,z1,z2,z8,z5,z717]),(0,[z0,z1,z2,z8,z5,z718]),(0,[z0,z1,z2,z52,z719,z6]),(0,[z634,z123,z1,z2,z8,z5])],[(0,[z0,z1,z175,z8,z5,z311]),(0,[z0,z1,z143,z8,z78,z6])],[(0,[z0,z1,z720,z2,z8,z5]),(0,[z0,z1,z2,z8,z721,z6]),(0,[z0,z2,z8,z11,z722,z6]),(0,[z0,z18,z1,z2,z571,z5]),(0,[z0,z18,z1,z723,z8,z5]),(0,[z0,z1,z2,z8,z6,z724])],[(0,[z0,z1,z2,z74,z319,z6]),(0,[z186,z1,z2,z725,z5,z6]),(0,[z0,z18,z1,z2,z427,z5]),(0,[z0,z18,z68,z1,z8,z338])],[(0,[z0,z1,z2,z8,z5,z726]),(0,[z7,z18,z1,z2,z8,z9]),(0,[z0,z1,z727,z8,z5,z6]),(0,[z0,z1,z680,z8,z5,z86]),(0,[z0,z728,z1,z2,z8,z5]),(0,[z0,z123,z1,z144,z8,z5]),(0,[z0,z1,z144,z8,z5,z94])]],
   [[(0,[z0,z1,z232,z74,z5,z6]),(0,[z7,z1,z2,z8,z9,z13]),(0,[z0,z1,z2,z8,z233,z121]),(0,[z1,z2,z8,z5,z98,z729])],[(0,[z0,z1,z2,z8,z5,z730]),(0,[z0,z1,z2,z8,z138,z322]),(0,[z0,z1,z2,z8,z5,z158]),(0,[z0,z1,z2,z8,z5,z731]),(0,[z0,z1,z732,z2,z8,z6]),(0,[z0,z733,z1,z2,z5,z6]),(0,[z0,z1,z73,z2,z8,z5])],[(0,[z1,z2,z8,z5,z729,z121]),(0,[z0,z261,z2,z8,z332,z6]),(0,[z57,z0,z18,z10,z1,z2])],[(0,[z1,z2,z8,z734,z5,z6]),(0,[z0,z1,z2,z8,z93,z94])],[(0,[z0,z1,z2,z32,z54,z5]),(0,[z0,z1,z2,z8,z735,z6]),(0,[z0,z18,z1,z2,z238,z5]),(0,[z0,z269,z211,z8,z5,z6]),(0,[z0,z49,z100,z8,z5,z158]),(0,[z0,z1,z2,z736,z5,z6]),(0,[z0,z310,z2,z19,z5,z6]),(0,[z0,z1,z2,z5,z6,z737]),(0,[z0,z1,z738,z2,z8,z5]),(0,[z0,z18,z204,z1,z2,z5])],[(0,[z0,z739,z2,z8,z5,z6]),(0,[z26,z1,z156,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z740]),(0,[z0,z1,z2,z8,z5,z741]),(0,[z57,z0,z18,z1,z90,z5])],[(0,[z0,z1,z2,z8,z5,z322]),(0,[z0,z1,z2,z742,z8,z5])],[(0,[z0,z430,z2,z8,z484,z6]),(0,[z0,z18,z1,z384,z8,z5]),(0,[z0,z1,z144,z8,z5,z213])]],
   [[(0,[z0,z1,z175,z32,z8,z5]),(0,[z0,z1,z2,z8,z743,z6]),(0,[z0,z1,z2,z200,z5,z6])],[(0,[z0,z261,z10,z2,z8,z6]),(0,[z0,z1,z744,z8,z5,z6]),(0,[z0,z745,z2,z8,z5,z6]),(0,[z0,z1,z477,z2,z8,z213]),(0,[z0,z1,z73,z2,z52,z5]),(0,[z0,z465,z1,z2,z32,z5])],[(0,[z0,z746,z2,z8,z5,z6]),(0,[z0,z37,z1,z2,z133,z5]),(0,[z0,z1,z2,z32,z5,z184]),(0,[z0,z1,z2,z8,z93,z418])],[(0,[z243,z1,z2,z4,z5,z6]),(0,[z0,z1,z603,z2,z8,z213]),(0,[z109,z0,z1,z8,z5,z76]),(0,[z0,z1,z90,z32,z8,z5])],[(0,[z0,z1,z2,z747,z8,z5]),(0,[z0,z1,z2,z5,z6,z748]),(0,[z0,z1,z2,z200,z5,z85])],[(0,[z0,z1,z749,z8,z5,z6]),(0,[z0,z750,z1,z2,z8,z5])],[(0,[z0,z1,z751,z8,z5,z6]),(0,[z0,z430,z143,z8,z5,z6]),(0,[z26,z1,z156,z27,z5,z6]),(0,[z0,z1,z752,z8,z5,z6]),(0,[z0,z49,z100,z8,z5,z187]),(0,[z139,z0,z2,z455,z133,z5]),(0,[z0,z18,z10,z2,z133,z5]),(0,[z0,z1,z2,z753,z5,z6])],[(0,[z0,z454,z2,z8,z484,z6]),(0,[z0,z1,z2,z32,z8,z245]),(0,[z0,z1,z2,z754,z8,z5])]],
   [[(0,[z0,z1,z175,z21,z5,z6]),(0,[z0,z1,z2,z8,z755,z6]),(0,[z0,z1,z2,z8,z319,z147]),(0,[z0,z1,z2,z8,z484,z459]),(0,[z0,z1,z32,z8,z267,z5]),(0,[z648,z1,z2,z8,z138,z6]),(0,[z1,z2,z8,z5,z729,z6]),(0,[z0,z1,z144,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z756])],[(0,[z0,z1,z2,z27,z5,z392]),(0,[z0,z1,z2,z304,z8,z33])],[(0,[z0,z1,z2,z32,z27,z5]),(0,[z26,z1,z156,z54,z5,z6]),(0,[z0,z1,z627,z8,z5,z757]),(0,[z0,z1,z2,z8,z5,z758]),(0,[z0,z1,z2,z32,z5,z235]),(0,[z0,z1,z2,z8,z5,z759]),(0,[z0,z1,z760,z8,z5,z6]),(0,[z0,z18,z1,z761,z8,z5]),(0,[z0,z18,z1,z2,z8,z762]),(0,[z0,z18,z1,z2,z32,z5])],[(0,[z0,z1,z2,z8,z5,z763])],[(0,[z0,z1,z2,z8,z764,z6]),(0,[z0,z430,z2,z32,z8,z5]),(0,[z1,z36,z765,z8,z5,z6]),(0,[z0,z1,z2,z8,z766,z6])],[(0,[z0,z430,z2,z8,z78,z6]),(0,[z186,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z455,z8,z288]),(0,[z47,z0,z2,z8,z5,z767]),(0,[z0,z18,z433,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z724])],[(0,[z0,z1,z2,z8,z768,z6]),(0,[z57,z0,z18,z1,z2,z9]),(0,[z0,z1,z2,z769,z5,z6])],[(0,[z0,z1,z2,z770,z5,z6]),(0,[z0,z1,z2,z771,z8,z5]),(0,[z0,z1,z2,z772,z8,z5]),(0,[z0,z1,z2,z5,z6,z649]),(0,[z432,z0,z2,z8,z41,z5])]],
   [[(0,[z0,z1,z773,z8,z5,z6]),(0,[z0,z430,z156,z8,z5,z6]),(0,[z774,z1,z2,z8,z5,z6]),(0,[z0,z775,z2,z32,z8,z5])],[(0,[z0,z1,z175,z74,z5,z6])],[(0,[z0,z1,z2,z776,z5,z6]),(0,[z139,z0,z2,z710,z5,z6]),(0,[z0,z18,z1,z2,z298,z5])],[(0,[z0,z1,z777,z8,z5,z6]),(0,[z683,z0,z18,z1,z2,z5]),(0,[z0,z210,z211,z8,z5,z6])],[(0,[z247,z23,z2,z8,z5,z6]),(0,[z0,z454,z2,z32,z8,z5]),(0,[z663,z1,z2,z8,z9,z6]),(0,[z0,z1,z143,z8,z352,z6])],[(0,[z0,z18,z1,z2,z8,z484]),(0,[z0,z18,z29,z1,z30,z5])],[(0,[z0,z49,z382,z8,z5,z6]),(0,[z79,z1,z2,z55,z38,z5]),(0,[z0,z1,z2,z778,z5,z6]),(0,[z0,z1,z779,z8,z5,z6])],[(0,[z0,z1,z2,z780,z5,z6]),(0,[z57,z0,z1,z2,z168,z53])]],
   [[(0,[z0,z1,z781,z8,z5,z6]),(0,[z0,z1,z8,z782,z5,z6]),(0,[z0,z1,z2,z8,z783,z6]),(0,[z0,z2,z8,z722,z332,z6]),(0,[z0,z106,z2,z32,z8,z332])],[(0,[z0,z1,z2,z8,z784,z6]),(0,[z0,z430,z2,z54,z5,z6]),(0,[z0,z210,z749,z8,z5,z6]),(0,[z109,z0,z1,z8,z391,z5]),(0,[z0,z785,z2,z32,z8,z5]),(0,[z0,z1,z295,z154,z8,z5]),(1,[z0,z1,z2,z8,z724])],[(0,[z0,z1,z2,z8,z786,z6]),(0,[z0,z1,z2,z8,z5,z25])],[(0,[z0,z1,z2,z5,z787,z6]),(0,[z1,z2,z8,z709,z9,z6]),(0,[z0,z1,z2,z788,z8,z5]),(0,[z0,z117,z2,z710,z5,z6]),(0,[z0,z18,z1,z2,z5,z203]),(0,[z0,z1,z2,z8,z5,z789])],[(0,[z0,z1,z2,z8,z790,z6]),(0,[z0,z1,z2,z8,z791,z6]),(0,[z35,z1,z8,z530,z5,z6]),(0,[z0,z1,z2,z8,z792,z6])],[(0,[z0,z454,z2,z27,z5,z6]),(0,[z0,z1,z2,z8,z5,z793]),(0,[z0,z1,z2,z455,z5,z184])],[(0,[z0,z1,z2,z27,z5,z459]),(0,[z0,z1,z2,z8,z5,z794]),(0,[z1,z2,z8,z138,z709,z6]),(0,[z39,z1,z2,z8,z5,z98]),(0,[z0,z117,z2,z32,z19,z5]),(0,[z0,z1,z2,z8,z795,z6])],[(0,[z0,z1,z796,z8,z5,z6]),(0,[z0,z1,z2,z797,z8,z5]),(0,[z0,z798,z2,z8,z5,z6]),(0,[z79,z1,z2,z725,z5,z6]),(0,[z0,z1,z2,z55,z8,z5]),(0,[z301,z0,z1,z90,z8,z5])]],
   [[(0,[z0,z1,z2,z8,z5,z799]),(0,[z0,z1,z2,z800,z8,z5]),(0,[z582,z0,z2,z133,z5,z6]),(0,[z0,z117,z2,z80,z5,z6]),(0,[z0,z1,z2,z801,z5,z6]),(0,[z0,z18,z1,z669,z2,z5])],[(0,[z0,z454,z2,z54,z5,z6]),(0,[z0,z18,z246,z1,z2,z5]),(0,[z0,z1,z8,z267,z5,z6]),(0,[z0,z18,z1,z2,z8,z802])],[(0,[z0,z1,z2,z54,z5,z459]),(0,[z371,z0,z1,z2,z8,z418])],[(1,[z0,z2,z8,z5,z767]),(0,[z47,z0,z2,z8,z41,z5]),(0,[z0,z1,z90,z144,z8,z5])],[(0,[z79,z1,z2,z38,z5,z6]),(0,[z0,z18,z1,z803,z8,z5])],[(0,[z0,z1,z2,z8,z5,z804]),(0,[z259,z185,z2,z8,z5,z6]),(0,[z0,z1,z627,z8,z78,z6]),(0,[z0,z18,z261,z1,z2,z5]),(0,[z57,z0,z18,z1,z2,z53])],[(0,[z0,z18,z1,z175,z8,z5]),(0,[z35,z18,z1,z36,z8,z5]),(0,[z0,z18,z1,z2,z5,z580]),(0,[z0,z117,z2,z19,z5,z6]),(0,[z0,z18,z1,z2,z5,z236])],[(0,[z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z75,z8,z5,z86]),(0,[z0,z1,z3,z801,z5,z6])]],
   [[(0,[z0,z1,z2,z8,z34,z6]),(0,[z0,z805,z1,z2,z8,z5]),(0,[z26,z1,z385,z8,z5,z6]),(0,[z0,z18,z1,z2,z351,z5]),(0,[z0,z806,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z807]),(0,[z369,z1,z2,z8,z5,z98]),(0,[z0,z1,z2,z8,z288,z6])],[(0,[z0,z1,z2,z32,z8,z78]),(0,[z1,z765,z156,z8,z5,z6]),(0,[z0,z18,z1,z401,z2,z5]),(0,[z57,z0,z18,z1,z2,z138]),(0,[z0,z49,z100,z8,z5,z6]),(0,[z0,z808,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z711,z5]),(0,[z0,z18,z117,z2,z19,z5]),(0,[z0,z167,z2,z8,z5,z767]),(0,[z0,z1,z2,z8,z5,z809])],[(0,[z20,z23,z2,z21,z5,z6]),(0,[z0,z1,z2,z8,z810,z6]),(1,[z0,z1,z801,z5,z6])],[(0,[z0,z2,z8,z5,z811,z6]),(0,[z0,z1,z812,z8,z5,z6]),(0,[z0,z18,z10,z2,z8,z11]),(0,[z0,z1,z2,z414,z200,z5])],[(0,[z0,z1,z2,z813,z8,z5]),(0,[z0,z1,z2,z8,z814,z6]),(0,[z0,z307,z2,z8,z138,z6]),(0,[z0,z1,z211,z8,z171,z6]),(0,[z0,z1,z143,z8,z24,z6]),(0,[z0,z1,z548,z8,z5,z86]),(0,[z0,z18,z1,z2,z5,z815]),(0,[z0,z1,z2,z5,z6,z816])],[(0,[z0,z1,z2,z8,z5,z817]),(0,[z0,z1,z8,z5,z818,z6]),(0,[z0,z1,z2,z819,z5,z6]),(0,[z0,z1,z2,z8,z820,z6]),(0,[z0,z1,z2,z8,z802,z6]),(0,[z0,z1,z2,z8,z245,z271]),(0,[z0,z1,z627,z8,z69,z6]),(0,[z0,z1,z821,z8,z5,z6]),(1,[z1,z2,z8,z5,z729]),(0,[z139,z0,z2,z32,z133,z5]),(0,[z0,z18,z1,z90,z133,z5])],[(0,[z0,z18,z1,z232,z8,z5]),(0,[z0,z1,z822,z2,z8,z5]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z0,z1,z2,z824,z8,z5]),(0,[z120,z1,z2,z8,z5,z121]),(0,[z0,z749,z211,z8,z5,z6]),(0,[z47,z0,z2,z132,z5,z218]),(0,[z308,z0,z1,z144,z8,z5]),(0,[z0,z310,z1,z144,z8,z5]),(0,[z0,z18,z1,z2,z5,z816]),(0,[z0,z2,z32,z8,z825,z5])]],
   [[(0,[z0,z1,z2,z8,z5,z125]),(0,[z57,z0,z18,z68,z1,z2]),(0,[z0,z18,z1,z2,z5,z258])],[(0,[z0,z1,z2,z8,z5,z826]),(0,[z0,z1,z2,z8,z827,z6]),(0,[z0,z1,z2,z828,z8,z5]),(0,[z0,z1,z2,z8,z5,z829]),(0,[z57,z0,z1,z2,z446,z6]),(0,[z57,z0,z1,z73,z2,z53])],[(0,[z0,z1,z232,z21,z5,z6]),(0,[z0,z1,z2,z8,z5,z830])],[(0,[z0,z831,z2,z8,z5,z6]),(0,[z0,z1,z832,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z833]),(0,[z416,z1,z2,z8,z5,z98]),(0,[z0,z261,z307,z2,z8,z6]),(0,[z47,z0,z2,z8,z5,z15]),(0,[z0,z18,z1,z83,z3,z5]),(0,[z109,z0,z1,z8,z5,z85])],[(0,[z20,z23,z2,z74,z5,z6]),(0,[z0,z1,z2,z8,z5,z834]),(0,[z0,z1,z2,z835,z8,z5]),(0,[z0,z18,z1,z836,z8,z5])],[(0,[z0,z1,z2,z837,z21,z5]),(0,[z0,z1,z2,z838,z5,z6]),(0,[z0,z1,z2,z839,z5,z6]),(0,[z0,z1,z2,z32,z8,z288]),(0,[z0,z1,z8,z5,z713,z6])],[(0,[z0,z1,z2,z840,z5,z6]),(0,[z0,z10,z2,z8,z285,z6]),(0,[z0,z1,z2,z8,z5,z841])],[(0,[z0,z1,z2,z842,z5,z6]),(0,[z0,z1,z2,z8,z843,z6]),(0,[z0,z18,z310,z2,z19,z5]),(0,[z0,z10,z2,z8,z722,z6]),(0,[z0,z844,z2,z8,z5,z6]),(0,[z0,z1,z143,z8,z69,z173]),(0,[z0,z1,z143,z32,z8,z69]),(0,[z0,z68,z1,z8,z274,z6]),(0,[z0,z18,z1,z845,z8,z5])]],
   [[(0,[z0,z1,z2,z27,z484,z6]),(0,[z0,z1,z2,z846,z5,z6]),(0,[z0,z847,z1,z2,z8,z5])],[(0,[z0,z1,z2,z8,z319,z6]),(0,[z0,z1,z2,z8,z5,z147]),(0,[z0,z848,z1,z2,z8,z5]),(0,[z0,z18,z1,z2,z74,z5]),(0,[z0,z1,z2,z8,z849,z6]),(0,[z0,z1,z2,z8,z850,z6]),(0,[z0,z655,z1,z2,z32,z5]),(0,[z0,z29,z1,z75,z30,z5]),(0,[z0,z851,z1,z2,z8,z5])],[(0,[z0,z1,z2,z8,z34,z147]),(0,[z0,z1,z2,z8,z852,z6]),(0,[z0,z1,z2,z8,z5,z853]),(0,[z0,z1,z2,z8,z5,z854]),(0,[z0,z18,z855,z2,z8,z5])],[(0,[z0,z1,z2,z856,z8,z5]),(0,[z0,z18,z1,z2,z690,z5]),(0,[z0,z1,z2,z8,z5,z857]),(0,[z169,z1,z2,z410,z8,z5]),(0,[z0,z1,z2,z32,z5,z649])],[(0,[z0,z858,z1,z2,z21,z5]),(0,[z0,z1,z2,z54,z484,z6]),(0,[z0,z18,z1,z2,z8,z161]),(0,[z0,z18,z1,z627,z8,z5]),(0,[z0,z1,z2,z8,z5,z859]),(0,[z0,z1,z860,z2,z8,z5])],[(0,[z0,z861,z2,z8,z5,z6]),(0,[z0,z1,z862,z8,z5,z6]),(0,[z120,z1,z2,z8,z5,z729]),(0,[z0,z1,z144,z8,z5,z121]),(0,[z0,z1,z8,z715,z5,z6])],[(0,[z0,z1,z2,z32,z8,z34]),(0,[z0,z1,z2,z8,z863,z6]),(0,[z0,z1,z2,z8,z5,z864]),(0,[z7,z1,z2,z8,z9,z322]),(0,[z7,z1,z627,z8,z9,z6]),(0,[z0,z2,z8,z5,z722,z6]),(0,[z0,z1,z2,z8,z5,z76])],[(0,[z0,z1,z2,z32,z8,z484]),(0,[z0,z865,z2,z8,z5,z6]),(1,[z0,z18,z261,z1,z2]),(0,[z0,z18,z261,z1,z2,z133]),(0,[z0,z1,z2,z866,z8,z5]),(0,[z508,z0,z18,z1,z2,z5]),(0,[z0,z1,z716,z8,z5,z6]),(0,[z0,z867,z2,z32,z8,z5])]],
   [[(0,[z0,z868,z2,z8,z5,z6])],[(0,[z0,z1,z2,z74,z5,z311]),(0,[z0,z18,z106,z2,z8,z332]),(0,[z0,z18,z1,z2,z8,z306]),(0,[z0,z1,z317,z2,z649,z213])],[(0,[z35,z1,z36,z32,z8,z5]),(0,[z646,z0,z2,z133,z5,z6]),(0,[z0,z1,z2,z132,z5,z6]),(0,[z0,z29,z1,z400,z30,z6])],[(0,[z0,z18,z1,z2,z8,z319]),(0,[z0,z637,z211,z8,z5,z6]),(0,[z0,z869,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z192,z52])],[(0,[z0,z870,z2,z8,z5,z6]),(0,[z0,z1,z2,z5,z871,z6]),(0,[z0,z1,z8,z338,z420,z6]),(0,[z0,z1,z2,z8,z5,z872]),(0,[z0,z1,z2,z8,z5,z873]),(0,[z0,z1,z627,z8,z5,z874]),(0,[z0,z1,z2,z8,z875,z5]),(0,[z0,z1,z2,z8,z5,z876]),(0,[z0,z1,z2,z8,z5,z877]),(0,[z0,z1,z2,z878,z5,z6])],[(0,[z1,z879,z2,z8,z5,z6]),(0,[z362,z1,z2,z8,z5,z98]),(1,[z0,z1,z2,z719,z6])],[(0,[z20,z23,z2,z8,z5,z147]),(0,[z0,z1,z2,z27,z78,z6]),(0,[z0,z880,z1,z2,z8,z5]),(0,[z35,z1,z765,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z187]),(0,[z0,z1,z761,z8,z5,z6]),(0,[z0,z1,z881,z2,z8,z6]),(0,[z0,z1,z110,z8,z5,z86])],[(0,[z0,z1,z2,z8,z882,z6]),(0,[z879,z23,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z883]),(0,[z26,z1,z765,z8,z5,z6]),(0,[z1,z2,z765,z8,z5,z6]),(0,[z0,z1,z2,z19,z5,z191]),(0,[z0,z884,z1,z2,z8,z5]),(0,[z0,z1,z885,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z8,z886,z6]),(0,[z0,z1,z2,z8,z5,z887]),(0,[z305,z0,z1,z8,z5,z85]),(0,[z888,z1,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z5,z277]),(0,[z0,z1,z2,z8,z889,z6]),(0,[z57,z0,z1,z2,z53,z6]),(0,[z0,z1,z2,z52,z5,z815]),(0,[z0,z890,z2,z32,z8,z5])],[(0,[z0,z1,z413,z3,z5,z6]),(0,[z0,z100,z749,z8,z5,z6]),(0,[z0,z18,z2,z133,z5,z332])],[(0,[z0,z18,z1,z2,z21,z5]),(0,[z0,z1,z2,z54,z78,z6]),(0,[z0,z1,z2,z8,z5,z891]),(0,[z0,z283,z2,z8,z5,z239])],[(0,[z0,z892,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z9,z322]),(0,[z0,z1,z893,z8,z5,z6]),(0,[z894,z18,z1,z2,z8,z5])],[(0,[z0,z1,z384,z8,z5,z6]),(0,[z0,z18,z1,z2,z309,z5])],[(0,[z0,z1,z232,z8,z319,z6]),(0,[z0,z1,z232,z8,z5,z147]),(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z1,z2,z5,z184,z434]),(0,[z0,z18,z1,z2,z611,z5])],[(1,[z1,z765,z8,z5,z6]),(0,[z0,z1,z2,z725,z5,z6]),(0,[z0,z896,z1,z2,z8,z5]),(0,[z0,z1,z2,z192,z580,z6]),(0,[z0,z1,z143,z8,z336,z6]),(0,[z0,z1,z262,z8,z11,z6]),(0,[z0,z18,z1,z2,z695,z5]),(0,[z0,z18,z1,z144,z8,z5]),(0,[z0,z465,z1,z317,z2,z5])],[(0,[z0,z848,z1,z2,z74,z5]),(0,[z1,z2,z8,z725,z5,z6]),(0,[z0,z1,z897,z8,z5,z6]),(0,[z186,z1,z2,z32,z4,z5]),(0,[z139,z0,z2,z133,z5,z6]),(0,[z0,z1,z153,z2,z8,z5]),(0,[z0,z1,z2,z898,z8,z5]),(0,[z894,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z168])]],
   [[(0,[z0,z1,z2,z8,z899,z6]),(0,[z0,z1,z2,z8,z5,z900]),(0,[z0,z901,z2,z8,z5,z6])],[(0,[z0,z1,z2,z837,z8,z5]),(0,[z902,z0,z1,z2,z5,z6]),(0,[z0,z903,z2,z8,z5,z6]),(0,[z0,z18,z261,z1,z2,z8]),(0,[z0,z1,z2,z904,z8,z5])],[(0,[z0,z1,z905,z2,z8,z5]),(0,[z906,z1,z2,z8,z5,z6]),(0,[z0,z422,z1,z144,z8,z5])],[(0,[z39,z1,z2,z8,z5,z729])],[(0,[z0,z1,z175,z8,z5,z6]),(0,[z0,z160,z211,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z392]),(0,[z0,z1,z2,z8,z161,z271]),(0,[z0,z907,z2,z8,z5,z6]),(0,[z0,z1,z908,z2,z8,z5]),(0,[z0,z167,z2,z8,z5,z425]),(0,[z0,z1,z83,z3,z5,z76]),(0,[z0,z1,z143,z8,z69,z248])],[(0,[z0,z1,z175,z8,z34,z6]),(0,[z0,z1,z2,z8,z5,z909]),(0,[z0,z879,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z171,z6]),(0,[z0,z1,z2,z8,z910,z6]),(1,[z0,z18,z307,z2,z5]),(0,[z0,z18,z1,z2,z8,z766])],[(0,[z0,z430,z36,z8,z5,z6]),(0,[z0,z1,z2,z797,z27,z5]),(0,[z911,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z912,z8,z5]),(0,[z0,z1,z2,z8,z5,z713]),(0,[z0,z18,z1,z144,z52,z5])],[(0,[z0,z1,z2,z8,z5,z913]),(0,[z0,z1,z627,z192,z8,z6]),(0,[z0,z1,z2,z8,z5,z914]),(0,[z47,z0,z2,z8,z5,z218])]],
   [[(0,[z0,z858,z1,z2,z8,z5]),(0,[z0,z430,z2,z27,z5,z6]),(0,[z0,z49,z100,z8,z171,z6]),(0,[z0,z1,z915,z2,z8,z5]),(0,[z0,z18,z1,z90,z19,z5]),(0,[z0,z10,z2,z8,z11,z6])],[(0,[z0,z1,z144,z8,z5,z98]),(0,[z0,z18,z1,z262,z8,z5]),(0,[z57,z0,z1,z2,z51,z6]),(0,[z0,z1,z209,z8,z5,z85]),(0,[z57,z0,z18,z1,z144,z5]),(0,[z0,z1,z2,z32,z5,z816])],[(0,[z0,z1,z2,z8,z5,z916]),(0,[z0,z49,z100,z8,z411,z6]),(0,[z57,z0,z18,z106,z1,z2]),(0,[z0,z1,z2,z8,z5,z917])],[(0,[z0,z1,z2,z8,z918,z6]),(0,[z0,z1,z100,z8,z171,z6]),(0,[z0,z550,z2,z8,z11,z6]),(0,[z0,z1,z2,z8,z919,z5]),(0,[z0,z18,z920,z2,z8,z5])],[(0,[z0,z1,z8,z338,z715,z6])],[(0,[z0,z1,z2,z921,z5,z6]),(0,[z0,z922,z2,z8,z5,z6]),(0,[z79,z18,z1,z2,z38,z5]),(0,[z0,z1,z2,z32,z8,z411]),(0,[z0,z1,z2,z8,z5,z923])],[(0,[z0,z1,z2,z924,z5,z6]),(0,[z0,z1,z2,z925,z8,z5]),(0,[z0,z1,z2,z8,z5,z926]),(0,[z77,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z8,z152,z94]),(0,[z0,z1,z2,z8,z5,z927]),(0,[z109,z0,z1,z8,z5,z713])],[(0,[z0,z1,z8,z928,z5,z6]),(0,[z0,z1,z2,z8,z5,z929]),(0,[z57,z0,z18,z1,z143,z2]),(0,[z0,z68,z307,z2,z8,z6]),(0,[z930,z18,z1,z2,z8,z5])]],
   [[(0,[z0,z1,z2,z8,z931,z6]),(0,[z0,z1,z2,z8,z5,z932]),(0,[z0,z933,z2,z8,z5,z6]),(0,[z0,z344,z211,z8,z5,z6]),(0,[z0,z433,z2,z8,z5,z6]),(0,[z0,z1,z8,z5,z76,z86]),(0,[z0,z1,z8,z5,z713,z86]),(0,[z0,z1,z2,z8,z5,z434])],[(0,[z0,z1,z2,z8,z934,z6]),(1,[z0,z1,z8,z5,z713]),(0,[z0,z1,z2,z8,z724,z213])],[(0,[z0,z2,z8,z5,z6,z935]),(0,[z64,z0,z2,z8,z5,z218]),(0,[z0,z2,z19,z710,z5,z6]),(0,[z0,z307,z2,z5,z184,z6])],[(0,[z182,z18,z1,z2,z8,z138]),(0,[z0,z1,z2,z936,z5,z6]),(0,[z937,z1,z2,z8,z5,z6]),(0,[z930,z1,z2,z8,z5,z6])],[(0,[z7,z1,z2,z32,z8,z9]),(0,[z0,z465,z1,z2,z138,z6]),(0,[z0,z1,z938,z8,z5,z6]),(0,[z0,z775,z2,z8,z5,z6]),(0,[z0,z1,z8,z801,z5,z6])],[(0,[z0,z185,z175,z8,z5,z6]),(0,[z0,z1,z2,z200,z5,z218]),(0,[z0,z1,z2,z8,z715,z6])],[(0,[z0,z18,z1,z2,z8,z5]),(0,[z0,z1,z175,z8,z319,z6]),(0,[z0,z1,z175,z8,z5,z147]),(0,[z0,z1,z2,z8,z939,z6]),(0,[z0,z940,z2,z8,z5,z6]),(0,[z0,z941,z1,z2,z8,z5]),(0,[z0,z1,z2,z32,z8,z161]),(0,[z57,z0,z1,z2,z545,z6]),(0,[z371,z0,z465,z1,z2,z5])],[(0,[z0,z1,z942,z8,z5,z6]),(0,[z0,z1,z627,z32,z8,z5]),(0,[z0,z1,z262,z8,z332,z6]),(0,[z0,z18,z1,z90,z32,z5])]],
   [[(0,[z0,z454,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z943]),(0,[z0,z488,z1,z8,z338,z6]),(0,[z0,z1,z2,z944,z8,z5]),(0,[z0,z1,z945,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z459]),(0,[z0,z1,z946,z2,z8,z6]),(0,[z0,z465,z1,z2,z5,z6]),(0,[z0,z18,z1,z90,z5,z149])],[(0,[z186,z1,z2,z4,z245,z6]),(0,[z0,z1,z2,z8,z5,z729]),(1,[z0,z2,z8,z722,z6]),(0,[z0,z745,z2,z32,z8,z5])],[(0,[z0,z1,z2,z8,z947,z6]),(0,[z0,z215,z2,z8,z11,z6]),(0,[z0,z1,z2,z948,z5,z6])],[(0,[z0,z949,z2,z8,z5,z6]),(0,[z0,z950,z1,z2,z8,z5]),(0,[z0,z18,z1,z2,z200,z5])],[(0,[z0,z785,z2,z8,z5,z6]),(0,[z698,z1,z2,z8,z138,z6]),(0,[z0,z1,z2,z8,z6,z951]),(0,[z0,z1,z8,z715,z69,z6]),(0,[z0,z91,z1,z2,z32,z5])],[(0,[z0,z1,z2,z8,z952,z6]),(0,[z0,z953,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z954,z6]),(0,[z0,z1,z90,z8,z5,z76]),(0,[z0,z1,z2,z8,z5,z955]),(0,[z0,z956,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z52,z5])],[(0,[z0,z590,z2,z19,z5,z6]),(0,[z0,z1,z2,z8,z709,z6]),(0,[z0,z1,z2,z957,z8,z5]),(0,[z0,z1,z2,z8,z5,z958])]],
   [[(1,[z0,z1,z8,z715,z6]),(0,[z57,z0,z18,z1,z2,z5]),(0,[z0,z1,z2,z8,z5,z959])],[(0,[z0,z23,z175,z8,z5,z6]),(0,[z0,z960,z1,z8,z5,z6]),(0,[z0,z1,z2,z961,z8,z5]),(0,[z0,z117,z2,z19,z5,z303])],[(0,[z0,z1,z2,z8,z5,z962]),(0,[z0,z1,z2,z8,z5,z303]),(0,[z0,z106,z2,z8,z722,z6])],[(0,[z0,z18,z1,z2,z5,z431]),(0,[z0,z282,z1,z144,z8,z5])],[(0,[z186,z1,z2,z4,z5,z271]),(0,[z0,z963,z1,z2,z8,z5]),(0,[z0,z1,z2,z964,z8,z5]),(0,[z0,z29,z1,z32,z30,z5])],[(0,[z0,z965,z1,z2,z5,z6]),(0,[z0,z1,z2,z8,z5,z13]),(0,[z0,z307,z2,z8,z5,z6]),(0,[z0,z18,z1,z2,z711,z5]),(0,[z0,z18,z1,z2,z502,z5]),(0,[z0,z2,z8,z5,z767,z239]),(0,[z0,z1,z2,z8,z306,z6])],[(0,[z0,z1,z2,z8,z966,z6]),(0,[z0,z1,z2,z967,z5,z6]),(0,[z0,z1,z2,z8,z968,z6]),(0,[z0,z1,z2,z8,z5,z969]),(0,[z0,z970,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z757]),(0,[z0,z18,z1,z2,z132,z5]),(0,[z0,z1,z801,z30,z5,z6])],[(0,[z20,z23,z2,z8,z5,z6]),(0,[z0,z1,z2,z971,z8,z5]),(0,[z0,z1,z2,z8,z5,z972]),(0,[z308,z0,z324,z2,z8,z5])]],
   [[(0,[z20,z23,z2,z8,z34,z6]),(0,[z0,z1,z2,z8,z973,z6])],[(0,[z0,z1,z2,z974,z8,z5]),(0,[z0,z1,z331,z2,z8,z213]),(0,[z0,z18,z1,z2,z8,z171]),(0,[z0,z1,z2,z133,z5,z191]),(0,[z0,z1,z2,z719,z53,z6]),(0,[z0,z18,z1,z2,z5,z451])],[(0,[z0,z18,z454,z2,z8,z5]),(0,[z0,z18,z2,z19,z133,z5]),(0,[z0,z975,z1,z2,z8,z5]),(0,[z0,z1,z976,z8,z5,z6]),(0,[z0,z18,z1,z2,z8,z899]),(0,[z0,z1,z2,z5,z816,z149]),(0,[z0,z1,z2,z32,z8,z977])],[(0,[z0,z1,z2,z21,z5,z311]),(0,[z0,z1,z2,z8,z5,z978]),(0,[z0,z1,z2,z979,z8,z5]),(0,[z0,z1,z2,z8,z5,z980]),(0,[z0,z18,z1,z2,z95,z5]),(0,[z0,z1,z2,z192,z52,z25])],[(0,[z0,z1,z2,z8,z5,z981]),(0,[z607,z1,z2,z4,z5,z6]),(0,[z0,z210,z211,z32,z8,z5]),(0,[z0,z1,z2,z8,z982,z6]),(0,[z0,z1,z2,z8,z5,z983]),(0,[z57,z0,z1,z73,z2,z5])],[(0,[z20,z18,z23,z2,z8,z5]),(0,[z0,z880,z1,z2,z27,z5]),(1,[z0,z2,z710,z5,z6]),(0,[z0,z10,z384,z8,z11,z6]),(0,[z0,z68,z1,z32,z8,z338]),(0,[z0,z18,z1,z2,z320,z5])],[(0,[z0,z1,z232,z8,z5,z6]),(0,[z22,z185,z2,z8,z5,z6]),(0,[z26,z1,z156,z8,z5,z392]),(0,[z0,z2,z8,z5,z984,z6]),(0,[z0,z1,z2,z985,z5,z6]),(0,[z0,z1,z2,z8,z5,z986]),(0,[z0,z18,z1,z2,z5,z300]),(0,[z0,z18,z1,z2,z487,z5])],[(0,[z0,z1,z232,z8,z34,z6]),(0,[z0,z1,z8,z987,z5,z6]),(0,[z0,z1,z2,z8,z988,z6]),(0,[z0,z307,z2,z8,z9,z6]),(0,[z989,z1,z2,z8,z5,z6]),(0,[z0,z68,z1,z8,z338,z6])]],
   [[(0,[z260,z1,z36,z8,z5,z6]),(0,[z0,z1,z83,z3,z5,z6]),(0,[z275,z1,z2,z97,z8,z5])],[(0,[z0,z1,z2,z990,z5,z6]),(0,[z0,z1,z2,z991,z5,z6]),(0,[z0,z1,z8,z992,z5,z6]),(0,[z0,z1,z627,z8,z11,z6]),(0,[z139,z0,z2,z288,z133,z6]),(0,[z0,z1,z144,z8,z5,z545]),(0,[z0,z18,z1,z2,z532,z5])],[(0,[z0,z993,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z994]),(0,[z0,z1,z2,z8,z5,z995]),(0,[z0,z1,z845,z8,z5,z6]),(0,[z0,z167,z2,z8,z5,z239]),(0,[z0,z29,z1,z82,z30,z5]),(0,[z0,z1,z90,z8,z5,z86])],[(0,[z0,z1,z2,z8,z5,z996]),(0,[z0,z1,z2,z8,z5,z997]),(0,[z0,z117,z2,z19,z5,z191])],[(0,[z0,z1,z2,z8,z5,z998]),(0,[z0,z1,z2,z8,z5,z999]),(0,[z0,z1,z2,z8,z245,z6]),(0,[z0,z1,z2,z8,z5,z191]),(0,[z0,z1,z400,z2,z32,z8]),(0,[z371,z0,z18,z1,z2,z5]),(0,[z0,z18,z1,z976,z8,z5])],[(0,[z0,z1,z2,z8,z5,z1000]),(0,[z0,z1,z2,z8,z1001,z6]),(0,[z0,z1,z2,z8,z5,z767]),(0,[z0,z1,z143,z8,z715,z6]),(0,[z0,z1,z317,z2,z8,z545])],[(0,[z0,z1,z2,z8,z5,z1002]),(0,[z0,z1003,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z1004]),(0,[z0,z1,z627,z8,z338,z6]),(0,[z0,z18,z1,z2,z635,z5]),(0,[z0,z1,z2,z32,z405,z5]),(0,[z0,z18,z465,z1,z2,z5])],[(0,[z0,z18,z1,z2,z44,z5]),(0,[z0,z1,z2,z8,z1005,z6]),(0,[z0,z1,z378,z8,z5,z86]),(0,[z0,z18,z1,z2,z114,z5]),(0,[z888,z18,z1,z2,z8,z5]),(0,[z0,z282,z1,z2,z8,z159])]],
   [[(0,[z20,z879,z2,z8,z5,z6]),(0,[z0,z1,z8,z338,z78,z6]),(0,[z120,z1,z2,z8,z233,z121]),(0,[z0,z1,z262,z8,z5,z6]),(0,[z0,z18,z1,z2,z656,z5]),(0,[z0,z1,z2,z1006,z5,z6]),(0,[z0,z1,z2,z192,z52,z6])],[(0,[z20,z23,z2,z8,z319,z6]),(0,[z0,z1,z2,z8,z1007,z5]),(0,[z0,z1008,z1,z2,z8,z5]),(0,[z120,z1,z2,z8,z492,z121])],[(0,[z0,z1,z765,z8,z5,z6])],[(0,[z20,z23,z232,z8,z5,z6]),(0,[z185,z879,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z1009,z6]),(0,[z0,z1,z803,z8,z5,z6]),(0,[z0,z91,z1,z30,z5,z6]),(0,[z0,z18,z1,z143,z8,z69]),(0,[z57,z0,z1,z2,z32,z53]),(0,[z0,z1,z2,z8,z1010,z6])],[(0,[z0,z1,z2,z8,z5,z1011]),(0,[z0,z1,z1012,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z1013]),(0,[z189,z1,z2,z8,z138,z6]),(0,[z0,z10,z2,z32,z8,z11]),(0,[z57,z0,z18,z1,z2,z545]),(0,[z0,z1,z2,z8,z5,z1014])],[(0,[z0,z1,z2,z8,z5,z1015]),(0,[z0,z1,z2,z8,z245,z125]),(0,[z182,z1,z2,z32,z8,z138]),(0,[z0,z1,z110,z8,z5,z713]),(0,[z0,z1,z2,z8,z719,z6])],[(0,[z0,z1,z2,z1016,z5,z6]),(0,[z79,z37,z1,z2,z38,z5])],[(0,[z0,z165,z211,z8,z5,z6]),(0,[z0,z2,z8,z1017,z5,z6]),(0,[z0,z29,z1,z30,z5,z6])]],
   [[(0,[z0,z1,z2,z1018,z8,z5]),(0,[z0,z1,z8,z5,z1019,z6]),(0,[z186,z1,z2,z4,z161,z6]),(0,[z0,z18,z49,z100,z8,z5]),(0,[z0,z1,z2,z8,z5,z1020]),(0,[z0,z18,z1,z1021,z8,z5]),(0,[z88,z0,z1,z2,z8,z545])],[(0,[z0,z1,z2,z8,z78,z6])],[(0,[z26,z454,z156,z8,z5,z6]),(0,[z0,z1,z1022,z2,z8,z6]),(0,[z0,z1,z2,z8,z5,z1023]),(0,[z0,z1,z2,z192,z719,z6])],[(0,[z22,z18,z185,z2,z8,z5]),(0,[z0,z49,z100,z32,z8,z5]),(0,[z0,z1024,z2,z8,z5,z6]),(0,[z0,z1,z2,z52,z6,z335]),(0,[z0,z283,z2,z414,z8,z5])],[(0,[z26,z1,z156,z8,z5,z6]),(0,[z0,z1025,z2,z8,z5,z6]),(0,[z0,z1026,z1,z2,z8,z5]),(0,[z0,z465,z1,z2,z5,z86])],[(0,[z0,z454,z2,z8,z5,z392]),(0,[z0,z1,z2,z1027,z8,z5]),(0,[z1,z2,z4,z725,z5,z6]),(0,[z0,z668,z2,z8,z5,z239]),(0,[z0,z617,z2,z8,z332,z6]),(0,[z0,z1,z1028,z2,z8,z6])],[(0,[z0,z1,z2,z8,z319,z311]),(0,[z0,z18,z1,z2,z80,z5]),(0,[z0,z1,z2,z32,z200,z5])],[(0,[z0,z1,z2,z8,z5,z1029]),(0,[z0,z953,z1,z2,z54,z5]),(0,[z0,z37,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z94,z724])]],
   [[(0,[z0,z1,z2,z8,z5,z1030]),(0,[z0,z1,z2,z8,z5,z1031]),(0,[z0,z1,z2,z8,z194,z94]),(0,[z468,z601,z1,z2,z8,z5])],[(0,[z0,z1,z1032,z8,z5,z6]),(0,[z0,z1,z700,z8,z5,z85]),(0,[z0,z1,z2,z1033,z8,z5])],[(0,[z0,z430,z8,z338,z5,z6]),(0,[z1,z2,z725,z38,z5,z6]),(0,[z0,z1,z627,z8,z332,z6]),(0,[z0,z1,z2,z8,z411,z6]),(0,[z0,z749,z2,z8,z5,z6]),(0,[z0,z1,z90,z8,z5,z6]),(0,[z0,z1,z400,z2,z8,z6])],[(0,[z0,z1,z2,z8,z1034,z6]),(0,[z22,z879,z2,z8,z5,z6]),(0,[z0,z550,z100,z8,z5,z6]),(0,[z0,z1,z2,z8,z1035,z6])],[(0,[z0,z18,z1,z2,z389,z5]),(0,[z0,z890,z2,z8,z5,z6]),(1,[z0,z1,z2,z5,z816])],[(0,[z0,z18,z1,z2,z27,z5]),(0,[z0,z1036,z2,z8,z5,z6]),(0,[z0,z1037,z1,z2,z8,z5]),(0,[z0,z314,z1,z2,z32,z5]),(0,[z0,z18,z1,z2,z5,z542])],[(0,[z0,z465,z1,z2,z5,z121]),(0,[z0,z1,z90,z8,z5,z85])],[(0,[z0,z1038,z2,z8,z5,z6]),(0,[z120,z123,z1,z2,z8,z5]),(0,[z0,z1,z2,z8,z5,z1039]),(0,[z0,z1,z2,z8,z5,z1040]),(0,[z0,z1,z2,z8,z159,z94])]],
   [[(0,[z0,z2,z710,z133,z5,z6]),(0,[z0,z18,z1,z144,z19,z5]),(0,[z0,z1,z2,z32,z132,z5]),(0,[z109,z0,z1,z75,z8,z5]),(0,[z0,z1,z83,z801,z5,z6])],[(0,[z443,z1,z2,z8,z9,z6]),(0,[z0,z1,z2,z32,z5,z584])],[(0,[z0,z1,z295,z8,z5,z86]),(0,[z0,z1,z2,z8,z5,z1041])],[(0,[z0,z430,z2,z8,z5,z6]),(0,[z0,z1,z2,z8,z1042,z6]),(1,[z0,z749,z8,z5,z6]),(0,[z0,z1043,z1,z2,z8,z5])],[(0,[z20,z23,z175,z8,z5,z6]),(0,[z7,z1,z8,z267,z9,z6]),(0,[z0,z1,z2,z8,z5,z173]),(0,[z57,z0,z1,z2,z719,z6])],[(0,[z0,z1044,z1,z2,z8,z5]),(0,[z7,z1,z2,z8,z709,z6]),(0,[z57,z0,z1,z2,z585,z6]),(0,[z0,z1,z2,z8,z1045,z6]),(0,[z0,z1,z1046,z8,z5,z6]),(0,[z47,z0,z1,z144,z8,z5]),(0,[z0,z1047,z1,z2,z8,z5]),(0,[z0,z465,z1,z317,z2,z213])],[(0,[z0,z1,z2,z32,z74,z5]),(0,[z0,z1,z1048,z8,z5,z6]),(0,[z0,z1,z2,z1049,z5,z6]),(0,[z0,z18,z1,z2,z8,z233]),(0,[z0,z1,z2,z1050,z5,z6]),(0,[z0,z1,z2,z8,z6,z1051]),(0,[z0,z1,z2,z32,z318,z5])],[(0,[z247,z1,z156,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z8,z5,z1052]),(0,[z0,z1,z2,z8,z5,z1053]),(0,[z182,z1,z2,z8,z138,z6]),(0,[z0,z1,z8,z5,z1054,z6]),(0,[z0,z1,z2,z8,z5,z1055]),(0,[z0,z1,z2,z8,z5,z1056])],[(0,[z0,z1,z2,z1057,z5,z6])],[(0,[z0,z454,z2,z8,z5,z459]),(0,[z7,z1,z2,z8,z9,z6]),(0,[z1058,z0,z1,z2,z8,z6]),(0,[z0,z1,z2,z8,z5,z1059]),(0,[z0,z10,z307,z2,z8,z6]),(0,[z0,z18,z1,z812,z8,z5])],[(0,[z0,z1,z2,z455,z8,z5]),(0,[z0,z18,z1,z2,z5,z706]),(0,[z0,z18,z1,z2,z5,z434]),(0,[z0,z465,z1,z2,z93,z5])],[(0,[z0,z106,z2,z8,z332,z6])],[(0,[z0,z1060,z1,z2,z8,z6]),(0,[z0,z1,z2,z8,z93,z606]),(0,[z0,z1,z2,z1061,z8,z5])],[(0,[z0,z1,z2,z32,z8,z306])],[(0,[z0,z1,z2,z8,z1062,z6]),(0,[z57,z0,z307,z2,z53,z6]),(0,[z57,z0,z18,z1,z2,z159]),(0,[z0,z1,z317,z2,z8,z724]),(0,[z0,z1,z2,z8,z93,z724])]],
   [[(0,[z0,z1,z2,z32,z8,z319]),(0,[z0,z1,z2,z8,z484,z392]),(0,[z0,z1,z2,z8,z5,z874]),(0,[z0,z1,z1063,z2,z8,z5]),(0,[z0,z18,z1,z2,z370,z5]),(0,[z0,z465,z1,z2,z5,z85]),(0,[z0,z1,z2,z32,z192,z52])],[(0,[z0,z1,z2,z8,z5,z1064]),(0,[z0,z1,z153,z2,z8,z288]),(0,[z0,z18,z1,z144,z5,z149])],[(0,[z182,z1,z2,z8,z709,z6]),(0,[z242,z1,z2,z8,z138,z6]),(0,[z275,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z1065,z5,z6]),(0,[z0,z1,z2,z1066,z5,z6]),(0,[z0,z1,z2,z8,z5,z1067]),(0,[z139,z0,z18,z2,z133,z5])],[(0,[z0,z1,z2,z74,z5,z147]),(0,[z0,z1,z2,z8,z1068,z6]),(0,[z0,z1,z2,z8,z161,z125])],[(0,[z0,z1,z2,z8,z5,z1069]),(0,[z0,z18,z1,z2,z8,z492]),(0,[z0,z1070,z1,z2,z5,z6]),(0,[z57,z0,z18,z307,z2,z5]),(0,[z0,z566,z310,z2,z8,z5]),(0,[z0,z1,z144,z32,z8,z5])],[(0,[z0,z2,z8,z825,z5,z6]),(0,[z0,z1,z384,z32,z8,z5]),(0,[z0,z1,z1071,z8,z5,z6]),(0,[z0,z1,z2,z8,z1072,z6])],[(0,[z0,z1,z2,z1073,z5,z6]),(0,[z0,z1,z2,z8,z1074,z6]),(0,[z559,z1,z2,z38,z5,z6]),(0,[z0,z465,z1,z2,z9,z6]),(0,[z0,z261,z1,z2,z32,z8]),(0,[z0,z1,z2,z8,z1075,z6]),(0,[z0,z1,z2,z200,z5,z239])],[(0,[z0,z1,z2,z32,z21,z5]),(0,[z0,z1076,z1,z2,z8,z5]),(0,[z0,z1,z2,z1077,z5,z6]),(0,[z0,z18,z922,z2,z8,z5])]],
   [[(0,[z0,z18,z1,z2,z19,z5]),(0,[z0,z1,z262,z8,z5,z914]),(0,[z0,z1,z2,z8,z5,z1078]),(0,[z0,z1,z2,z32,z5,z440]),(0,[z109,z0,z1,z144,z8,z5])],[(0,[z0,z1,z2,z5,z6,z1079]),(0,[z1080,z0,z1,z2,z8,z5]),(0,[z0,z18,z1,z144,z133,z5]),(0,[z0,z10,z262,z8,z11,z6]),(0,[z0,z1,z2,z8,z5,z1081]),(0,[z57,z0,z18,z433,z2,z5])],[(0,[z0,z1,z2,z8,z1082,z6]),(0,[z0,z1,z2,z8,z5,z1083]),(0,[z0,z465,z1,z2,z5,z98]),(0,[z0,z1,z1084,z2,z8,z5]),(0,[z0,z1,z143,z8,z69,z6])],[(0,[z26,z1,z156,z8,z78,z6]),(0,[z0,z1,z627,z8,z5,z6]),(0,[z0,z1,z2,z8,z1085,z6]),(0,[z0,z1,z2,z455,z132,z5]),(0,[z0,z1,z75,z2,z8,z306]),(0,[z0,z1,z1086,z2,z8,z5])],[(0,[z0,z1,z2,z1087,z8,z5]),(0,[z0,z1,z2,z1088,z5,z6]),(0,[z0,z1,z2,z82,z8,z306])],[(0,[z0,z1,z2,z1089,z74,z5]),(0,[z0,z1,z2,z8,z5,z1090]),(0,[z0,z18,z1,z2,z8,z78]),(0,[z0,z197,z1,z30,z5,z6]),(0,[z0,z1,z2,z8,z1091,z6]),(0,[z0,z1,z478,z2,z8,z213])],[(0,[z0,z1,z2,z8,z78,z392]),(0,[z0,z1,z1092,z2,z8,z6]),(0,[z39,z1,z2,z410,z8,z5]),(0,[z0,z18,z861,z2,z8,z5])],[(0,[z0,z166,z1,z8,z338,z6]),(0,[z0,z49,z749,z8,z5,z6]),(0,[z0,z2,z8,z5,z767,z6]),(0,[z0,z29,z1,z306,z30,z6])]],
   [[(0,[z0,z1,z2,z1093,z5,z6]),(0,[z0,z1,z2,z8,z5,z1094]),(0,[z0,z1,z2,z8,z1095,z6]),(0,[z0,z1,z1096,z2,z8,z5]),(0,[z0,z1,z2,z8,z762,z6]),(0,[z0,z1,z2,z32,z450,z5]),(0,[z0,z1,z317,z2,z8,z213])],[(0,[z516,z1,z2,z8,z9,z6]),(0,[z0,z261,z1,z2,z184,z6]),(0,[z0,z18,z1,z2,z136,z5]),(0,[z0,z1,z2,z8,z5,z248]),(0,[z0,z1,z2,z192,z52,z434])],[(0,[z0,z1,z2,z1097,z8,z5]),(0,[z0,z1,z2,z1098,z8,z5]),(0,[z0,z18,z1,z2,z446,z5]),(0,[z0,z167,z1,z144,z8,z5]),(0,[z0,z18,z1,z400,z2,z8]),(0,[z0,z1,z2,z32,z8,z1010])],[(0,[z0,z1,z2,z8,z233,z6]),(0,[z0,z1,z2,z1099,z8,z5]),(0,[z0,z18,z1,z90,z8,z5]),(0,[z0,z18,z1,z2,z5,z629])],[(0,[z0,z1,z2,z8,z492,z6])],[(0,[z0,z1,z1100,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z1101]),(0,[z419,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z8,z1102,z6])],[(0,[z0,z1,z2,z8,z484,z6]),(0,[z0,z261,z1,z2,z455,z8]),(0,[z0,z18,z1,z307,z2,z5]),(0,[z0,z920,z2,z8,z5,z6])],[(0,[z0,z1,z2,z8,z5,z311]),(0,[z0,z18,z430,z2,z8,z5]),(0,[z0,z2,z8,z1103,z5,z6]),(0,[z0,z1,z8,z5,z6,z1104]),(0,[z0,z1,z2,z8,z1105,z6]),(0,[z0,z1,z2,z8,z5,z1106]),(0,[z0,z167,z324,z2,z8,z5]),(0,[z0,z1107,z2,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z8,z34,z311]),(0,[z0,z1,z2,z32,z5,z206]),(0,[z0,z18,z1,z2,z8,z288]),(0,[z0,z18,z261,z1,z2,z6]),(0,[z57,z0,z1,z262,z8,z6]),(0,[z0,z1,z75,z144,z8,z5]),(0,[z1108,z18,z1,z2,z8,z5])],[(0,[z0,z433,z2,z32,z8,z5]),(0,[z0,z18,z1,z2,z5,z149])],[(0,[z0,z1,z2,z8,z1109,z6]),(0,[z0,z1,z2,z54,z5,z392]),(0,[z79,z1,z2,z32,z38,z5]),(0,[z468,z1,z2,z8,z5,z98])],[(0,[z0,z357,z2,z8,z332,z6]),(0,[z0,z1,z2,z8,z5,z1110]),(0,[z0,z1,z2,z8,z1111,z6]),(0,[z0,z1,z2,z8,z5,z1112]),(0,[z0,z1,z2,z8,z6,z1113]),(0,[z0,z18,z1,z90,z52,z5])],[(0,[z0,z1,z1114,z8,z5,z6]),(0,[z0,z1,z2,z8,z1115,z6]),(0,[z1108,z1,z2,z8,z5,z6]),(0,[z0,z261,z1,z2,z8,z6]),(0,[z0,z1,z2,z8,z722,z6])],[(0,[z0,z1,z2,z1116,z5,z6]),(0,[z26,z430,z156,z8,z5,z6]),(0,[z0,z1117,z2,z8,z5,z6]),(0,[z0,z1118,z2,z8,z5,z6]),(0,[z0,z1,z115,z2,z8,z213]),(0,[z0,z1,z2,z8,z5,z1119]),(0,[z0,z18,z1,z2,z414,z5]),(0,[z0,z18,z307,z2,z8,z5])],[(0,[z0,z1,z1120,z8,z5,z6]),(0,[z0,z1,z2,z1121,z5,z6]),(0,[z1,z2,z8,z709,z5,z6]),(0,[z0,z1,z1122,z8,z5,z6]),(0,[z0,z10,z2,z8,z687,z6]),(0,[z0,z1,z2,z8,z5,z1123]),(0,[z0,z1,z2,z8,z5,z1124]),(0,[z0,z18,z1,z2,z5,z649])],[(0,[z0,z1,z2,z8,z5,z1125]),(0,[z0,z1,z2,z8,z1126,z6]),(1,[z1,z2,z725,z5,z6]),(0,[z0,z1,z2,z8,z1127,z6]),(0,[z0,z1,z2,z8,z6,z1128]),(0,[z0,z1,z2,z8,z5,z1129])]],
   [[(0,[z0,z1,z2,z8,z5,z1130]),(0,[z0,z430,z2,z8,z5,z392]),(0,[z0,z1131,z2,z8,z5,z6]),(0,[z364,z0,z2,z133,z5,z6]),(0,[z0,z18,z1,z8,z267,z5]),(0,[z0,z1,z2,z32,z8,z233]),(0,[z0,z1,z2,z8,z1132,z6]),(0,[z0,z2,z8,z5,z218,z767])],[(0,[z0,z18,z1,z2,z8,z34]),(0,[z0,z1,z2,z8,z5,z271]),(0,[z0,z1,z2,z8,z5,z1133]),(0,[z0,z1,z2,z8,z233,z98]),(0,[z0,z18,z1,z2,z133,z5]),(0,[z0,z18,z1,z2,z5,z659]),(0,[z0,z1,z2,z5,z184,z816])],[(0,[z0,z1,z1134,z8,z5,z6]),(0,[z0,z454,z2,z8,z78,z6]),(0,[z0,z1,z2,z8,z1135,z6]),(0,[z0,z18,z1,z2,z54,z5]),(0,[z26,z18,z1,z156,z8,z5]),(0,[z0,z1,z2,z192,z502,z6])],[(0,[z0,z1,z2,z32,z8,z5]),(0,[z0,z1,z2,z8,z5,z1136]),(0,[z0,z1,z1137,z8,z5,z6]),(0,[z0,z1,z2,z8,z5,z1138]),(0,[z0,z1,z2,z8,z78,z459]),(0,[z186,z1,z2,z4,z5,z125]),(0,[z0,z1,z723,z8,z5,z6]),(0,[z0,z1,z2,z8,z977,z6])],[(0,[z0,z1,z1139,z8,z5,z6]),(0,[z20,z23,z2,z8,z5,z311])],[(0,[z0,z1140,z1,z2,z8,z6]),(0,[z0,z1141,z1,z2,z5,z6]),(0,[z0,z1142,z2,z8,z5,z6]),(0,[z0,z1,z83,z3,z32,z5]),(0,[z0,z1,z2,z8,z1143,z6])],[(1,[z879,z2,z8,z5,z6]),(0,[z26,z1,z156,z8,z5,z459]),(0,[z0,z1,z1144,z8,z5,z6]),(0,[z139,z0,z261,z2,z133,z6]),(0,[z0,z867,z2,z8,z5,z6])],[(0,[z0,z18,z1,z2,z455,z5]),(0,[z0,z18,z1,z945,z8,z5])]],
   [[(0,[z0,z1,z2,z1145,z5,z6]),(0,[z0,z1,z2,z8,z5,z1146]),(0,[z0,z1,z2,z8,z1147,z5])],[(0,[z0,z1,z1148,z8,z5,z6]),(0,[z35,z1,z36,z8,z5,z6]),(0,[z0,z1,z2,z1149,z5,z6]),(0,[z0,z1,z2,z32,z437,z5]),(0,[z0,z1,z2,z8,z5,z1150]),(0,[z0,z307,z143,z2,z8,z6]),(0,[z0,z18,z307,z2,z5,z6]),(0,[z0,z1,z2,z5,z649,z434])],[],[(0,[z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z232,z8,z5,z311]),(0,[z0,z1,z2,z5,z6,z1151]),(0,[z0,z1,z2,z192,z487,z6])],[(0,[z0,z1,z2,z21,z34,z6]),(0,[z0,z1,z2,z8,z5,z1152]),(0,[z0,z1,z2,z8,z5,z1153]),(0,[z0,z1,z2,z27,z5,z6]),(0,[z0,z1,z2,z8,z5,z1154]),(0,[z646,z0,z18,z1,z2,z5])],[(0,[z0,z18,z1,z2,z8,z245]),(0,[z0,z1,z2,z8,z1155,z6]),(0,[z419,z1,z2,z8,z9,z6]),(0,[z0,z1,z2,z8,z5,z178]),(0,[z0,z18,z1,z760,z8,z5])],[(0,[z0,z1,z2,z32,z8,z492]),(0,[z141,z1,z2,z8,z5,z121]),(0,[z0,z1,z2,z8,z5,z1156]),(0,[z0,z1,z1157,z2,z8,z6]),(0,[z0,z1158,z1,z2,z5,z6]),(0,[z0,z307,z2,z32,z8,z5])],[(0,[z0,z1,z2,z710,z5,z6])]],
   [[(0,[z0,z1,z1159,z8,z5,z6]),(0,[z20,z23,z2,z32,z8,z5]),(0,[z0,z1,z2,z54,z5,z6]),(0,[z0,z1,z75,z2,z8,z5]),(0,[z0,z1,z83,z450,z5,z6]),(0,[z0,z1,z143,z421,z8,z6])],[(0,[z0,z1,z2,z8,z1160,z6]),(0,[z0,z1,z2,z1161,z8,z5]),(0,[z0,z1,z2,z1162,z8,z5]),(0,[z0,z1,z262,z192,z8,z6]),(0,[z0,z310,z2,z8,z5,z218]),(0,[z0,z1,z2,z82,z8,z5])],[(0,[z0,z1,z2,z8,z5,z1163]),(0,[z0,z1,z2,z8,z5,z1164]),(0,[z186,z18,z1,z2,z4,z5]),(0,[z0,z1,z2,z8,z5,z1165]),(0,[z0,z29,z1,z801,z5,z6]),(0,[z0,z1,z2,z8,z5,z815])],[(0,[z0,z1,z2,z1166,z5,z6]),(0,[z0,z1167,z1,z2,z8,z5])],[(0,[z0,z1,z2,z74,z5,z6]),(0,[z0,z18,z210,z211,z8,z5]),(0,[z0,z1,z400,z2,z82,z8]),(0,[z0,z1,z2,z8,z5,z1168]),(0,[z0,z1,z2,z8,z5,z816])],[(0,[z0,z1,z2,z74,z34,z6]),(0,[z0,z18,z1,z2,z388,z5]),(0,[z0,z430,z2,z8,z5,z459]),(0,[z0,z106,z307,z2,z8,z6]),(0,[z0,z18,z1,z2,z287,z5]),(0,[z0,z18,z1,z2,z33,z5])],[(0,[z0,z1,z2,z8,z1169,z6]),(0,[z0,z1,z2,z32,z8,z171]),(0,[z0,z18,z1,z2,z41,z5]),(0,[z163,z0,z1,z8,z391,z5])],[(0,[z0,z1,z232,z32,z8,z5]),(0,[z0,z1,z2,z1170,z5,z6]),(0,[z0,z1,z2,z8,z5,z1171]),(0,[z22,z185,z2,z32,z8,z5]),(0,[z0,z1,z2,z979,z54,z5]),(0,[z0,z1,z1021,z8,z5,z6]),(0,[z0,z261,z1,z153,z2,z8]),(0,[z0,z1,z110,z144,z8,z5])]],
   [[(0,[z0,z1,z2,z1172,z5,z6]),(0,[z0,z1,z2,z8,z5,z1173]),(0,[z265,z1,z2,z38,z5,z6]),(0,[z0,z18,z324,z2,z19,z5]),(0,[z0,z1174,z1,z2,z8,z5]),(0,[z0,z1,z143,z8,z14,z6]),(0,[z0,z1,z2,z200,z5,z86]),(0,[z0,z18,z1,z885,z8,z5])],[(0,[z0,z579,z100,z8,z5,z6]),(0,[z0,z37,z1,z2,z19,z5]),(0,[z0,z18,z1,z2,z358,z5]),(0,[z0,z18,z1,z2,z591,z5]),(0,[z0,z1,z2,z8,z5,z1175]),(0,[z0,z1,z262,z8,z5,z1112])],[(0,[z0,z1,z1176,z8,z5,z6]),(0,[z0,z1,z2,z1089,z8,z5]),(0,[z0,z1,z2,z1177,z8,z5]),(0,[z0,z1,z2,z8,z1178,z6])],[(0,[z0,z1,z2,z1179,z5,z6]),(0,[z0,z18,z1,z2,z288,z133]),(0,[z0,z855,z2,z8,z5,z6]),(0,[z0,z601,z1,z144,z8,z5])],[(0,[z0,z1,z2,z1180,z5,z6])],[(0,[z0,z1,z2,z21,z319,z6]),(0,[z0,z1,z2,z21,z5,z147]),(0,[z0,z18,z1,z2,z237,z5]),(0,[z0,z1,z2,z8,z161,z6]),(0,[z139,z0,z153,z2,z133,z5]),(0,[z47,z0,z2,z200,z5,z218]),(0,[z0,z1,z400,z75,z2,z8])],[(0,[z0,z1,z836,z8,z5,z6]),(0,[z57,z0,z1,z627,z8,z6]),(0,[z0,z1,z2,z8,z5,z1181]),(0,[z0,z1,z2,z5,z719,z6])],[(0,[z57,z0,z433,z2,z53,z6]),(0,[z0,z18,z1,z2,z146,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1055).take 171) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1226)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 527, 171] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 100).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 201).take 55).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [100, 101, 55] = true :=
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

end PEqualNP.Outside.L_meta_40311

theorem PEqualNP.Outside.L_meta_40311 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4272597152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4272597152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40311.solve