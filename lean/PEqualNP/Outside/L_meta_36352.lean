import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36352

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8010000028044154#64 ++ 0x200400000a011055#64 ++ 0x7bec5208f84cc3ff#64 ++ 0xdefb14823e1330ff#64 : BitVec 256),
   (0x0820043360953330#64 ++ 0x4208010cd8254ccc#64 ++ 0xf7d8ac7761b73333#64 ++ 0xbdf62b1dd86dcccc#64 : BitVec 256),
   (0x204130858238142a#64 ++ 0x88104c21608e050a#64 ++ 0xeebf318786383c3f#64 ++ 0x7bafcc61e18e0f0f#64 : BitVec 256),
   (0x1282c15805c02a81#64 ++ 0x04a0b05601700aa0#64 ++ 0xde7fc1f807c03fc2#64 ++ 0xf79ff07e01f00ff0#64 : BitVec 256),
   (0x2303fa00076a8002#64 ++ 0x08c0fe8001daa000#64 ++ 0xc1fbfe0007ffc001#64 ++ 0xf07eff8001fff000#64 : BitVec 256),
   (0x3c03ffeed0000000#64 ++ 0x0f00fffbb4000000#64 ++ 0x3ffbfffff8000000#64 ++ 0x0ffefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [9, 8]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0020001020852310 0x40080004082148c4 0x0000000001870300 0x800000000061c0c0

def z1 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8ac7761b73333 0xbdf62b1dd86dcccc

def z2 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fc1f807c03fc2 0xf79ff07e01f00ff0

def z3 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf318786383c3f 0x7bafcc61e18e0f0f

def z4 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z5 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z6 : W := mkw 0x8010000028044154 0x200400000a011055 0x7bec5208f84cc3ff 0xdefb14823e1330ff

def z7 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcfe7ff9fff3ff 0xffff3f9ffe7ffcff

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f8fe0001ffc001 0xf07e3f80007ff000

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0x4a2c000000000002 0x528b000000000000

def z10 : W := mkw 0x0820042360151130 0x42080108d805444c 0xe1d8ac0761b70031 0xb8762b01d86dc00c

def z11 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0x00002c0000330000 0x00000b00000cc000

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a0400008000003e 0x0a8100002000000f

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ac0001b70001 0xb0762b00006dc000

def z14 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdfffedf807f73fc3 0xf7fffb7e01fdcff0

def z15 : W := mkw 0x0040008580101428 0x801000216004050a 0x2e04018780003c3e 0x0b810061e0000f0f

def z16 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1040c07801c003c0 0x8410301e007000f0

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x5bec5208004cc3c3 0xd6fb1482001330f0

def z18 : W := mkw 0x0000000000000000 0x0000000000000000 0x41e85200004cc001 0xd07a148000133000

def z19 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8013ac0007b30000 0x2004eb0001ecc000

def z20 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x002352000648c000 0x4008d48001923000

def z21 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8033fe0007fbc000 0x600cff8001fef000

def z22 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0x1e0401f800003fc2 0x0781007e00000ff0

def z23 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x208030078038003d 0x08200c01e00e000f

def z24 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0x01803e00003fc001 0x00600f80000ff000

def z25 : W := mkw 0xa313fa002f6ec156 0x28c4fe800bdbb055 0xfbfffe08ffffc3ff 0xfeffff823ffff0ff

def z26 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x1e7bc1f800000000 0x079ef07e00000000

def z27 : W := mkw 0x3e83fffed5c02a81 0x0fa0ffffb5700aa0 0xffffffffffc03fc2 0xfffffffffff00ff0

def z28 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffbffffffffc001 0xfffefffffffff000

def z29 : W := mkw 0xbc13ffeef8044154 0x2f04fffbbe011055 0x7ffffffff84cc3ff 0xdffffffffe1330ff

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z31 : W := mkw 0x2001300102381022 0x08004c00408e0408 0xe6bb300706383033 0x79aecc01c18e0c0c

def z32 : W := mkw 0x0040008580101428 0x801000216004050a 0xee9c218780303c3f 0x3ba70861e00c0f0f

def z33 : W := mkw 0x8010000028044154 0x200400000a011055 0x31c05208f84cc3fd 0x8c7014823e1330ff

def z34 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0xc004000007c03fc2 0xf001000001f00ff0

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x5a6c4008004003c2 0xd69b1002001000f0

def z36 : W := mkw 0x8010000028044154 0x200400000a011055 0x21801200f80cc03d 0x086004803e03300f

def z37 : W := mkw 0x004000010238142a 0x80100000408e050a 0xc004000006383c3f 0x70010000018e0f0f

def z38 : W := mkw 0x3c43ffefd238142a 0x8f10fffbf48e050a 0xfffffffffe383c3f 0x7fffffffff8e0f0f

def z39 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc000000007ffc001 0xf000000001fff000

def z40 : W := mkw 0x2c03fea6d0000000 0x0b00ffa9b4000000 0x21fbfe07f8000000 0x087eff81fe000000

def z41 : W := mkw 0x20013a0000000000 0x08004e8000000000 0x01803e0000000000 0x00600f8000000000

def z42 : W := mkw 0x8010000028044154 0x200400000a011055 0x61841200f84cc3ff 0xd86104803e1330ff

def z43 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x0140ce0001c7c000 0x805033800071f000

def z44 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x8413218706303c00 0x2104c861c18c0f00

def z45 : W := mkw 0x8010000028044154 0x200400000a011055 0x114042087844c3c0 0x845010821e1130f0

def z46 : W := mkw 0x0282c01005c02a81 0x00a0b00401700aa0 0xc07fc00007c03fc2 0xf01ff00001f00ff0

def z47 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e0001fff8000000 0x0f80007ffe000000

def z48 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x000042000040c000 0x0000108000103000

def z49 : W := mkw 0x0040008580101428 0x801000216004050a 0xee3f018786003c3e 0x7b8fc061e1800f0f

def z50 : W := mkw 0x1aa2c57b65d53bb1 0x46a8b15ed9754eec 0xf7dbadf767b73f33 0xbdf6eb7dd9edcfcc

def z51 : W := mkw 0x0820043260852310 0x4208010c982148c4 0x73c88c7061870333 0x9cf2231c1861c0cc

def z52 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xc4bb318706383c01 0x712ecc61c18e0f00

def z53 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfff8fe7ff9b73333 0xbffe3f9ffe6dcccc

def z54 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x41fbfe00004cc001 0xd07eff8000133000

def z55 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x8410ac7701b33000 0x21042b1dc06ccc00

def z56 : W := mkw 0x0000000020040110 0x0000000008010044 0x7be85208f8040333 0x9efa14823e0100cc

def z57 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0x41e87e00007fc001 0xd07a1f80001ff000

def z58 : W := mkw 0x0020001120953330 0x4008000448254ccc 0xc000000001b73333 0xb0000000006dcccc

def z59 : W := mkw 0x3403fbcc90000000 0x0d00fef324000000 0x0823538898000000 0x0208d4e226000000

def z60 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xc417218706383c3f 0x7105c861c18e0f0f

def z61 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x28a7318786380c3d 0x4a29cc61e18e030f

def z62 : W := mkw 0x1aa2c57a65c52b91 0x46a8b15e99714ae4 0x1140cc7861c703c0 0x8450331e1871c0f0

def z63 : W := mkw 0x0820043260852310 0x4208010c982148c4 0x11408c7061870300 0x8450231c1861c0c0

def z64 : W := mkw 0x8010000008004044 0x2004000002001011 0x082452089848c0cc 0x4209148226123033

def z65 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x3f803ffff8000000 0x0fe00ffffe000000

def z66 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a000008f8000000 0x0e8000023e000000

def z67 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0xde7fc1f807ccffff 0xf79ff07e01f33fff

def z68 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0xd65c807007c03fc2 0xf597201c01f00ff0

def z69 : W := mkw 0x32c3f1dd87f83eab 0x8cb0fc7761fe0faa 0x8413a1f707b03c00 0x2104e87dc1ec0f00

def z70 : W := mkw 0x2103fa00022a8002 0x0840fe80008aa000 0x01fbfe00003fc001 0x007eff80000ff000

def z71 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x3ffbd3f8f8000000 0x0ffef4fe3e000000

def z72 : W := mkw 0x1aa2c57b65d53bb1 0x46a8b15ed9754eec 0xffffedff67f73ff3 0xfffffb7fd9fdcffc

def z73 : W := mkw 0x3ae3f5ffe7fd3fbb 0xceb8fd7ff9ff4fee 0xfffffdffe7ff3fff 0xffffff7ff9ffcfff

def z74 : W := mkw 0x0820042360151130 0x42080108d805444c 0x21802c0760370031 0x08600b01d80dc00c

def z75 : W := mkw 0x0000000100101020 0x0000000040040408 0x8410200700303000 0x21040801c00c0c00

def z76 : W := mkw 0x3c63fffff2bd373a 0xcf18fffffcaf4dce 0xffffffffffbf3f3f 0xffffffffffefcfcf

def z77 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x3600007760003332 0x0d80001dd8000ccc

def z78 : W := mkw 0x2b23fe3367ffb332 0x4ac8ff8cd9ffeccc 0xf7fbfe7767fff333 0xfdfeff9dd9fffccc

def z79 : W := mkw 0x3c03ffeef0040110 0x0f00fffbbc010044 0x7ffbfffff8040333 0x9ffefffffe0100cc

def z80 : W := mkw 0x2b23fe3347fbb222 0x4ac8ff8cd1feec88 0xc5fbfe7707fff001 0xf17eff9dc1fffc00

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0x014042000044c000 0x8050108000113000

def z82 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xc410ac7701b73333 0xb1042b1dc06dcccc

def z83 : W := mkw 0x204130848228040a 0x88104c21208a0102 0x0827118086080c0c 0x4209c46021820303

def z84 : W := mkw 0x3c43ffeed228040a 0x8f10fffbb48a0102 0x3ffffffffe080c0c 0x4fffffffff820303

def z85 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0xc004000001fff3ff 0xf0010000007ffcff

def z86 : W := mkw 0x2343fa85877a942a 0x88d0fea161dea50a 0xefffff8787fffc3f 0xfbffffe1e1ffff0f

def z87 : W := mkw 0x32c3f1dc87e82e8b 0x8cb0fc7721fa0ba2 0xde7fd1f887c83fce 0xf79ff47e21f20ff3

def z88 : W := mkw 0x3f43ffefd77a942a 0x8fd0fffbf5dea50a 0xfffffffffffffc3f 0xffffffffffffff0f

def z89 : W := mkw 0x3e83ffeed5400881 0x0fa0fffbb5500220 0x3ffffffffe400cc0 0x4fffffffff900330

def z90 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd044c07807c03fc2 0xf411301e01f00ff0

def z91 : W := mkw 0x2001308480000000 0x08004c2120000000 0x2ebb318780000000 0x0baecc61e0000000

def z92 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x1140ce7878000000 0x0450339e1e000000

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0xce3f018006003c02 0x738fc06001800f00

def z94 : W := mkw 0x32c3f1dd87f83eab 0x8cb0fc7761fe0faa 0xfefff1ff87f83fff 0xffbffc7fe1fe0fff

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a68400800000000 0x069a100200000000

def z96 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x841381f007803c00 0x2104e07c01e00f00

def z97 : W := mkw 0x0040000100101428 0x801000004004050a 0x0004000000003c3e 0x0001000000000f0f

def z98 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x0413adf700000000 0x0104eb7dc0000000

def z99 : W := mkw 0x8010000028044154 0x200400000a011055 0x40040000004cc3ff 0xd0010000001330ff

def z100 : W := mkw 0x0000001000802200 0x0000000400200880 0x1600007000003302 0x0580001c00000cc0

def z101 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0xffffd3f8ffccffff 0xfffff4fe3ff33fff

def z102 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0xffff738ffe7cffff 0xffffdce3ff9f3fff

def z103 : W := mkw 0x1c00056a50000000 0x0700015a94000000 0x1000007878000000 0x0400001e1e000000

def z104 : W := mkw 0x3c03ff6a50000000 0x0f00ffda94000000 0x11fbfe7878000000 0x047eff9e1e000000

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x082410008008000c 0x4209040020020003

def z106 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x0400007700003000 0x0100001dc0000c00

def z107 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x31c0fe7ff8000000 0x0c703f9ffe000000

def z108 : W := mkw 0x0820042360151130 0x42080108d805444c 0xe7982c0760373033 0x39e60b01d80dcc0c

def z109 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x21803e07f8000000 0x08600f81fe000000

def z110 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0xde3f01f806003fc2 0x778fc07e01800ff0

def z111 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb610ac7761b33332 0x2d842b1dd86ccccc

def z112 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdfffd3f807ccffc3 0xf7fff4fe01f33ff0

def z113 : W := mkw 0x0000000100101020 0x0000000040040408 0x2600000700003032 0x09800001c0000c0c

def z114 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xa493318786383c3d 0x2924cc61e18e0f0f

def z115 : W := mkw 0x3f03ffeed5428000 0x0fc0fffbb550a000 0x3ffbfffff9c7c000 0x8ffefffffe71f000

def z116 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffbfffff9b70001 0xbffefffffe6dc000

def z117 : W := mkw 0x3c23ffffd0913220 0x4f08fffff4244c88 0x8413adf701b33000 0x2104eb7dc06ccc00

def z118 : W := mkw 0xbc13ffeed8004044 0x2f04fffbb6001011 0x3ffffffff848c0cc 0x4ffffffffe123033

def z119 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0x0000000001c003c0 0x80000000007000f0

def z120 : W := mkw 0x004000010238142a 0x80100000408e050a 0xce3f018006383c3f 0x738fc060018e0f0f

def z121 : W := mkw 0x0820043260852310 0x4208010c982148c4 0x37d8ac7761870300 0x8df62b1dd861c0c0

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x6aac10008008003f 0x5aab04002002000f

def z123 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8153ee0007f7c000 0xa054fb8001fdf000

def z124 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0x21803207f83cc03d 0x08600c81fe0f300f

def z125 : W := mkw 0x286134b7e2bd373a 0xca184d2df8af4dce 0xffffbdf7e7bf3f3f 0xffffef7df9efcfcf

def z126 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe084300786383c3f 0x78210c01e18e0f0f

def z127 : W := mkw 0x1382cb5805c2aa81 0x04e0b2d60170aaa0 0xdf7fcff807c7ffc2 0xf7dff3fe01f1fff0

def z128 : W := mkw 0x2b23fe23677f9132 0x4ac8ff88d9dfe44c 0xe1fbfe0767ffc031 0xf87eff81d9fff00c

def z129 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0xc1d8be0001bfc001 0xb0762f80006ff000

def z130 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xe698ac7701b33033 0x39a62b1dc06ccc0c

def z131 : W := mkw 0x3283fb5805c02a81 0x0ca0fed601700aa0 0xdffffff807c03fc2 0xf7fffffe01f00ff0

def z132 : W := mkw 0x2041308580101428 0x88104c216004050a 0x2ebf318780003c3e 0x0bafcc61e0000f0f

def z133 : W := mkw 0x3383fb5807eaaa83 0x0ce0fed601faaaa0 0xde7fedf807f33fc2 0xf79ffb7e01fccff0

def z134 : W := mkw 0x0800042240000000 0x0200010890000000 0x37d8ac7760000000 0x0df62b1dd8000000

def z135 : W := mkw 0x20413085a23c153a 0x88104c21688f054e 0xffff3187e63c3f3f 0xffffcc61f98f0fcf

def z136 : W := mkw 0x0a22c43365d53330 0x4288b10cd9754ccc 0xf7fbec7767f73333 0xfdfefb1dd9fdcccc

def z137 : W := mkw 0x0000001000802200 0x0000000400200880 0xd658807001803302 0xb596201c00600cc0

def z138 : W := mkw 0x0000000020040110 0x0000000008010044 0x4000000000040333 0x90000000000100cc

def z139 : W := mkw 0x30c131dd82b83eab 0x8c304c7760ae0faa 0xfebf31ff86383fff 0x7fafcc7fe18e0fff

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x3be85208f8000000 0x0efa14823e000000

def z141 : W := mkw 0x2203fa0005400000 0x0880fe8001500000 0xc1fbfe0007c00000 0xf07eff8001f00000

def z142 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7f8fe7761fff333 0xfdfe3f9dd87ffccc

def z143 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0x0827418806400cc0 0x4209d06201900330

def z144 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x2e27118786083c3e 0x4b89c461e1820f0f

def z145 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc07bc00007c00000 0xf01ef00001f00000

def z146 : W := mkw 0x3383fb5807eaaa83 0x0ce0fed601faaaa0 0xdffffff807ffffc3 0xf7fffffe01fffff0

def z147 : W := mkw 0x0020001120953330 0x4008000448254ccc 0xd658807001b73333 0xb596201c006dcccc

def z148 : W := mkw 0x1c4005efd0101428 0x8710017bf404050a 0x3e0401fff8003c3e 0x0f81007ffe000f0f

def z149 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1553efff78000000 0x0554fbffde000000

def z150 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0x082353889e48c000 0x4208d4e227923000

def z151 : W := mkw 0x2001300002280002 0x08004c00008a0000 0xc0bb300006380001 0x702ecc00018e0000

def z152 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x0000200700300000 0x00000801c00c0000

def z153 : W := mkw 0x12c2c15907f83eab 0x84b0b05641fe0faa 0xde7fc1f807f83fff 0xf79ff07e01fe0fff

def z154 : W := mkw 0x1280015805c02a81 0x04a0005601700aa0 0xde0401f807c03fc2 0xf781007e01f00ff0

def z155 : W := mkw 0x3043f1cd8238142a 0x8c10fc73608e050a 0xfefff1ff86383c3f 0x7fbffc7fe18e0f0f

def z156 : W := mkw 0x0040008580101428 0x801000216004050a 0x6eac118780083c3f 0x5bab0461e0020f0f

def z157 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x3e04007ff80033fe 0x0f81001ffe000cff

def z158 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x41eb5200064cc001 0xd07ad48001933000

def z159 : W := mkw 0x3e83fffed5c02a81 0x0fa0ffffb5700aa0 0x3ffbfffff9c003c0 0x8ffefffffe7000f0

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0xeebf118086083c3f 0x7bafc46021820f0f

def z161 : W := mkw 0x0000000020040110 0x0000000008010044 0x73c8000060040333 0x9cf20000180100cc

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x7be85208f84cc001 0xdefa14823e133000

def z163 : W := mkw 0x8010000028044154 0x200400000a011055 0x3be85208f80cc03d 0x0efa14823e03300f

def z164 : W := mkw 0x805000012a3c557e 0xa01400004a8f155f 0xc0040000067cffff 0xf0010000019f3fff

def z165 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf600007761b73333 0xbd80001dd86dcccc

def z166 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0xc9ffff8087ffcc0d 0xf27fffe021fff303

def z167 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xc41781f007c03fc2 0xf105e07c01f00ff0

def z168 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xfbfbfe08ffffc001 0xfefeff823ffff000

def z169 : W := mkw 0x12a2c15925d53bb1 0x44a8b05649754eec 0xde7fc1f807f73ff3 0xf79ff07e01fdcffc

def z170 : W := mkw 0x01000000022a8002 0x00400000008aa000 0x00000000003fc001 0x00000000000ff000

def z171 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xfeff718f86783fff 0xffbfdc63e19e0fff

def z172 : W := mkw 0xa313fa002f6ec156 0x28c4fe800bdbb055 0x7bef5208fe4cc3ff 0xdefbd4823f9330ff

def z173 : W := mkw 0x0202c00005400000 0x0080b00001500000 0x0023400006400000 0x4008d00001900000

def z174 : W := mkw 0x9012c14828044154 0x2404b0520a011055 0x7fffd3f8f84cc3ff 0xdffff4fe3e1330ff

def z175 : W := mkw 0xa313fa002f6ec156 0x28c4fe800bdbb055 0xd1fbfe087fffc3c1 0xf47eff821ffff0f0

def z176 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0xce3f418806403cc2 0x738fd06201900f30

def z177 : W := mkw 0xa1113a002a2ec156 0x28444e800a8bb055 0x7bec7e08f87fc3ff 0xdefb1f823e1ff0ff

def z178 : W := mkw 0x0800042240000000 0x0200010890000000 0xf7d8ac7761b70001 0xbdf62b1dd86dc000

def z179 : W := mkw 0x140001cc90000000 0x0500007324000000 0x0800018898000000 0x0200006226000000

def z180 : W := mkw 0x29213e23623f9132 0x4a484f88d88fe44c 0x21803e07603fc031 0x08600f81d80ff00c

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010ac0001b30000 0x20042b00006cc000

def z182 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf698207760303333 0x3da6081dd80c0ccc

def z183 : W := mkw 0x1000014800000000 0x0400005200000000 0x1e0001f800000000 0x0780007e00000000

def z184 : W := mkw 0x2001300002280002 0x08004c00008a0000 0xc1fbbc0007bf0001 0xf07eef0001efc000

def z185 : W := mkw 0x8010000028044154 0x200400000a011055 0x3a040008f80003fe 0x0e8100023e0000ff

def z186 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xffdcac7ff9b733ff 0xbff72b1ffe6dccff

def z187 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1e2741f806403fc2 0x4789d07e01900ff0

def z188 : W := mkw 0x004000858238142a 0x80100021608e050a 0xee04018786383c3f 0x7b810061e18e0f0f

def z189 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xda7fc00807c003c2 0xf69ff00201f000f0

def z190 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1dbac0007b70001 0xb076eb0001edc000

def z191 : W := mkw 0x2001300002280002 0x08004c00008a0000 0x0080300000380001 0x00200c00000e0000

def z192 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0xc9ffff8807ffccc1 0xf27fffe201fff330

def z193 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x9550ac7761b73300 0xa5542b1dd86dccc0

def z194 : W := mkw 0xb413fbcc98004044 0x2d04fef326001011 0x082753889848c0cc 0x4209d4e226123033

def z195 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9e1781f807803fc2 0x2785e07e01e00ff0

def z196 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc5d8ac7701b73001 0xb1762b1dc06dcc00

def z197 : W := mkw 0x0800042260040110 0x0200010898010044 0x77d8ac7760040333 0x9df62b1dd80100cc

def z198 : W := mkw 0x1f02cf6a55428000 0x07c0b3da9550a000 0x1140ce7879c7c000 0x8450339e1e71f000

def z199 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x040001f700000000 0x0100007dc0000000

def z200 : W := mkw 0x2323fa1127ffb332 0x48c8fe8449ffeccc 0xc1fbfe0007fff333 0xf07eff8001fffccc

def z201 : W := mkw 0x3403fbcc90000000 0x0d00fef324000000 0x3beb5388f8000000 0x0efad4e23e000000

def z202 : W := mkw 0x2043fa858238142a 0x8810fea1608e050a 0xefffff8786383c3f 0x7bffffe1e18e0f0f

def z203 : W := mkw 0x0000000100101020 0x0000000040040408 0xe698200700303033 0x39a60801c00c0c0c

def z204 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcec7f61f733f3 0xffff3b1fd87dccfc

def z205 : W := mkw 0x18a0057b60953bb1 0x4628015ed8254eec 0x3e0401ff60003ff2 0x0f81007fd8000ffc

def z206 : W := mkw 0xab33fe336ffff376 0x6accff8cdbfffcdd 0xfffffe7ffffff3ff 0xffffff9ffffffcff

def z207 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xd658ac7701b33302 0xb5962b1dc06cccc0

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000004cc001 0xd000000000133000

def z209 : W := mkw 0x8010000028044154 0x200400000a011055 0x73c81200f80cc33f 0x9cf204803e0330cf

def z210 : W := mkw 0x3c23fffff0953330 0x4f08fffffc254ccc 0xfffbfffff9b73333 0xbffefffffe6dcccc

def z211 : W := mkw 0x9292c1580dc06ac5 0x24a4b05603701ab1 0xde7fd3f89fc8ffce 0xf79ff4fe27f23ff3

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x7aec5008804803ff 0xdebb1402201200ff

def z213 : W := mkw 0xbe93fffefdc46bd5 0x2fa4ffffbf711af5 0xffffffffffccffff 0xfffffffffff33fff

def z214 : W := mkw 0x8010000008004044 0x2004000002001011 0x49ec5208984cc0cd 0xd27b148226133033

def z215 : W := mkw 0x0040008580101428 0x801000216004050a 0x200000078000003c 0x08000001e000000f

def z216 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcbc77e1bf333f 0xffff2f1df86fcccf

def z217 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8ee7f79f7f3f3 0xbdf63b9fde7dfcfc

def z218 : W := mkw 0x2803fe2240000000 0x0a00ff8890000000 0x37fbfe7760000000 0x0dfeff9dd8000000

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0xc03b000006000000 0x700ec00001800000

def z220 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x2e84318780383c3f 0x0ba10c61e00e0f0f

def z221 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1e7bedff00000000 0x079efb7fc0000000

def z222 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffbfffff84cc001 0xdffefffffe133000

def z223 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xe1802c0761b73333 0xb8600b01d86dcccc

def z224 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x00002c0700000000 0x00000b01c0000000

def z225 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xdbfffe0807ffc3c3 0xf6ffff8201fff0f0

def z226 : W := mkw 0x0820043260852310 0x4208010c982148c4 0xd7588c7061873302 0xb5d6231c1861ccc0

def z227 : W := mkw 0x0c000e2250000000 0x0300038894000000 0x01000e0078000000 0x004003801e000000

def z228 : W := mkw 0xa0113084a8044154 0x28044c212a011055 0x7fff738ff84cc3ff 0xdfffdce3fe1330ff

def z229 : W := mkw 0x2001308480000000 0x08004c2120000000 0x0413218700000000 0x0104c861c0000000

def z230 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x0013ac0000000000 0x0004eb0000000000

def z231 : W := mkw 0x0000000020040110 0x0000000008010044 0x73e85200604cc333 0xdcfa1480181330cc

def z232 : W := mkw 0x1aa2c57b45d13aa1 0x46a8b15ed1744ea8 0xde7fedff07f33fc2 0xf79ffb7fc1fccff0

def z233 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8be77f9bff33f 0xbdf62f9dfe6ffccf

def z234 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc1e8520007ffc001 0xf07a148001fff000

def z235 : W := mkw 0x8010000028044154 0x200400000a011055 0x73c842087844c3f3 0x9cf210821e1130fc

def z236 : W := mkw 0x8010000028044154 0x200400000a011055 0x3b841208f80cc3ff 0x0ee104823e0330ff

def z237 : W := mkw 0x1382c15807eaaa83 0x04e0b05601faaaa0 0xde7fc1f807ffffc3 0xf79ff07e01fffff0

def z238 : W := mkw 0x9ab2c57b6dd57bf5 0x66acb15edb755efd 0xffffffffffffffff 0xffffffffffffffff

def z239 : W := mkw 0x3403fbcc90000000 0x0d00fef324000000 0x1e7bd3f898000000 0x079ef4fe26000000

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0x4068400000400000 0xd01a100000100000

def z241 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x01fbfe0000000000 0x007eff8000000000

def z242 : W := mkw 0x8010000028044154 0x200400000a011055 0x51e85208784cc3c1 0xd47a14821e1330f0

def z243 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7dcac7761fff3ff 0xfdf72b1dd87ffcff

def z244 : W := mkw 0x004000000228040a 0x80100000008a0102 0x0004000006080c0c 0x4001000001820303

def z245 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x37dbadf760000000 0x0df6eb7dd8000000

def z246 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc07bec0007f30000 0xf01efb0001fcc000

def z247 : W := mkw 0x8010000028044154 0x200400000a011055 0x3be85208f844c3c0 0x8efa14823e1130f0

def z248 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc0bb72000678c001 0x702edc80019e3000

def z249 : W := mkw 0x2001308480000000 0x08004c2120000000 0x0823118080000000 0x0208c46020000000

def z250 : W := mkw 0x8010000028044154 0x200400000a011055 0xfbfcfe08f9ffc3ff 0xfeff3f823e7ff0ff

def z251 : W := mkw 0x1e82cf7a55c02a81 0x07a0b3de95700aa0 0xdf7fcff87fc03fc2 0xf7dff3fe1ff00ff0

def z252 : W := mkw 0x3403fbcc90000000 0x0d00fef324000000 0x2ebb738f98000000 0x0baedce3e6000000

def z253 : W := mkw 0x8830042368155174 0x620c0108da05545d 0x7bec7e0ff87fc3ff 0xdefb1f83fe1ff0ff

def z254 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3fd8adfff8000000 0x0ff62b7ffe000000

def z255 : W := mkw 0x0800042240000000 0x0200010890000000 0x3ff8fe7ff8000000 0x0ffe3f9ffe000000

def z256 : W := mkw 0xa353fa85af7ed57e 0xa8d4fea16bdfb55f 0xffffff8fffffffff 0xffffffe3ffffffff

def z257 : W := mkw 0x8212c0002d444154 0x2084b0000b511055 0xfbffd208ffccc3ff 0xfefff4823ff330ff

def z258 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3e13adfff8000000 0x0f84eb7ffe000000

def z259 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0x082753880648ccc0 0x4209d4e201923330

def z260 : W := mkw 0x0002c00000000000 0x0000b00000000000 0x007bc00000000000 0x001ef00000000000

def z261 : W := mkw 0x0820042360151130 0x42080108d805444c 0x73c82c0760370333 0x9cf20b01d80dc0cc

def z262 : W := mkw 0xbf13ffeeff6ec156 0x2fc4fffbbfdbb055 0xffffffffffffc3ff 0xfffffffffffff0ff

def z263 : W := mkw 0x33c3fbdd87fabeab 0x8cf0fef761feafaa 0xffffffff87ffffff 0xffffffffe1ffffff

def z264 : W := mkw 0x3c03ffefd0101020 0x0f00fffbf4040408 0xfffbfffff8303033 0x3ffefffffe0c0c0c

def z265 : W := mkw 0x0000001000802200 0x0000000400200880 0xd7d8ac7001b73303 0xb5f62b1c006dccc0

def z266 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffffffffe003c02 0x7fffffffff800f00

def z267 : W := mkw 0x3d03ffeed22a8002 0x0f40fffbb48aa000 0x3ffbfffff83fc001 0x0ffefffffe0ff000

def z268 : W := mkw 0x0300000005428000 0x00c000000150a000 0x0000000001c7c000 0x800000000071f000

def z269 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xae17218786303c3e 0x2b85c861e18c0f0f

def z270 : W := mkw 0x32c3f1cd87781cab 0x8cb0fc7361de072a 0xeebf718f86783cff 0x7bafdc63e19e0f3f

def z271 : W := mkw 0x8010000008004044 0x2004000002001011 0x000400000048c0cc 0x4001000000123033

def z272 : W := mkw 0x0000000100101020 0x0000000040040408 0xe7d8ac0701b73033 0xb9f62b01c06dcc0c

def z273 : W := mkw 0x805000012a3c557e 0xa01400004a8f155f 0xfbec5208fe7cffff 0xfefb14823f9f3fff

def z274 : W := mkw 0x282134b7e0953330 0x4a084d2df8254ccc 0xfffbbdf7e1b73333 0xbffeef7df86dcccc

def z275 : W := mkw 0x2343fa01077a942a 0x88d0fe8041dea50a 0xc1fffe0007fffc3f 0xf07fff8001ffff0f

def z276 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0xfebf318ffe383fff 0x7fafcc63ff8e0fff

def z277 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0xfbec5208f9fff3ff 0xfefb14823e7ffcff

def z278 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf658807761803332 0xbd96201dd8600ccc

def z279 : W := mkw 0x9090015828846bd5 0x242400560a211af5 0x3e0401f8f8003ffe 0x0f81007e3e000fff

def z280 : W := mkw 0x2c413ea7d238142a 0x8b104fa9f48e050a 0x21803e07f838003d 0x08600f81fe0e000f

def z281 : W := mkw 0x286134b7e2bd373a 0xca184d2df8af4dce 0xf7dbadf767b73f33 0xbdf6eb7dd9edcfcc

def z282 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xce3f81f007803c02 0x738fe07c01e00f00

def z283 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc0bbbc0007bb0001 0x702eef0001eec000

def z284 : W := mkw 0x8010000028044154 0x200400000a011055 0x00040000000003fe 0x00010000000000ff

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000001b70001 0xb0000000006dc000

def z286 : W := mkw 0x0000008480000000 0x0000002120000000 0x2e00018780000000 0x0b800061e0000000

def z287 : W := mkw 0x8010000028044154 0x200400000a011055 0x10000008780003c0 0x040000021e0000f0

def z288 : W := mkw 0x204130848228040a 0x88104c21208a0102 0xce3f118086083c0e 0x738fc46021820f03

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e04018000003c02 0x0381006000000f00

def z290 : W := mkw 0x0380001007eaaa83 0x00e0000401faaaa0 0xc004000007ffffc3 0xf001000001fffff0

def z291 : W := mkw 0x3383fb5807eaaa83 0x0ce0fed601faaaa0 0xc5fbfff007fffc01 0xf17efffc01ffff00

def z292 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffffffff808003f 0x5ffffffffe02000f

def z293 : W := mkw 0x3f23fffff7ffb332 0x4fc8fffffdffeccc 0xfffbfffffffff333 0xfffefffffffffccc

def z294 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0xeebf3187867cffff 0xfbafcc61e19f3fff

def z295 : W := mkw 0x3003f1cc80000000 0x0c00fc7320000000 0x3efbf1ff80000000 0x0fbefc7fe0000000

def z296 : W := mkw 0xb2d3f1ddaffc7fff 0xacb4fc776bff1fff 0xfffff3fffffcffff 0xfffffcffffff3fff

def z297 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc1fbd20007ccc001 0xf07ef48001f33000

def z298 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xebfffe0087ffc03f 0xfaffff8021fff00f

def z299 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x81fbfe0007b30000 0x207eff8001ecc000

def z300 : W := mkw 0x1802c56a40000000 0x0600b15a90000000 0x3ffbedff60000000 0x0ffefb7fd8000000

def z301 : W := mkw 0x1aa2c57a65c52b91 0x46a8b15e99714ae4 0xdf7fcdf867c73fc2 0xf7dff37e19f1cff0

def z302 : W := mkw 0x3c0135eed0000000 0x0f004d7bb4000000 0x3ebb31fff8000000 0x0faecc7ffe000000

def z303 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0xc140ce0007ffc001 0xf050338001fff000

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0xc098200000300001 0x30260800000c0000

def z305 : W := mkw 0x3443fbcd9238142a 0x8d10fef3648e050a 0xeebf738f9e383c3f 0x7bafdce3e78e0f0f

def z306 : W := mkw 0x2f03fea6d76a8002 0x0bc0ffa9b5daa000 0xe1fbfe07ffffc001 0xf87eff81fffff000

def z307 : W := mkw 0x2001300000000000 0x08004c0000000000 0x00bb300000000000 0x002ecc0000000000

def z308 : W := mkw 0x0000001020842310 0x00000004082108c4 0xf7d8807061843333 0xbdf6201c18610ccc

def z309 : W := mkw 0x0000000100101020 0x0000000040040408 0xeebf218706303c33 0x7bafc861c18c0f0c

def z310 : W := mkw 0x1c22cf7b70953330 0x4708b3dedc254ccc 0xf7d8ee7f79b73333 0xbdf63b9fde6dcccc

def z311 : W := mkw 0x3383fb5807eaaa83 0x0ce0fed601faaaa0 0xd1fbfe7807ffc3c1 0xf47eff9e01fff0f0

def z312 : W := mkw 0x2001300002280002 0x08004c00008a0000 0x0023100006080000 0x4008c40001820000

def z313 : W := mkw 0x0200000005400000 0x0080000001500000 0xc000000007c00000 0xf000000001f00000

def z314 : W := mkw 0x3683fbcc95400881 0x0da0fef325500220 0x082753889e400cc0 0x4209d4e227900330

def z315 : W := mkw 0x004000010238142a 0x80100000408e050a 0x8000000006303c00 0x20000000018c0f00

def z316 : W := mkw 0x9c1005eef8044154 0x2704017bbe011055 0x7fec53fff84cc3ff 0xdffb14fffe1330ff

def z317 : W := mkw 0x0000001000802200 0x0000000400200880 0xde7cc07801c033c2 0xf79f301e00700cf0

def z318 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x31c0ac7761b70331 0x8c702b1dd86dc0cc

def z319 : W := mkw 0x3c43ffefd238142a 0x8f10fffbf48e050a 0x8413adf706303c00 0x2104eb7dc18c0f00

def z320 : W := mkw 0x0b20043367ffb332 0x42c8010cd9ffeccc 0xf7d8ac7767fff333 0xfdf62b1dd9fffccc

def z321 : W := mkw 0x1c2005fff0953330 0x4708017ffc254ccc 0xffd8adfff9b73333 0xbff62b7ffe6dcccc

def z322 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xbffbffffffb30000 0x2ffeffffffecc000

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x6288000000000033 0x18a200000000000c

def z324 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefffbd8787bf3c3f 0xfbffef61e1efcf0f

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a040008000003c2 0x06810002000000f0

def z326 : W := mkw 0x3403fbcc90000000 0x0d00fef324000000 0x0003018000000000 0x0000c06000000000

def z327 : W := mkw 0x2001308482280002 0x08004c21208a0000 0xeebb318786380001 0x7baecc61e18e0000

def z328 : W := mkw 0x1e82c5fed5c02a81 0x07a0b17fb5700aa0 0xfe7fc1ffffc03fc2 0xff9ff07ffff00ff0

def z329 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xffff738ffe383c3f 0x7fffdce3ff8e0f0f

def z330 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0x01fbfe0001c7c000 0x807eff800071f000

def z331 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x8c37c1f807c03cc0 0x630df07e01f00f30

def z332 : W := mkw 0x204130848228040a 0x88104c21208a0102 0x6aaf118086080c3f 0x5aabc4602182030f

def z333 : W := mkw 0x0000001100903220 0x0000000440240c88 0xf6d8a07701b03333 0xbdb6281dc06c0ccc

def z334 : W := mkw 0x0000000020040110 0x0000000008010044 0x7bec4008604403f3 0xdefb1002181100fc

def z335 : W := mkw 0x3c83fffed0802a81 0x0f20ffffb4200aa0 0x3ffffffff8003fc2 0x0ffffffffe000ff0

def z336 : W := mkw 0x8010000028044154 0x200400000a011055 0x5a6c4008004cc3ff 0xd69b1002001330ff

def z337 : W := mkw 0x2b23fe3347fbb222 0x4ac8ff8cd1feec88 0x8413ac7707b33000 0x2104eb1dc1eccc00

def z338 : W := mkw 0x1c22cf7a70852310 0x4708b3de9c2148c4 0x1140ce7879870300 0x8450339e1e61c0c0

def z339 : W := mkw 0x004000010238142a 0x80100000408e050a 0x000000000038003d 0x00000000000e000f

def z340 : W := mkw 0x2243f0858778142a 0x8890fc2161de050a 0xeefff18787f83c3f 0xfbbffc61e1fe0f0f

def z341 : W := mkw 0x3f83fffed7eaaa83 0x0fe0ffffb5faaaa0 0xffffffffffffffc3 0xfffffffffffffff0

def z342 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xa590ac7761b73031 0x29642b1dd86dcc0c

def z343 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc17bce0007c7c000 0xf05ef38001f1f000

def z344 : W := mkw 0x0202c00005400000 0x0080b00001500000 0x8013800007800000 0x2004e00001e00000

def z345 : W := mkw 0x2d013ea6d22a8002 0x0b404fa9b48aa000 0x21803e07f83fc001 0x08600f81fe0ff000

def z346 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0xc1bb3e00063fc001 0x706ecf80018ff000

def z347 : W := mkw 0x280134a6c0000000 0x0a004d29b0000000 0x3ffbbdf7e0000000 0x0ffeef7df8000000

def z348 : W := mkw 0x0000001000802200 0x0000000400200880 0xc000000001803302 0xb000000000600cc0

def z349 : W := mkw 0x8010000028044154 0x200400000a011055 0x7bcc0008f80403ff 0x9ef300023e0100ff

def z350 : W := mkw 0x20613095a2bd373a 0xc8184c2568af4dce 0xeebf318787bf3f3f 0xfbafcc61e1efcfcf

def z351 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffffadf767b73f33 0xffffeb7dd9edcfcc

def z352 : W := mkw 0x8010000028044154 0x200400000a011055 0x3bec5208f80003fe 0x0efb14823e0000ff

def z353 : W := mkw 0x2041309582b8362a 0x88104c2560ae0d8a 0xfeffb1f787b83f3f 0xffbfec7de1ee0fcf

def z354 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0xfffbffffffc00000 0xfffefffffff00000

def z355 : W := mkw 0x2c413ea7d238142a 0x8b104fa9f48e050a 0xefbf3f87fe383c3f 0x7befcfe1ff8e0f0f

def z356 : W := mkw 0x1202c14805400000 0x0480b05201500000 0xde7bc1f807c00000 0xf79ef07e01f00000

def z357 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0xfe7fc1f8ffc03ffe 0xff9ff07e3ff00fff

def z358 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9e7bc1f807803c00 0x279ef07e01e00f00

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x2698200700000000 0x09a60801c0000000

def z360 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xffffd3f8ffc03fc2 0xfffff4fe3ff00ff0

def z361 : W := mkw 0x8010000028044154 0x200400000a011055 0x3a245208f848c3fe 0x4e8914823e1230ff

def z362 : W := mkw 0x0320001127ffb332 0x40c8000449ffeccc 0xc000000007fff333 0xf000000001fffccc

def z363 : W := mkw 0x831000002f6ec156 0x20c400000bdbb055 0xfbec5208ffffc3ff 0xfefb14823ffff0ff

def z364 : W := mkw 0x3e83fffed5c02a81 0x0fa0ffffb5700aa0 0xde7fedff07c03fc2 0xf79ffb7fc1f00ff0

def z365 : W := mkw 0x0800042240000000 0x0200010890000000 0x0410ac7700000000 0x01042b1dc0000000

def z366 : W := mkw 0x0202c00005400000 0x0080b00001500000 0x0040c00001c00000 0x8010300000700000

def z367 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xfeffd1f887c83fff 0xffbff47e21f20fff

def z368 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xcfffff8007fffc03 0xf3ffffe001ffff00

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x208010008008003d 0x082004002002000f

def z370 : W := mkw 0x0c0004a6d0000000 0x03000129b4000000 0x20000007f8000000 0x08000001fe000000

def z371 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8193be0007bfc001 0x2064ef8001eff000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x40a8100000080001 0x502a040000020000

def z373 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc07bd20007c8c000 0xf01ef48001f23000

def z374 : W := mkw 0x9c12cf6a78044154 0x2704b3da9e011055 0x7becde78f84cc3ff 0xdefb379e3e1330ff

def z375 : W := mkw 0x086004b7e0953738 0xc218012df8254dce 0x3e0401f7e0003f3e 0x0f81007df8000fcf

def z376 : W := mkw 0x0040008480000408 0x8010002120000102 0x0804018080000c0c 0x0201006020000303

def z377 : W := mkw 0x286134b7e2bd373a 0xca184d2df8af4dce 0xfebf31f7e6383f3f 0x7fafcc7df98e0fcf

def z378 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x01c0fe0001ffc001 0x80703f80007ff000

def z379 : W := mkw 0x1c02c5eed0000000 0x0700b17bb4000000 0x3e7bc1fff8000000 0x0f9ef07ffe000000

def z380 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9453c1f807c03fc0 0xa514f07e01f00ff0

def z381 : W := mkw 0x9c12cf6a78044154 0x2704b3da9e011055 0x1140ce787844c3c0 0x8450339e1e1130f0

def z382 : W := mkw 0x9c1005eef8044154 0x2704017bbe011055 0x3e0401fff80003fe 0x0f81007ffe0000ff

def z383 : W := mkw 0x1282c15825c42b91 0x04a0b05609710ae4 0xffffc1f867c43ff3 0xfffff07e19f10ffc

def z384 : W := mkw 0x286134b7c2b9362a 0xca184d2df0ae4d8a 0xeebfbdf787bb3c3f 0x7bafef7de1eecf0f

def z385 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xd1408c7061b73333 0xb450231c186dcccc

def z386 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xb7d8ac7761b33000 0x2df62b1dd86ccc00

def z387 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0x000000000648c000 0x4000000001923000

def z388 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x0003000006000000 0x0000c00001800000

def z389 : W := mkw 0x0820043240812200 0x4208010c90204880 0x00008c7001830000 0x0000231c0060c000

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x7bec5208f84003c2 0xdefb14823e1000f0

def z391 : W := mkw 0x12c2c1dd85d03ea9 0x84b0b07761740faa 0xfe7fc1ff87c03ffe 0xff9ff07fe1f00fff

def z392 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0x5e6c41f800403fc2 0xd79b107e00100ff0

def z393 : W := mkw 0x8830043268856354 0x620c010c9a2158d5 0x7becde78f9cfc3ff 0xdefb379e3e73f0ff

def z394 : W := mkw 0x3403fbcc90000000 0x0d00fef324000000 0x09fbff8898000000 0x027effe226000000

def z395 : W := mkw 0x284134a7c238142a 0x8a104d29f08e050a 0xffffbdf7e6383c3f 0x7fffef7df98e0f0f

def z396 : W := mkw 0x8830043268856354 0x620c010c9a2158d5 0x1140ce7879c7c3c0 0x8450339e1e71f0f0

def z397 : W := mkw 0x0000000002280002 0x00000000008a0000 0xc000000006380001 0x70000000018e0000

def z398 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1e7bc1f801c003c0 0x879ef07e007000f0

def z399 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x37d8ee7f78000000 0x0df63b9fde000000

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x33c8000060000000 0x0cf2000018000000

def z401 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0x8000000007803c00 0x2000000001e00f00

def z402 : W := mkw 0x829000102dc46bd5 0x20a400040b711af5 0xc004000007ccffff 0xf001000001f33fff

def z403 : W := mkw 0xa05130848a28444e 0xa8144c21228a1113 0x082753889e48cccc 0x4209d4e227923333

def z404 : W := mkw 0x8010000028044154 0x200400000a011055 0x7a040008f84cc3ff 0xde8100023e1330ff

def z405 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x8413adf707b30000 0x2104eb7dc1ecc000

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0xc058800001800000 0xb016200000600000

def z407 : W := mkw 0x0000001000802200 0x0000000400200880 0xde7f81f007803f02 0xf79fe07c01e00fc0

def z408 : W := mkw 0x0800043240802200 0x0200010c90200880 0xf7d8ac7761803302 0xbdf62b1dd8600cc0

def z409 : W := mkw 0x0800042240000000 0x0200010890000000 0x11408c7060000000 0x0450231c18000000

def z410 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefff7387867cfc3f 0xfbffdce1e19f3f0f

def z411 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x37d8be77f8000000 0x0df62f9dfe000000

def z412 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xdffbfff807ffc001 0xf7fefffe01fff000

def z413 : W := mkw 0xa313fa002f6ec156 0x28c4fe800bdbb055 0xe1fbfe00ffffc03d 0xf87eff803ffff00f

def z414 : W := mkw 0x0060001122bd373a 0xc018000448af4dce 0xc004000007bf3f3f 0xf001000001efcfcf

def z415 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0x1e7fc1f806400cc0 0x479ff07e01900330

def z416 : W := mkw 0x8010000028044154 0x200400000a011055 0xffff5388fe4cffff 0xffffd4e23f933fff

def z417 : W := mkw 0x03400001077a942a 0x80d0000041dea50a 0xc004000007fffc3f 0xf001000001ffff0f

def z418 : W := mkw 0x8010000028044154 0x200400000a011055 0x6aac1000804cc3ff 0xdaab0400201330ff

def z419 : W := mkw 0x8010000028044154 0x200400000a011055 0x00000000000cc03d 0x000000000003300f

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x1140420878000000 0x045010821e000000

def z421 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc013ac0007ffc001 0xf004eb0001fff000

def z422 : W := mkw 0x2c213ea7f0151130 0x4b084fa9fc05444c 0x21803e07f8370031 0x08600f81fe0dc00c

def z423 : W := mkw 0x10c001dd80903ea9 0x8430007760240faa 0x3e0401ff80003ffe 0x0f81007fe0000fff

def z424 : W := mkw 0xac113ea6f8044154 0x2b044fa9be011055 0x7bec7e0ff84cc3ff 0xdefb1f83fe1330ff

def z425 : W := mkw 0x0040008580101428 0x801000216004050a 0x0400018700003c00 0x01000061c0000f00

def z426 : W := mkw 0x3c23fffff0953330 0x4f08fffffc254ccc 0xf7dbadf761b73333 0xbdf6eb7dd86dcccc

def z427 : W := mkw 0x2b03fe22476a8002 0x0ac0ff8891daa000 0xf7fbfe7767ffc001 0xfdfeff9dd9fff000

def z428 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc1d8ac0007ffc001 0xf0762b0001fff000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x8413018006003c00 0x2104c06001800f00

def z430 : W := mkw 0x24013a8490000000 0x09004ea124000000 0x0000120098000000 0x0000048026000000

def z431 : W := mkw 0x2001308480000000 0x08004c2120000000 0x2080300780000000 0x08200c01e0000000

def z432 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x01a37e00067fc001 0x4068df80019ff000

def z433 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3e2353fff8000000 0x0f88d4fffe000000

def z434 : W := mkw 0x9090015828846bd5 0x242400560a211af5 0x7fec53f8f84cffff 0xdffb14fe3e133fff

def z435 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1d8ee0001f7c001 0xb0763b80007df000

def z436 : W := mkw 0x21413a85823a942a 0x88504ea1608ea50a 0xefbf3f87863ffc3f 0x7befcfe1e18fff0f

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x01801200000cc001 0x0060048000033000

def z438 : W := mkw 0x3c43ffefd0101428 0x8f10fffbf404050a 0x3ffffffff8003c3e 0x0ffffffffe000f0f

def z439 : W := mkw 0x204130848228040a 0x88104c21208a0102 0x2ebf318786080c0c 0x4bafcc61e1820303

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x40040000004003c2 0xd0010000001000f0

def z441 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0xc9fbff889fffc001 0xf27effe227fff000

def z442 : W := mkw 0x2001300002280002 0x08004c00008a0000 0x8013200006300000 0x2004c800018c0000

def z443 : W := mkw 0x3c23fffef0852310 0x4f08ffffbc2148c4 0x3ffbfffff9870300 0x8ffefffffe61c0c0

def z444 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x1040c07800000000 0x0410301e00000000

def z445 : W := mkw 0x3e83fffed5c02a81 0x0fa0ffffb5700aa0 0x8413adf707803c00 0x2104eb7dc1e00f00

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x2aa8100080000000 0x0aaa040020000000

def z447 : W := mkw 0x29213e3362bfb332 0x4a484f8cd8afeccc 0xf7d8be7761bff333 0xbdf62f9dd86ffccc

def z448 : W := mkw 0x32c3f1dd87f83eab 0x8cb0fc7761fe0faa 0xde7fe1ff07f03fc2 0xf79ff87fc1fc0ff0

def z449 : W := mkw 0x0020001120953330 0x4008000448254ccc 0xc1d8ac0001b73333 0xb0762b00006dcccc

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0xc618000000003002 0x3186000000000c00

def z451 : W := mkw 0x9292c1480d4048c5 0x24a4b05203501231 0x082753889e48cccc 0x4209d4e227923333

def z452 : W := mkw 0x1c2005fff0953330 0x4708017ffc254ccc 0x3e0001fff8003332 0x0f80007ffe000ccc

def z453 : W := mkw 0x0b22ce3365d7b330 0x42c8b38cd975eccc 0xf7d8ee7761f7f333 0xbdf63b9dd87dfccc

def z454 : W := mkw 0x3c23ffeff0151130 0x4f08fffbfc05444c 0x3ffbfffff8370031 0x0ffefffffe0dc00c

def z455 : W := mkw 0x02a0001125d53bb1 0x40a8000449754eec 0xc004000007f73ff3 0xf001000001fdcffc

def z456 : W := mkw 0x1402cb4810000000 0x0500b2d204000000 0x0000420818000000 0x0000108206000000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x0820520898000000 0x0208148226000000

def z458 : W := mkw 0x2003fa0002280002 0x0800fe80008a0000 0xc1fbfe0006380001 0x707eff80018e0000

def z459 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0xce3f018007c03fc2 0xf38fc06001f00ff0

def z460 : W := mkw 0x32c3f1dd87f83eab 0x8cb0fc7761fe0faa 0xeebfb1f787b83c3f 0x7bafec7de1ee0f0f

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e8520000000000 0x007a148000000000

def z462 : W := mkw 0x0820043260852310 0x4208010c982148c4 0x1000007060000300 0x0400001c180000c0

def z463 : W := mkw 0x02c0001107f83eab 0x80b0000441fe0faa 0xc004000007f83fff 0xf001000001fe0fff

def z464 : W := mkw 0x23413085877a942a 0x88d04c2161dea50a 0xeebf318787fffc3f 0xfbafcc61e1ffff0f

def z465 : W := mkw 0x0000000020040110 0x0000000008010044 0x3200000060000332 0x0c800000180000cc

def z466 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0x8000000007b30000 0x2000000001ecc000

def z467 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xeffbff8787ffc001 0xfbfeffe1e1fff000

def z468 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x1f7bcff878000000 0x07def3fe1e000000

def z469 : W := mkw 0xbc13ffeef8044154 0x2f04fffbbe011055 0x3ffbfffff80cc03d 0x0ffefffffe03300f

def z470 : W := mkw 0x2343fa85877a942a 0x88d0fea161dea50a 0xeebf73878678fc3f 0x7bafdce1e19e3f0f

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x10404008004003c0 0x84101002001000f0

def z472 : W := mkw 0x0000000120141130 0x000000004805044c 0xf7d8200760343333 0xbdf60801d80d0ccc

def z473 : W := mkw 0xb413fbccb8044154 0x2d04fef32e011055 0x7bef5388f84cc3ff 0xdefbd4e23e1330ff

def z474 : W := mkw 0x0000000100101020 0x0000000040040408 0xeebc30078038303f 0x7baf0c01e00e0c0f

def z475 : W := mkw 0x01000a0000028000 0x004002800000a000 0x01000e000007c000 0x004003800001f000

def z476 : W := mkw 0x21413a85823a942a 0x88504ea1608ea50a 0x21803e07803fc03d 0x08600f81e00ff00f

def z477 : W := mkw 0x0280000005400881 0x00a0000001500220 0x0004000006400cc0 0x4001000001900330

def z478 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd658c07801c033c2 0xb596301e00700cf0

def z479 : W := mkw 0x3c43ffefd238142a 0x8f10fffbf48e050a 0x3ffbfffff838003d 0x0ffefffffe0e000f

def z480 : W := mkw 0x3f03ff6a576a8002 0x0fc0ffda95daa000 0xd1fbfe787fffc001 0xf47eff9e1ffff000

def z481 : W := mkw 0xa313fa002f6ec156 0x28c4fe800bdbb055 0xc1fffe0007ffc3ff 0xf07fff8001fff0ff

def z482 : W := mkw 0x2303fa1007eaa202 0x08c0fe8401faa880 0xd7fbfe7007fff303 0xf5feff9c01fffcc0

def z483 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe0bb30078638003d 0x782ecc01e18e000f

def z484 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffffffff84003c2 0xdffffffffe1000f0

def z485 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x05fbfff700000000 0x017efffdc0000000

def z486 : W := mkw 0x23013000076a8002 0x08c04c0001daa000 0xc0bb300007ffc001 0xf02ecc0001fff000

def z487 : W := mkw 0x286134a7e23d153a 0xca184d29f88f454e 0x21803c07e03f003d 0x08600f01f80fc00f

def z488 : W := mkw 0x0000000020040110 0x0000000008010044 0x7bec1000e00c033f 0xdefb0400380300cf

def z489 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe69b218706303c33 0x39a6c861c18c0f0c

def z490 : W := mkw 0x1822c57b60953330 0x4608b15ed8254ccc 0xfffbedff61b73333 0xbffefb7fd86dcccc

def z491 : W := mkw 0x2b63feb7e7ffb73a 0xcad8ffadf9ffedce 0xfffffff7e7ffff3f 0xfffffffdf9ffffcf

def z492 : W := mkw 0xa0513084aa2c455e 0xa8144c212a8b1157 0x7bef5388fe4ccfff 0xdefbd4e23f9333ff

def z493 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x2fbb3f87f8000000 0x0beecfe1fe000000

def z494 : W := mkw 0x8010000028044154 0x200400000a011055 0x6bac1200f80cc03f 0x5aeb04803e03300f

def z495 : W := mkw 0x2001300002280002 0x08004c00008a0000 0xc1fb7200067cc001 0xf07edc80019f3000

def z496 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x41e8de0001cfc001 0xd07a37800073f000

def z497 : W := mkw 0xa313fa000f6ac046 0x28c4fe8003dab011 0xc9fffe089fffc0cd 0xf27fff8227fff033

def z498 : W := mkw 0x8010000028044154 0x200400000a011055 0x000000000044c3c0 0x80000000001130f0

def z499 : W := mkw 0xbc13ffeef8044154 0x2f04fffbbe011055 0x3ffbfffff844c3c0 0x8ffefffffe1130f0

def z500 : W := mkw 0xa01130002a2c4156 0x28044c000a8b1055 0xfbff7208fe7cc3ff 0xfeffdc823f9f30ff

def z501 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0x7bec720ff87cc3ff 0xdefb1c83fe1f30ff

def z502 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x5a6cc07801c003c2 0xd69b301e007000f0

def z503 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc1fbec0007f70001 0xf07efb0001fdc000

def z504 : W := mkw 0x3283f15807e82a83 0x0ca0fc5601fa0aa0 0xdefff1f807f83fc3 0xf7bffc7e01fe0ff0

def z505 : W := mkw 0x2343fa85877a942a 0x88d0fea161dea50a 0xc5fbff8707fffc01 0xf17effe1c1ffff00

def z506 : W := mkw 0x2303fa00276e8112 0x08c0fe8009dba044 0xf3fbfe0067ffc333 0xfcfeff8019fff0cc

def z507 : W := mkw 0xbc33fffff8957374 0x6f0cfffffe255cdd 0xfffffffff9fff3ff 0xfffffffffe7ffcff

def z508 : W := mkw 0x829000102dc46bd5 0x20a400040b711af5 0xfbec5208ffccffff 0xfefb14823ff33fff

def z509 : W := mkw 0x3003fb4800000000 0x0c00fed200000000 0x1ffbfff800000000 0x07fefffe00000000

def z510 : W := mkw 0x2821343362bd3332 0x4a084d0cd8af4ccc 0xf7fbbc7767bf3333 0xfdfeef1dd9efcccc

def z511 : W := mkw 0x204130010238142a 0x88104c00408e050a 0xc0bf300006383c3f 0x702fcc00018e0f0f

def z512 : W := mkw 0x3ba3ff7b67ffbbb3 0x4ee8ffded9ffeeec 0xffffffff67fffff3 0xffffffffd9fffffc

def z513 : W := mkw 0x0202c01005c02200 0x0080b00401700880 0xd67bc07007c03302 0xf59ef01c01f00cc0

def z514 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xc827418807c03fc2 0xf209d06201f00ff0

def z515 : W := mkw 0x3383fb5807eaaa83 0x0ce0fed601faaaa0 0x8413adf007b33c00 0x2104eb7c01eccf00

def z516 : W := mkw 0x0080001000802a81 0x0020000400200aa0 0x0004000000003fc2 0x0001000000000ff0

def z517 : W := mkw 0x8010000028044154 0x200400000a011055 0x7a6c4008f84003fe 0xde9b10023e1000ff

def z518 : W := mkw 0x0020001120953330 0x4008000448254ccc 0xe698200701b73333 0xb9a60801c06dcccc

def z519 : W := mkw 0x0020000120151130 0x400800004805444c 0x0000000000370031 0x00000000000dc00c

def z520 : W := mkw 0x8830042368155174 0x620c0108da05545d 0x21803e07f83fc03d 0x08600f81fe0ff00f

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e3b018000000000 0x038ec06000000000

def z522 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0x10000078000003c0 0x0400001e000000f0

def z523 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x37802c7760373333 0x0de00b1dd80dcccc

def z524 : W := mkw 0xa1113a002a2ec156 0x28444e800a8bb055 0x21803e00f83fc03d 0x08600f803e0ff00f

def z525 : W := mkw 0x204130848228040a 0x88104c21208a0102 0x0003018006000c00 0x0000c06001800300

def z526 : W := mkw 0x3383fb5807eaaa83 0x0ce0fed601faaaa0 0xde7fd3f807c8ffc2 0xf79ff4fe01f23ff0

def z527 : W := mkw 0xa87134b7eabd777e 0xea1c4d2dfaaf5ddf 0xffffffffffffffff 0xffffffffffffffff

def z528 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x2ebbbdf780000000 0x0baeef7de0000000

def z529 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xce3f218706303c02 0x738fc861c18c0f00

def z530 : W := mkw 0x8010000128145174 0x200400004a05145d 0xfffc720ff87cf3ff 0xffff1c83fe1f3cff

def z531 : W := mkw 0x2b23fe3267efa312 0x4ac8ff8c99fbe8c4 0xd1fbfe7067ffc301 0xf47eff9c19fff0c0

def z532 : W := mkw 0xa05130858a38546e 0xa8144c21628e151b 0xeebf738f9e78fcff 0x7bafdce3e79e3f3f

def z533 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x0163de0007cfc000 0xc058f78001f3f000

def z534 : W := mkw 0x3ec3ffffd7f83eab 0x8fb0fffff5fe0faa 0xfffffffffff83fff 0xfffffffffffe0fff

def z535 : W := mkw 0x0820042340111020 0x42080108d0044408 0x00002c0700330000 0x00000b01c00cc000

def z536 : W := mkw 0x22c1309587f83eab 0x88b04c2561fe0faa 0xeebf318787f83fff 0xfbafcc61e1fe0fff

def z537 : W := mkw 0x1002c15800802200 0x0400b05600200880 0xde7bc1f801803302 0xb79ef07e00600cc0

def z538 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0xc1803e0007ffc001 0xf0600f8001fff000

def z539 : W := mkw 0x2343fa85877a942a 0x88d0fea161dea50a 0xeebfbd8787bb3c3f 0x7bafef61e1eecf0f

def z540 : W := mkw 0x2001308480000000 0x08004c2120000000 0x6ebf31878008003f 0x5bafcc61e002000f

def z541 : W := mkw 0x8010000008004044 0x2004000002001011 0x5a6c52089848c3ce 0xd69b1482261230f3

def z542 : W := mkw 0x8010000028044154 0x200400000a011055 0x73cc0000604cc3ff 0xdcf30000181330ff

def z543 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0x040001f000003c00 0x0100007c00000f00

def z544 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x2ebb31878038003d 0x0baecc61e00e000f

def z545 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x2593bff7f8000000 0x0964effdfe000000

def z546 : W := mkw 0x0020001120953330 0x4008000448254ccc 0xf3c8000061b73333 0xbcf20000186dcccc

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x6bec5200804cc03f 0xdafb14802013300f

def z548 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1963dff8f8000000 0x0658f7fe3e000000

def z549 : W := mkw 0x0002ca0000000000 0x0000b28000000000 0x0140ce0000000000 0x0050338000000000

def z550 : W := mkw 0x32c3f1cc87680c8b 0x8cb0fc7321da0322 0x0827518886480ccc 0x4209d46221920333

def z551 : W := mkw 0x2001300002280002 0x08004c00008a0000 0xcebf318006383c03 0x73afcc60018e0f00

def z552 : W := mkw 0x80500085a814557c 0xa01400216a05155f 0x3e04018ff8003ffe 0x0f810063fe000fff

def z553 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0x00004008004000c0 0x0000100200100030

def z554 : W := mkw 0x0820042360151130 0x42080108d805444c 0x37d8ac7760370031 0x0df62b1dd80dc00c

def z555 : W := mkw 0x8010000008004044 0x2004000002001011 0x6aac52089848c0ff 0x5aab14822612303f

def z556 : W := mkw 0x3683fbdc95c02a81 0x0da0fef725700aa0 0xde7fd3f89fc03fc2 0xf79ff4fe27f00ff0

def z557 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0xde5c81f801803fc2 0xb797207e00600ff0

def z558 : W := mkw 0x2003fa8480000000 0x0800fea120000000 0x2ffbff8780000000 0x0bfeffe1e0000000

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0x5248000000000302 0x94920000000000c0

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x002052000048c000 0x4008148000123000

def z561 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0xdf7fc3f87fc4ffc2 0xf7dff0fe1ff13ff0

def z562 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x29a37f8ff8000000 0x0a68dfe3fe000000

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x0827018006000c00 0x4209c06001800300

def z564 : W := mkw 0x8010000028044154 0x200400000a011055 0x48245208984cc3ff 0xd2091482261330ff

def z565 : W := mkw 0x1e82cf7a55c02a81 0x07a0b3de95700aa0 0x1140ce7879c003c0 0x8450339e1e7000f0

def z566 : W := mkw 0x0020001120953330 0x4008000448254ccc 0x0000000000003332 0x0000000000000ccc

def z567 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3f40cffff8000000 0x0fd033fffe000000

def z568 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe69830078038303f 0x39a60c01e00e0c0f

def z569 : W := mkw 0x0000001000802200 0x0000000400200880 0x8410807001803000 0x2104201c00600c00

def z570 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd07bc07807c003c0 0xf41ef01e01f000f0

def z571 : W := mkw 0x3c43ffefd238142a 0x8f10fffbf48e050a 0xbffbfffffe303c00 0x2ffeffffff8c0f00

def z572 : W := mkw 0x2b23fe3367ffb332 0x4ac8ff8cd9ffeccc 0xf7dbac7767b73333 0xbdf6eb1dd9edcccc

def z573 : W := mkw 0x0820042260050110 0x4208010898014044 0x01000c0060070000 0x004003001801c000

def z574 : W := mkw 0x3443fbcc9228040a 0x8d10fef3248a0102 0x082753889e080c0c 0x4209d4e227820303

def z575 : W := mkw 0x3c23ffffd0913220 0x4f08fffff4244c88 0xbffbfffff9b33000 0x2ffefffffe6ccc00

def z576 : W := mkw 0x8010000028044154 0x200400000a011055 0x20000000f800003c 0x080000003e00000f

def z577 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0x5a6f418806400fc2 0xd69bd062019003f0

def z578 : W := mkw 0x1aa2c57b65d53bb1 0x46a8b15ed9754eec 0xf7d8ec7f61f733f3 0xbdf63b1fd87dccfc

def z579 : W := mkw 0x0000000100101020 0x0000000040040408 0xc000000000303033 0x30000000000c0c0c

def z580 : W := mkw 0x2343fa85877a942a 0x88d0fea161dea50a 0xe1fbfe0787ffc03d 0xf87eff81e1fff00f

def z581 : W := mkw 0x3c23fffff0953330 0x4f08fffffc254ccc 0x3ffbfffff8003332 0x0ffefffffe000ccc

def z582 : W := mkw 0x0860043362bd373a 0xc218010cd8af4dce 0xf7dcac7767bf3f3f 0xfdf72b1dd9efcfcf

def z583 : W := mkw 0xa313fa000f6ac046 0x28c4fe8003dab011 0x082752089e48c0cc 0x4209d48227923033

def z584 : W := mkw 0x0000001000802200 0x0000000400200880 0x1040807001800300 0x8410201c006000c0

def z585 : W := mkw 0x0000000020040110 0x0000000008010044 0xf3d8ac0061b70333 0xbcf62b00186dc0cc

def z586 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0xfffbfffffe380001 0x7ffeffffff8e0000

def z587 : W := mkw 0x2303fa01077a9022 0x08c0fe8041dea408 0xe7fbfe0707fff033 0xf9feff81c1fffc0c

def z588 : W := mkw 0x1082c15800802a81 0x0420b05600200aa0 0x1e7fc1f800003fc2 0x079ff07e00000ff0

def z589 : W := mkw 0x0800042240000000 0x0200010890000000 0x3600007760000000 0x0d80001dd8000000

def z590 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3fe853fff8000000 0x0ffa14fffe000000

def z591 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x5e7fc1f8004003c2 0xd79ff07e001000f0

def z592 : W := mkw 0x2001308480000000 0x08004c2120000000 0xeebf318786003c02 0x7bafcc61e1800f00

def z593 : W := mkw 0x1c8005fed0802a81 0x0720017fb4200aa0 0x3e0401fff8003fc2 0x0f81007ffe000ff0

def z594 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x0c33ffff98000000 0x030cffffe6000000

def z595 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xaebb318786303c00 0x2baecc61e18c0f00

def z596 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x37408c7761873332 0x8dd0231dd861cccc

def z597 : W := mkw 0x204130848228040a 0x88104c21208a0102 0x000010008008000c 0x0000040020020003

def z598 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xc47bc1f007c03c00 0xf11ef07c01f00f00

def z599 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0xc1fbfe0001b70001 0xb07eff80006dc000

def z600 : W := mkw 0x3283f1dc85c02a81 0x0ca0fc7721700aa0 0xfefff1ff87c03fc2 0xffbffc7fe1f00ff0

def z601 : W := mkw 0x8010000008004044 0x2004000002001011 0x000012009808c00c 0x0000048026023003

def z602 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1e44c1f801c03fc2 0x8791307e00700ff0

def z603 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x37d8ac7760003332 0x0df62b1dd8000ccc

def z604 : W := mkw 0x3c4135efd238142a 0x8f104d7bf48e050a 0xfebf31fffe383c3f 0x7fafcc7fff8e0f0f

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x01802c0000370001 0x00600b00000dc000

def z606 : W := mkw 0x8810042268044154 0x220401089a011055 0x7ffcfe7ff84cc3ff 0xdfff3f9ffe1330ff

def z607 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x0823418800000000 0x0208d06200000000

def z608 : W := mkw 0x8312ca002d46c154 0x20c4b2800b51b055 0x7becde08f9cfc3ff 0xdefb37823e73f0ff

def z609 : W := mkw 0x0820042360151130 0x42080108d805444c 0x2000000760000030 0x08000001d800000c

def z610 : W := mkw 0x0800042340101020 0x02000108d0040408 0xf7d8ac7760303033 0x3df62b1dd80c0c0c

def z611 : W := mkw 0x8312ca002d46c154 0x20c4b2800b51b055 0x1140ce0879c7c3c0 0x845033821e71f0f0

def z612 : W := mkw 0x1382cb5805c2aa81 0x04e0b2d60170aaa0 0x1140ce7801c7c3c0 0x8450339e0071f0f0

def z613 : W := mkw 0x8010000008004044 0x2004000002001011 0x000042081840c0c0 0x0000108206103030

def z614 : W := mkw 0x0020001100913220 0x4008000440244c88 0x8000000001b33000 0x20000000006ccc00

def z615 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x7fec527ff84cf3ff 0xdffb149ffe133cff

def z616 : W := mkw 0x1282c15905d03aa1 0x04a0b05641740ea8 0xfeffe1ff07f03ff3 0xffbff87fc1fc0ffc

def z617 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x3be8de78f8000000 0x0efa379e3e000000

def z618 : W := mkw 0x2383fa1007eaaa83 0x08e0fe8401faaaa0 0xc1fffe0007ffffc3 0xf07fff8001fffff0

def z619 : W := mkw 0x8010001028846354 0x200400040a2118d5 0xfffcd278f9ccf3ff 0xffff349e3e733cff

def z620 : W := mkw 0x1080014800000881 0x0420005200000220 0x0804018800000cc0 0x0201006200000330

def z621 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x6aac30078038003f 0x5aab0c01e00e000f

def z622 : W := mkw 0x2823fe3360953330 0x4a08ff8cd8254ccc 0xf7fbfe7761b73333 0xbdfeff9dd86dcccc

def z623 : W := mkw 0x0000000020040110 0x0000000008010044 0x2180000060040031 0x086000001801000c

def z624 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x0000807001800000 0x0000201c00600000

def z625 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x77c8007760043333 0x9df2001dd8010ccc

def z626 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xc827118086383c3f 0x7209c460218e0f0f

def z627 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd65b81f007803f02 0xb596e07c01e00fc0

def z628 : W := mkw 0x2c213eb7f0953330 0x4b084fadfc254ccc 0xf7d8be77f9b73333 0xbdf62f9dfe6dcccc

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x7bec5208f808003f 0x5efb14823e02000f

def z630 : W := mkw 0x004000010238142a 0x80100000408e050a 0xe69c200706383c3f 0x79a70801c18e0f0f

def z631 : W := mkw 0xb393fb582feeebd7 0x2ce4fed60bfbbaf5 0xfffffff8ffffffff 0xfffffffe3fffffff

def z632 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xce7fc18007c03c02 0xf39ff06001f00f00

def z633 : W := mkw 0x1aa2c57b45d13aa1 0x46a8b15ed1744ea8 0x8413adf707b33c00 0x2104eb7dc1eccf00

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x08244008004000c0 0x4209100200100030

def z635 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x3be87e0ff8000000 0x0efa1f83fe000000

def z636 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0x7becd278f9ccc3ff 0xdefb349e3e7330ff

def z637 : W := mkw 0x8010000028044154 0x200400000a011055 0x5b6c42087844c3c2 0xd6db10821e1130f0

def z638 : W := mkw 0xbc53ffeffa3c557e 0xaf14fffbfe8f155f 0xfffffffffe7cffff 0xffffffffff9f3fff

def z639 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x3ffbfffffe48c000 0x4ffeffffff923000

def z640 : W := mkw 0x0aa0043365d53bb1 0x42a8010cd9754eec 0xf7dcac7767f73ff3 0xfdf72b1dd9fdcffc

def z641 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0x1140c27879c4c3c0 0x8450309e1e7130f0

def z642 : W := mkw 0x2001308480000000 0x08004c2120000000 0x3ffb738ff8000000 0x0ffedce3fe000000

def z643 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x3bfbfe08f8000000 0x0efeff823e000000

def z644 : W := mkw 0x1aa2c57b65d53bb1 0x46a8b15ed9754eec 0xfe7fc1ff67c03ff2 0xff9ff07fd9f00ffc

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004000006003c02 0x7001000001800f00

def z646 : W := mkw 0x0000000100101020 0x0000000040040408 0x2080200700300031 0x08200801c00c000c

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x1658807000000000 0x0596201c00000000

def z648 : W := mkw 0x3ea3fffff5d53bb1 0x4fa8fffffd754eec 0xfffffffffff73ff3 0xfffffffffffdcffc

def z649 : W := mkw 0x086004b7e0953738 0xc218012df8254dce 0xffdcadf7e1b73f3f 0xbff72b7df86dcfcf

def z650 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xc5fbfff707ffc001 0xf17efffdc1fff000

def z651 : W := mkw 0x3e83fffed5c02a81 0x0fa0ffffb5700aa0 0xbffbffffff803c00 0x2ffeffffffe00f00

def z652 : W := mkw 0x80500085a814557c 0xa01400216a05155f 0x7fec538ff84cffff 0xdffb14e3fe133fff

def z653 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x01fbfe000648c000 0x407eff8001923000

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x400400000008003f 0x500100000002000f

def z655 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x00008c7000000000 0x0000231c00000000

def z656 : W := mkw 0x9292c1482d4449d5 0x24a4b0520b511275 0x7bef5388fe4ccfff 0xdefbd4e23f9333ff

def z657 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x00008c0001830000 0x000023000060c000

def z658 : W := mkw 0x8010000028044154 0x200400000a011055 0x7aac1008f80803ff 0x5eab04023e0200ff

def z659 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0x000012000008c000 0x0000048000023000

def z660 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0x0003018006000c00 0x0000c06001800300

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x21801200f8000000 0x086004803e000000

def z662 : W := mkw 0x8010000028044154 0x200400000a011055 0x41ec5200004cc3ff 0xd07b1480001330ff

def z663 : W := mkw 0x8010000028044154 0x200400000a011055 0x51444208784cc3ff 0xd45110821e1330ff

def z664 : W := mkw 0x8010000028044154 0x200400000a011055 0x3b444208f844c3fe 0x8ed110823e1130ff

def z665 : W := mkw 0x2343fa85877a942a 0x88d0fea161dea50a 0x8413ad8707b33c00 0x2104eb61c1eccf00

def z666 : W := mkw 0x8010000008004044 0x2004000002001011 0x3bec5208f848c0cc 0x4efb14823e123033

def z667 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0xefbf3387fe3cfc3f 0x7befcce1ff8f3f0f

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x01408c0001870000 0x805023000061c000

def z669 : W := mkw 0x1282c14805400881 0x04a0b05201500220 0xc87fc18807c00cc0 0xf21ff06201f00330

def z670 : W := mkw 0x8010000028044154 0x200400000a011055 0x61e85200f84cc03d 0xd87a14803e13300f

def z671 : W := mkw 0x286134b7c2b9362a 0xca184d2df0ae4d8a 0x8413adf707b33c00 0x2104eb7dc1eccf00

def z672 : W := mkw 0x2001308580101020 0x08004c2160040408 0xeebb318780303033 0x3baecc61e00c0c0c

def z673 : W := mkw 0x286134a7e23d153a 0xca184d29f88f454e 0xefbf3d87e63f3c3f 0x7befcf61f98fcf0f

def z674 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1867c1f807c00fc0 0xc619f07e01f003f0

def z675 : W := mkw 0x8010000028044154 0x200400000a011055 0x19645208f84cc3cc 0xc65914823e1330f3

def z676 : W := mkw 0x0000000020040110 0x0000000008010044 0x1140000060040300 0x84500000180100c0

def z677 : W := mkw 0x286134b7e2bd373a 0xca184d2df8af4dce 0xf7d8bc77e1bf333f 0xbdf62f1df86fcccf

def z678 : W := mkw 0x0302c000076a8002 0x00c0b00001daa000 0xc07bc00007ffc001 0xf01ef00001fff000

def z679 : W := mkw 0x3c43ffefd238142a 0x8f10fffbf48e050a 0xeebfbdf786383c3f 0x7bafef7de18e0f0f

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0x01d8ac0000000000 0x00762b0000000000

def z681 : W := mkw 0x1002c14800000000 0x0400b05200000000 0xde7fc1f806003c02 0x779ff07e01800f00

def z682 : W := mkw 0xac113ea6f8044154 0x2b044fa9be011055 0x21803e07f80cc03d 0x08600f81fe03300f

def z683 : W := mkw 0x8010000028044154 0x200400000a011055 0x29a45208f84cc0fd 0x4a6914823e13303f

def z684 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x0023520000000000 0x0008d48000000000

def z685 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0x082753808648cc0c 0x4209d4e021923303

def z686 : W := mkw 0x004000010238142a 0x80100000408e050a 0xeaac100086383c3f 0x7aab0400218e0f0f

def z687 : W := mkw 0x8010000028044154 0x200400000a011055 0x010002007804c000 0x004000801e013000

def z688 : W := mkw 0x2001300002280002 0x08004c00008a0000 0xeabf30008638003f 0x7aafcc00218e000f

def z689 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0xda6c400807c03fc2 0xf69b100201f00ff0

def z690 : W := mkw 0x0800042240000000 0x0200010890000000 0x21802c0760000000 0x08600b01d8000000

def z691 : W := mkw 0x204130848228040a 0x88104c21208a0102 0xc8bf318086380c0d 0x722fcc60218e0303

def z692 : W := mkw 0x831000002f6ec156 0x20c400000bdbb055 0xc004000007ffc3ff 0xf001000001fff0ff

def z693 : W := mkw 0x8010000008004044 0x2004000002001011 0x08040008980000cc 0x0201000226000033

def z694 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x8c37318786383c0c 0x630dcc61e18e0f03

def z695 : W := mkw 0x3c03fffed0802200 0x0f00ffffb4200880 0xfffbfffff9803302 0xbffefffffe600cc0

def z696 : W := mkw 0x2203f00007680002 0x0880fc0001da0000 0xc0fbf00007f80001 0xf03efc0001fe0000

def z697 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x041381f000000000 0x0104e07c00000000

def z698 : W := mkw 0x0b22ce3265c7a310 0x42c8b38c9971e8c4 0x1140ce7061c7c300 0x8450339c1871f0c0

def z699 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc023520007ffc001 0xf008d48001fff000

def z700 : W := mkw 0xbc13ffeef8044154 0x2f04fffbbe011055 0x3ffffffff80003fe 0x0ffffffffe0000ff

def z701 : W := mkw 0x18a0057b60953bb1 0x4628015ed8254eec 0xffdcadff61b73ff3 0xbff72b7fd86dcffc

def z702 : W := mkw 0x0820043260852310 0x4208010c982148c4 0xd1d8ac7061b70301 0xb4762b1c186dc0c0

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0xde7f418806403fc2 0xf79fd06201900ff0

def z704 : W := mkw 0xa013fa0028044154 0x2804fe800a011055 0x7bfffe08f84cc3ff 0xdeffff823e1330ff

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c8000000040001 0x9072000000010000

def z706 : W := mkw 0x1a82c57a45c02a81 0x06a0b15e91700aa0 0xffffedff67c03fc2 0xfffffb7fd9f00ff0

def z707 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xa410ac7761b33030 0x29042b1dd86ccc0c

def z708 : W := mkw 0x3f43ffeed76a840a 0x8fd0fffbb5daa102 0x3ffffffffe48cc0c 0x4fffffffff923303

def z709 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8ac7f79b733f3 0xbdf62b1fde6dccfc

def z710 : W := mkw 0x1f0005eed76a8002 0x07c0017bb5daa000 0xfe0001ffffffc001 0xff80007ffffff000

def z711 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3e33fffff8000000 0x0f8cfffffe000000

def z712 : W := mkw 0x8830043348917264 0x620c010cd2245c99 0x8c34fe7f99fbf0cc 0x630d3f9fe67efc33

def z713 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xae97318786383c3f 0x2ba5cc61e18e0f0f

def z714 : W := mkw 0x8010000028044154 0x200400000a011055 0xfffc5208f84cf3ff 0xffff14823e133cff

def z715 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3f8013fff8000000 0x0fe004fffe000000

def z716 : W := mkw 0x8010000028044154 0x200400000a011055 0x7aac5208f848c3ff 0x5eab14823e1230ff

def z717 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x3ffbfffff9ffc001 0x8ffefffffe7ff000

def z718 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x140001ff78000000 0x0500007fde000000

def z719 : W := mkw 0x0800042260040110 0x0200010898010044 0xf7d8ac7761b70333 0xbdf62b1dd86dc0cc

def z720 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x9550ac7761b33000 0x25542b1dd86ccc00

def z721 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffbfffff8000302 0x9ffefffffe0000c0

def z722 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffbfffff9ffc001 0xfffefffffe7ff000

def z723 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x37c0ac7761b73333 0x8df02b1dd86dcccc

def z724 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x3e002dfff8000000 0x0f800b7ffe000000

def z725 : W := mkw 0x0820042360151130 0x42080108d805444c 0xf7d8ac7761b70031 0xbdf62b1dd86dc00c

def z726 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xa593bff7ffbfc001 0x2964effdffeff000

def z727 : W := mkw 0xac513ea7fa3c557e 0xab144fa9fe8f155f 0x21803e07f83cc03d 0x08600f81fe0f300f

def z728 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc1f8fe0007ffc001 0xf07e3f8001fff000

def z729 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0xeffbff8f9fffc001 0xfbfeffe3e7fff000

def z730 : W := mkw 0x0800042240000000 0x0200010890000000 0xfff8fe7ff9ffc001 0xfffe3f9ffe7ff000

def z731 : W := mkw 0x21413a85823a942a 0x88504ea1608ea50a 0xefffbf8787bffc3f 0xfbffefe1e1efff0f

def z732 : W := mkw 0x3e83ffeed5400881 0x0fa0fffbb5500220 0xffffffffffc00cc0 0xfffffffffff00330

def z733 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffffffff84cc03f 0xdffffffffe13300f

def z734 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xfeff318786383f3f 0xffbfcc61e18e0fcf

def z735 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe69b318786383c3f 0x39a6cc61e18e0f0f

def z736 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x37dbbff7f8000000 0x0df6effdfe000000

def z737 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3140ce7ff8000000 0x0c50339ffe000000

def z738 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefffff8787fffc3f 0xfbffffe1e1ffff0f

def z739 : W := mkw 0xb713fbccbf6ec156 0x2dc4fef32fdbb055 0x7bef5388fe4cc3ff 0xdefbd4e23f9330ff

def z740 : W := mkw 0x3c43ffeed228040a 0x8f10fffbb48a0102 0xfffffffffe083c0e 0x7fffffffff820f03

def z741 : W := mkw 0x0800042340101020 0x02000108d0040408 0xf7d8ac7761b73033 0xbdf62b1dd86dcc0c

def z742 : W := mkw 0x32c3f1dd87f83eab 0x8cb0fc7761fe0faa 0x30c0f07f81f803fd 0x8c303c1fe07e00ff

def z743 : W := mkw 0x0280001005c02a81 0x00a0000401700aa0 0xde7f81f007c03fc2 0xf79fe07c01f00ff0

def z744 : W := mkw 0x3c43ffeed228040a 0x8f10fffbb48a0102 0xfffffffffe380c0d 0x7fffffffff8e0303

def z745 : W := mkw 0x2b03fe22476a8002 0x0ac0ff8891daa000 0xfffbfe7fffffc001 0xfffeff9ffffff000

def z746 : W := mkw 0x3c43ffeed228040a 0x8f10fffbb48a0102 0x7ffffffffe080c3f 0x5fffffffff82030f

def z747 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xa413218786303c3c 0x2904c861e18c0f0f

def z748 : W := mkw 0x2b23fe3367ffb332 0x4ac8ff8cd9ffeccc 0x362352776648f332 0x4d88d49dd9923ccc

def z749 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xa590ac7761b33000 0x29642b1dd86ccc00

def z750 : W := mkw 0xa0513085aa3c557e 0xa8144c216a8f155f 0x9553638f7e74ffc0 0xa554d8e3df9d3ff0

def z751 : W := mkw 0x0800042240000000 0x0200010890000000 0x3e00007ff8000000 0x0f80001ffe000000

def z752 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x3ffbfffffe000000 0x0ffeffffff800000

def z753 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xaebb318786383c3d 0x2baecc61e18e0f0f

def z754 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xbffbfffffe003c00 0x2ffeffffff800f00

def z755 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x2db3fffff8000000 0x0b6cfffffe000000

def z756 : W := mkw 0x23013000076a8002 0x08c04c0001daa000 0xc1fbbc0007ffc001 0xf07eef0001fff000

def z757 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc5f8fe7701fff001 0xf17e3f9dc07ffc00

def z758 : W := mkw 0x0800042240000000 0x0200010890000000 0x3fd8ac7ff8000000 0x0ff62b1ffe000000

def z759 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x31c0ee7f78000000 0x0c703b9fde000000

def z760 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x3600007f780033f2 0x0d80001fde000cfc

def z761 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1e7fc1f806403fc2 0x479ff07e01900ff0

def z762 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0xc1fbff8007ffc001 0xf07effe001fff000

def z763 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffbfffff9800000 0xbffefffffe600000

def z764 : W := mkw 0x08a0043360953bb1 0x4228010cd8254eec 0xf7dcac7761b73ff3 0xbdf72b1dd86dcffc

def z765 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffbadf761b73333 0xbffeeb7dd86dcccc

def z766 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf658ac7761b33332 0xbd962b1dd86ccccc

def z767 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffd8ac7ff9b73333 0xbff62b1ffe6dcccc

def z768 : W := mkw 0x1aa2c56b655519b1 0x46a8b15ad955466c 0x29a76d8f66770cf1 0x4a69db63d99dc33c

def z769 : W := mkw 0x3e83ffeed5400881 0x0fa0fffbb5500220 0x7ffffffffe400fc2 0xdfffffffff9003f0

def z770 : W := mkw 0x3003f1cc80000000 0x0c00fc7320000000 0x3ffbf3fff8000000 0x0ffefcfffe000000

def z771 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0xfffbffffffbf0001 0xfffeffffffefc000

def z772 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3f802dfff8000000 0x0fe00b7ffe000000

def z773 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x35d3fffff8000000 0x0d74fffffe000000

def z774 : W := mkw 0x2041308580101428 0x88104c216004050a 0xeebf318786003c3e 0x7bafcc61e1800f0f

def z775 : W := mkw 0x8010000028044154 0x200400000a011055 0x3bec5208f848c3fe 0x4efb14823e1230ff

def z776 : W := mkw 0x8010000028044154 0x200400000a011055 0x73c85208f84cc3ff 0x9cf214823e1330ff

def z777 : W := mkw 0x0040008580101428 0x801000216004050a 0x2e27018786003c3e 0x4b89c061e1800f0f

def z778 : W := mkw 0x3f03ffeed5428000 0x0fc0fffbb550a000 0xfffbffffffc7c000 0xfffefffffff1f000

def z779 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fedf807f33fc2 0xf79ffb7e01fccff0

def z780 : W := mkw 0x1c02c5eed0000000 0x0700b17bb4000000 0x3e40c1fff8000000 0x0f90307ffe000000

def z781 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3e008dfff8000000 0x0f80237ffe000000

def z782 : W := mkw 0x0000000100101020 0x0000000040040408 0xeebf318786383c3f 0x7bafcc61e18e0f0f

def z783 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffffffff84cc3c3 0xdffffffffe1330f0

def z784 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e6841fff8000000 0x0f9a107ffe000000

def z785 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xc5fbfff007ffc001 0xf17efffc01fff000

def z786 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc9fffe0807ffc0c1 0xf27fff8201fff030

def z787 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc410ac7701b33033 0x31042b1dc06ccc0c

def z788 : W := mkw 0x1c8005eed0000881 0x0720017bb4000220 0x3e0401fff8000cc0 0x0f81007ffe000330

def z789 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0x9e1701f806003fc2 0x2785c07e01800ff0

def z790 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffbffffffc8c000 0xfffefffffff23000

def z791 : W := mkw 0x3c0135eed0000000 0x0f004d7bb4000000 0x3e2311fff8000000 0x0f88c47ffe000000

def z792 : W := mkw 0x3ec3ffeed7680c8b 0x8fb0fffbb5da0322 0x3ffffffffe480ccc 0x4fffffffff920333

def z793 : W := mkw 0x8010000028044154 0x200400000a011055 0xfbff5208fe4cc3ff 0xfeffd4823f9330ff

def z794 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcee7f79f7f3f3 0xffff3b9fde7dfcfc

def z795 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xffdcbe7ff9bff3ff 0xbff72f9ffe6ffcff

def z796 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0xc1e8de0007ffc001 0xf07a378001fff000

def z797 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0xc1e87e0007ffc001 0xf07a1f8001fff000

def z798 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0x3ffbfffffe400000 0x4ffeffffff900000

def z799 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3e0043fff8000000 0x0f8010fffe000000

def z800 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0xc004000001b733ff 0xb0010000006dccff

def z801 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc7fbfe0007fff003 0xf1feff8001fffc00

def z802 : W := mkw 0x9c3005fff8957374 0x670c017ffe255cdd 0x3e0401fff80033fe 0x0f81007ffe000cff

def z803 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffbffffffb70001 0xbffeffffffedc000

def z804 : W := mkw 0xa313fa002f6ec156 0x28c4fe800bdbb055 0xba17ac08ffb303fe 0x2e85eb023fecc0ff

def z805 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0xffffffffffc003c2 0xfffffffffff000f0

def z806 : W := mkw 0xa87134a7ea3d557e 0xea1c4d29fa8f555f 0x21803e07f83fc03d 0x08600f81fe0ff00f

def z807 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0xc1fbfe0807ffc0c1 0xf07eff8201fff030

def z808 : W := mkw 0xbc13ffeef8044154 0x2f04fffbbe011055 0x4417adf7004cc3ff 0xd105eb7dc01330ff

def z809 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0xcfffff8087fffc0f 0xf3ffffe021ffff03

def z810 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xce3fadf707b33c02 0x738feb7dc1eccf00

def z811 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x8410ac7701b33332 0x21042b1dc06ccccc

def z812 : W := mkw 0x0800042240000000 0x0200010890000000 0xb7d8ac7761b30000 0x2df62b1dd86cc000

def z813 : W := mkw 0x3c43ffeed228040a 0x8f10fffbb48a0102 0x3ffbfffff808000c 0x0ffefffffe020003

def z814 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff9870000 0x8ffefffffe61c000

def z815 : W := mkw 0x33c3fbcc876a8c8b 0x8cf0fef321daa322 0xc9ffff8887ffcccd 0xf27fffe221fff333

def z816 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x37d8fe7ff8000000 0x0df63f9ffe000000

def z817 : W := mkw 0x3f03ffeed5428000 0x0fc0fffbb550a000 0x7ffbfffff9cfc001 0xdffefffffe73f000

def z818 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x8413218706383c3d 0x2104c861c18e0f0f

def z819 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc498ac7701b33001 0x31262b1dc06ccc00

def z820 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e10adfff8000000 0x0f842b7ffe000000

def z821 : W := mkw 0x280134a6c0000000 0x0a004d29b0000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z822 : W := mkw 0x3423fbddb0953330 0x4d08fef76c254ccc 0xc823538899b73333 0xb208d4e2266dcccc

def z823 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x37dbefff78000000 0x0df6fbffde000000

def z824 : W := mkw 0x21413a85823a942a 0x88504ea1608ea50a 0xefff7f87867ffc3f 0xfbffdfe1e19fff0f

def z825 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xffdcac7ff9fff3ff 0xfff72b1ffe7ffcff

def z826 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x8150ee0001f7c000 0xa0543b80007df000

def z827 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf718f86783cff 0x7bafdc63e19e0f3f

def z828 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x2e07018786003c3e 0x0b81c061e1800f0f

def z829 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdfffc1f807c43fc3 0xf7fff07e01f10ff0

def z830 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3fd8effff8000000 0x0ff63bfffe000000

def z831 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xfe7fc1f8ffc03fc2 0xff9ff07e3ff00ff0

def z832 : W := mkw 0x286134b6e2ad271a 0xca184d2db8ab49c6 0x19679df0e78f0f0c 0xc659e77c39e3c3c3

def z833 : W := mkw 0x833000112ffff376 0x60cc00044bfffcdd 0xc004000007fff3ff 0xf001000001fffcff

def z834 : W := mkw 0x8010000028044154 0x200400000a011055 0x7a6c5208f848c3fe 0xde9b14823e1230ff

def z835 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x3ffbffffffcfc000 0xcffefffffff3f000

def z836 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8ac77f9b7333f 0xbdf62b1dfe6dcccf

def z837 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0x1e2701f806003fc2 0x4789c07e01800ff0

def z838 : W := mkw 0x1c000feed0000000 0x070003fbb4000000 0x3f000ffff8000000 0x0fc003fffe000000

def z839 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8ee7f79b73333 0xbdf63b9fde6dcccc

def z840 : W := mkw 0x0040008580101428 0x801000216004050a 0xae17018786003c3e 0x2b85c061e1800f0f

def z841 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x2ea7318786383c3f 0x4ba9cc61e18e0f0f

def z842 : W := mkw 0x8010000028044154 0x200400000a011055 0x59645208f84cc3ff 0xd65914823e1330ff

def z843 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xdfffff8807ffffc3 0xf7ffffe201fffff0

def z844 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0x00040000000033fe 0x0001000000000cff

def z845 : W := mkw 0x9292c1582dc46bd5 0x24a4b0560b711af5 0xa59393f0ff8cfc3d 0x2964e4fc3fe33f0f

def z846 : W := mkw 0x31813b5802aaaa83 0x0c604ed600aaaaa0 0x1f843ff8003fffc3 0x07e10ffe000ffff0

def z847 : W := mkw 0x3c0135eed0000000 0x0f004d7bb4000000 0x3e1321fff8000000 0x0f84c87ffe000000

def z848 : W := mkw 0x0c000e2250000000 0x0300038894000000 0x37d8ae7778000000 0x0df62b9dde000000

def z849 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xfeffb1f786383c3f 0x7fbfec7de18e0f0f

def z850 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0xde7f81f807803fc2 0xf79fe07e01e00ff0

def z851 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdf7fc3f807c4ffc2 0xf7dff0fe01f13ff0

def z852 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7dcac7761b733ff 0xbdf72b1dd86dccff

def z853 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xcc37318786383c3f 0x730dcc61e18e0f0f

def z854 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdffffff807ffffc3 0xf7fffffe01fffff0

def z855 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xe1fbfe0787ffc001 0xf87eff81e1fff000

def z856 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc0bbbc0007ffc001 0xf02eef0001fff000

def z857 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xffff3187e6383c3f 0x7fffcc61f98e0f0f

def z858 : W := mkw 0xb713fbcc9f6ac046 0x2dc4fef327dab011 0x082753889e48c0cc 0x4209d4e227923033

def z859 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1f8fe0001ffc001 0xf07e3f80007ff000

def z860 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x841781f007803fc2 0x2105e07c01e00ff0

def z861 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde3f81f807803fc2 0x778fe07e01e00ff0

def z862 : W := mkw 0xa333fa112ffff376 0x68ccfe844bfffcdd 0xc1fffe0007fff3ff 0xf07fff8001fffcff

def z863 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xe1fbfe0087ffc03d 0xf87eff8021fff00f

def z864 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffffedff67f73ff3 0xfffffb7fd9fdcffc

def z865 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfff8bc77e1b73333 0xbffe2f1df86dcccc

def z866 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xe7fbfe0707ffc001 0xf9feff81c1fff000

def z867 : W := mkw 0x004000010238142a 0x80100000408e050a 0xeebf218706383c3f 0x7bafc861c18e0f0f

def z868 : W := mkw 0x2d013ea6d22a8002 0x0b404fa9b48aa000 0xf7d8be77f9bfc001 0xbdf62f9dfe6ff000

def z869 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc010ac0007ffc001 0xf0042b0001fff000

def z870 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x7fe853fff84cc001 0xdffa14fffe133000

def z871 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x36000077f800333e 0x0d80001dfe000ccf

def z872 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3e7bd3fff8000000 0x0f9ef4fffe000000

def z873 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x25fbfff7f8000000 0x097efffdfe000000

def z874 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0xefffff8787ffcc0d 0xfbffffe1e1fff303

def z875 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1fffe0007ffc3c3 0xf07fff8001fff0f0

def z876 : W := mkw 0x1e02c5eed5400000 0x0780b17bb5500000 0xfe7bc1ffffc00000 0xff9ef07ffff00000

def z877 : W := mkw 0x1c02c5eed0000000 0x0700b17bb4000000 0x3ffbd3fff8000000 0x0ffef4fffe000000

def z878 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x81fbfe0007f7c000 0xa07eff8001fdf000

def z879 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf1d8ac7761b70331 0xbc762b1dd86dc0cc

def z880 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xd758ac7761b73302 0xb5d62b1dd86dccc0

def z881 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0xc000000001bff33f 0xb0000000006ffccf

def z882 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x36040077600033fe 0x0d81001dd8000cff

def z883 : W := mkw 0x1c02c5eed0000000 0x0700b17bb4000000 0x3e2341fff8000000 0x0f88d07ffe000000

def z884 : W := mkw 0x3c0135eed0000000 0x0f004d7bb4000000 0x3ffbbdfff8000000 0x0ffeef7ffe000000

def z885 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x3fe87ffff8000000 0x0ffa1ffffe000000

def z886 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x2ebf318786083c3e 0x4bafcc61e1820f0f

def z887 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1fffe0007ffc03f 0xf07fff8001fff00f

def z888 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc618ac7701b33002 0x31862b1dc06ccc00

def z889 : W := mkw 0x3783fbcc976a8883 0x0de0fef325daa220 0x082753889e48ccc0 0x4209d4e227923330

def z890 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xffdcee7ff9f7f3ff 0xbff73b9ffe7dfcff

def z891 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ac0001ffc001 0xf0762b00007ff000

def z892 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xbffbffffffbfc001 0x2ffeffffffeff000

def z893 : W := mkw 0x24413a859238142a 0x89104ea1648e050a 0xeebf33879e383c3f 0x7bafcce1e78e0f0f

def z894 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc9fffe0087ffc00d 0xf27fff8021fff003

def z895 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x9410ac7761b33300 0x25042b1dd86cccc0

def z896 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x31fbfe7ff8000000 0x0c7eff9ffe000000

def z897 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e9821fff8000000 0x0fa6087ffe000000

def z898 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc1408c0007ffc001 0xf050230001fff000

def z899 : W := mkw 0x2803fe2240000000 0x0a00ff8890000000 0x3ffbfe7ff8000000 0x0ffeff9ffe000000

def z900 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3000007ff8000000 0x0c00001ffe000000

def z901 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x3e2353fffe48c000 0x4f88d4ffff923000

def z902 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3f408dfff8000000 0x0fd0237ffe000000

def z903 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb7d8ac7761b73031 0x2df62b1dd86dcc0c

def z904 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xa610ac7701b33032 0x29842b1dc06ccc0c

def z905 : W := mkw 0x2703fa84976a8002 0x09c0fea125daa000 0xc1fbfe009fffc001 0xf07eff8027fff000

def z906 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0xc1d8ee0007ffc001 0xf0763b8001fff000

def z907 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xee3f218786303c3e 0x7b8fc861e18c0f0f

def z908 : W := mkw 0x0342ca8585529428 0x80d0b2a16154a50a 0x2f44cf8781c7fc3e 0x8bd133e1e071ff0f

def z909 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0xc0008c0007ffc001 0xf000230001fff000

def z910 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xffff738ffe7cfc3f 0xffffdce3ff9f3f0f

def z911 : W := mkw 0x3703fb48176a8002 0x0dc0fed205daa000 0xc1fbfe081fffc001 0xf07eff8207fff000

def z912 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0xc1fbff8007ffcc01 0xf07effe001fff300

def z913 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffffffff8003c02 0x0ffffffffe000f00

def z914 : W := mkw 0x2e813eb6d5c02a81 0x0ba04fadb5700aa0 0xe1843e07ffc03fc2 0xf8610f81fff00ff0

def z915 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1e67c1f807c03fc2 0xc799f07e01f00ff0

def z916 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8173fe0007ffc000 0xe05cff8001fff000

def z917 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0xc1fbfe0001ffc001 0xf07eff80007ff000

def z918 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xffffffffffffc03f 0xfffffffffffff00f

def z919 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x1e0701f806003fc2 0x0781c07e01800ff0

def z920 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x01fbfe0001ffc001 0x807eff80007ff000

def z921 : W := mkw 0x1280015805c02a81 0x04a0005601700aa0 0xde3f01f807c03fc2 0xf78fc07e01f00ff0

def z922 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcbc7ff9bf33ff 0xffff2f1ffe6fccff

def z923 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x5e6f41f806403fc2 0xd79bd07e01900ff0

def z924 : W := mkw 0x3d03ffeed22a8002 0x0f40fffbb48aa000 0xfffbfffff9bfc001 0xbffefffffe6ff000

def z925 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x9658ac7701b33000 0x25962b1dc06ccc00

def z926 : W := mkw 0x1c02c5eed0000000 0x0700b17bb4000000 0x3ffbedfff8000000 0x0ffefb7ffe000000

def z927 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7f8bc7761bf3333 0xfdfe2f1dd86fcccc

def z928 : W := mkw 0x3743fbcc976a840a 0x8dd0fef325daa102 0xc9ffff889fffcc0d 0xf27fffe227fff303

def z929 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf3187867cfc3f 0xfbafcc61e19f3f0f

def z930 : W := mkw 0x2001300002280002 0x08004c00008a0000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z931 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3f4043fff8000000 0x0fd010fffe000000

def z932 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z933 : W := mkw 0x0800042240000000 0x0200010890000000 0x3fe8527ff8000000 0x0ffa149ffe000000

def z934 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x8510ac7761b73000 0x21442b1dd86dcc00

def z935 : W := mkw 0x8010000028044154 0x200400000a011055 0xfbec5208fe4cffff 0xfefb14823f933fff

def z936 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb5d0ac7761b73331 0xad742b1dd86dcccc

def z937 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xbffbfffffff7c000 0xaffefffffffdf000

def z938 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8013ac0007bfc001 0x2004eb0001eff000

def z939 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8ac7761fff333 0xfdf62b1dd87ffccc

def z940 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x3e0013fff8000000 0x0f8004fffe000000

def z941 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x25803ff7f8000000 0x09600ffdfe000000

def z942 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x0140ee0001f7c000 0x80503b80007df000

def z943 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xfeff718f86383c3f 0x7fbfdc63e18e0f0f

def z944 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdfffedf807c03fc2 0xf7fffb7e01f00ff0

def z945 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xffffffffffffffff 0xffffffffffffffff

def z946 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x7becfe7ff9ffc3ff 0xdefb3f9ffe7ff0ff

def z947 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x9450ac7701b33300 0xa5142b1dc06cccc0

def z948 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc193be0007ffc001 0xf064ef8001fff000

def z949 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7dcac7761f733f3 0xfdf72b1dd87dccfc

def z950 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xe1fbfe00ffffc001 0xf87eff803ffff000

def z951 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xa698ac7701b33000 0x29a62b1dc06ccc00

def z952 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3ea811fff8000000 0x0faa047ffe000000

def z953 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0x7beb5388fe4cc001 0xdefad4e23f933000

def z954 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e0401fff80003c2 0x0f81007ffe0000f0

def z955 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xc4bf318706383c3f 0x712fcc61c18e0f0f

def z956 : W := mkw 0x3f03ffeed5428000 0x0fc0fffbb550a000 0x3ffbfffff840c000 0x0ffefffffe103000

def z957 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcfe7ff9bf333f 0xffff3f9ffe6fcccf

def z958 : W := mkw 0x3c03ff6a50000000 0x0f00ffda94000000 0x37fbfe7f78000000 0x0dfeff9fde000000

def z959 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xdbfbfe0807ffc001 0xf6feff8201fff000

def z960 : W := mkw 0x0820043260852310 0x4208010c982148c4 0xf7d8ac7761b70301 0xbdf62b1dd86dc0c0

def z961 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xd3fbfe0007ffc303 0xf4feff8001fff0c0

def z962 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xffffffffffffc3c3 0xfffffffffffff0f0

def z963 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xffffd3f8ffc83fff 0xfffff4fe3ff20fff

def z964 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc17bee0007f7c000 0xf05efb8001fdf000

def z965 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe8a7318786383c3f 0x7a29cc61e18e0f0f

def z966 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc033fe0007ffc001 0xf00cff8001fff000

def z967 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9e57c1f807c03fc2 0xa795f07e01f00ff0

def z968 : W := mkw 0x1382cb5805c2aa81 0x04e0b2d60170aaa0 0xdfffeff807f7ffc3 0xf7fffbfe01fdfff0

def z969 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x31803e7ff8000000 0x0c600f9ffe000000

def z970 : W := mkw 0x0800043240802200 0x0200010c90200880 0xf7d8ac7761b73303 0xbdf62b1dd86dccc0

def z971 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3fc801fff8000000 0x0ff2007ffe000000

def z972 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0xfffffffffe383c03 0x7fffffffff8e0f00

def z973 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0x0003018006000000 0x0000c06001800000

def z974 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xf7d8ac7761b73001 0xbdf62b1dd86dcc00

def z975 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffbfffff8003002 0x3ffefffffe000c00

def z976 : W := mkw 0x1082c15800802a81 0x0420b05600200aa0 0xde7fc1f806003fc2 0x779ff07e01800ff0

def z977 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xbff8fe7ff9b33000 0x2ffe3f9ffe6ccc00

def z978 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xdffffff807fffc03 0xf7fffffe01ffff00

def z979 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffbfffff8300001 0x3ffefffffe0c0000

def z980 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x8550ac7701b73000 0xa1542b1dc06dcc00

def z981 : W := mkw 0x0860043360953738 0xc218010cd8254dce 0xf7dcac7761b73f3f 0xbdf72b1dd86dcfcf

def z982 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffbfffff8000033 0x1ffefffffe00000c

def z983 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0xc1fcfe0001fff3ff 0xf07f3f80007ffcff

def z984 : W := mkw 0x8010000028044154 0x200400000a011055 0x7ffcd278f84cc3ff 0xdfff349e3e1330ff

def z985 : W := mkw 0x2c03fea6d0000000 0x0b00ffa9b4000000 0x37fbfe77f8000000 0x0dfeff9dfe000000

def z986 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xce3f218706383c3f 0x738fc861c18e0f0f

def z987 : W := mkw 0x3743fbcc976a840a 0x8dd0fef325daa102 0x082753889e48cc0c 0x4209d4e227923303

def z988 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7f8fe7f79fff3f3 0xfdfe3f9fde7ffcfc

def z989 : W := mkw 0x0800042240000000 0x0200010890000000 0x37d8ee7f78000000 0x0df63b9fde000000

def z990 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x240001f7f8000000 0x0900007dfe000000

def z991 : W := mkw 0x2103fa00022a8002 0x0840fe80008aa000 0xc1fbfe0001bfc001 0xb07eff80006ff000

def z992 : W := mkw 0x01000a0000028000 0x004002800000a000 0xc1d8ae0001b7c001 0xb0762b80006df000

def z993 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffffffffe083c3f 0x7fffffffff820f0f

def z994 : W := mkw 0x0c0004a6d0000000 0x03000129b4000000 0x36000077f8000000 0x0d80001dfe000000

def z995 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb790ac7761b73333 0x2de42b1dd86dcccc

def z996 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffffffff84000c0 0x4ffffffffe100030

def z997 : W := mkw 0x3f83ffeed76a8883 0x0fe0fffbb5daa220 0xffffffffffffccc1 0xfffffffffffff330

def z998 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0x01c0be0001bfc001 0x80702f80006ff000

def z999 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3f7bcffff8000000 0x0fdef3fffe000000

def z1000 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xee17218786383c3f 0x7b85c861e18e0f0f

def z1001 : W := mkw 0x8010000028044154 0x200400000a011055 0x39e45208f84cc3fd 0xce7914823e1330ff

def z1002 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9c77c1f807c03fc0 0xe71df07e01f00ff0

def z1003 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0xdffffff807ffccc1 0xf7fffffe01fff330

def z1004 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0xbffbfffffe300000 0x2ffeffffff8c0000

def z1005 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffbfffffe78c001 0x7ffeffffff9e3000

def z1006 : W := mkw 0x3c0135eed0000000 0x0f004d7bb4000000 0x3ffb73fff8000000 0x0ffedcfffe000000

def z1007 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x37d8ac7761b70331 0x8df62b1dd86dc0cc

def z1008 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x9610ac7701b33302 0x25842b1dc06cccc0

def z1009 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x0180be0001bfc001 0x00602f80006ff000

def z1010 : W := mkw 0x887004b7e895777c 0xe21c012dfa255ddf 0x3e0401fff8003ffe 0x0f81007ffe000fff

def z1011 : W := mkw 0x1e82c5eed5400881 0x07a0b17bb5500220 0x3e2741fffe400cc0 0x4f89d07fff900330

def z1012 : W := mkw 0x1c42cf6b5238142a 0x8710b3dad48e050a 0xd144ce787e383c3f 0x7451339e1f8e0f0f

def z1013 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xb610ac7761b33000 0x2d842b1dd86ccc00

def z1014 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0x81803e0007bfc001 0x20600f8001eff000

def z1015 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x01e3fe0007ffc001 0xc078ff8001fff000

def z1016 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0xc0002c0007ffc001 0xf0000b0001fff000

def z1017 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x6eaf118786083c3f 0x5babc461e1820f0f

def z1018 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7dcac7767b73f33 0xfdf72b1dd9edcfcc

def z1019 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7f8ec7761f73333 0xfdfe3b1dd87dcccc

def z1020 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x3ffbefff78000000 0x0ffefbffde000000

def z1021 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0xc1f8fe0001ffc001 0xf07e3f80007ff000

def z1022 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0xc1fbbe0007bfc001 0xf07eef8001eff000

def z1023 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff848c000 0x4ffefffffe123000

def z1024 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xbe13adffffb30000 0x2f84eb7fffecc000

def z1025 : W := mkw 0x3e83ffeed5400881 0x0fa0fffbb5500220 0x3ffbfffff84000c0 0x0ffefffffe100030

def z1026 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xc9fbff8087ffc001 0xf27effe021fff000

def z1027 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1bbbe0007bfc001 0x706eef8001eff000

def z1028 : W := mkw 0x8010000028044154 0x200400000a011055 0x7becde08f9cfc3ff 0xdefb37823e73f0ff

def z1029 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfff8fe7ff9fff333 0xfffe3f9ffe7ffccc

def z1030 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff8370001 0x0ffefffffe0dc000

def z1031 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc9ffff8007ffcc01 0xf27fffe001fff300

def z1032 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9e7bc1f807c03fc0 0xa79ef07e01f00ff0

def z1033 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc410ac7701b73001 0xb1042b1dc06dcc00

def z1034 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffffffffe403fc2 0xffffffffff900ff0

def z1035 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffffffffffffc03 0xffffffffffffff00

def z1036 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x7eac11fff808003f 0x5fab047ffe02000f

def z1037 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xee9f218786303c3f 0x3ba7c861e18c0f0f

def z1038 : W := mkw 0x1080015800802a81 0x0420005600200aa0 0xde7f41f806403fc2 0xf79fd07e01900ff0

def z1039 : W := mkw 0x8010000028044154 0x200400000a011055 0xfbfcd208f9ccc3ff 0xfeff34823e7330ff

def z1040 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x3fd8bffff8000000 0x0ff62ffffe000000

def z1041 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0x3ffbfffff8380001 0x0ffefffffe0e0000

def z1042 : W := mkw 0x3e83ffeed5400881 0x0fa0fffbb5500220 0xfffffffffe403cc2 0x7fffffffff900f30

def z1043 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x9550ee7f79f7f3c0 0xa5543b9fde7dfcf0

def z1044 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xcffbff8007ffc001 0xf3feffe001fff000

def z1045 : W := mkw 0x3c013feed0000000 0x0f004ffbb4000000 0x3fbb3ffff8000000 0x0feecffffe000000

def z1046 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x37803e77f8000000 0x0de00f9dfe000000

def z1047 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde3f41f806403fc2 0x778fd07e01900ff0

def z1048 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x3ffbfffffe7fc001 0x4ffeffffff9ff000

def z1049 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8bc77e1bf333f 0xbdf62f1df86fcccf

def z1050 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc458ac7701b33000 0xb1162b1dc06ccc00

def z1051 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e5881fff8000000 0x0f96207ffe000000

def z1052 : W := mkw 0x8010000028044154 0x200400000a011055 0x69a45208f84cc3ff 0xda6914823e1330ff

def z1053 : W := mkw 0x0800042240000000 0x0200010890000000 0x8410ac7701b30000 0x21042b1dc06cc000

def z1054 : W := mkw 0x01000000022a8002 0x00400000008aa000 0xc1d8ac0001bfc001 0xb0762b00006ff000

def z1055 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fc1f807ccffc3 0xf79ff07e01f33ff0

def z1056 : W := mkw 0x3c43ffeed228040a 0x8f10fffbb48a0102 0x3ffbfffffe000c00 0x0ffeffffff800300

def z1057 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x1140ac7761b70300 0x84502b1dd86dc0c0

def z1058 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x941381f807803fc0 0x2504e07e01e00ff0

def z1059 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8ac7761bff33f 0xbdf62b1dd86ffccf

def z1060 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0xc1fbfe0087ffc00d 0xf07eff8021fff003

def z1061 : W := mkw 0x21413a85823a942a 0x88504ea1608ea50a 0xeebf33878638fc3f 0x7bafcce1e18e3f0f

def z1062 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x8410ac7701b73300 0xa1042b1dc06dccc0

def z1063 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf318787bf3c3f 0xfbafcc61e1efcf0f

def z1064 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeeffb18787b83c3f 0xfbbfec61e1ee0f0f

def z1065 : W := mkw 0x2343fa00076a840a 0x88d0fe8001daa102 0xc1fffe0007ffcc0d 0xf07fff8001fff303

def z1066 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff808003d 0x0ffefffffe02000f

def z1067 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xbe14ac7ff9b333fe 0x2f852b1ffe6cccff

def z1068 : W := mkw 0x8010000028044154 0x200400000a011055 0x71c45208f84cc3ff 0xdc7114823e1330ff

def z1069 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e0401fff8003c02 0x0f81007ffe000f00

def z1070 : W := mkw 0x8010000028044154 0x200400000a011055 0x71e85208f84cc3fd 0xdc7a14823e1330ff

def z1071 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3e0301fff8000000 0x0f80c07ffe000000

def z1072 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdfffd3f807c03fc2 0xf7fff4fe01f00ff0

def z1073 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8be77f9b73333 0xbdf62f9dfe6dcccc

def z1074 : W := mkw 0x8010000028044154 0x200400000a011055 0x3ba45208f84cc3ff 0x4ee914823e1330ff

def z1075 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xfe7fc1f887c03ffe 0xff9ff07e21f00fff

def z1076 : W := mkw 0x1002c14800000000 0x0400b05200000000 0xde7fc1f806403fc2 0xf79ff07e01900ff0

def z1077 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xf7d8ac7761b33033 0x3df62b1dd86ccc0c

def z1078 : W := mkw 0x8010000028044154 0x200400000a011055 0xfbec5208f9ffc3ff 0xfefb14823e7ff0ff

def z1079 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3ff8fffff8000000 0x0ffe3ffffe000000

def z1080 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc5fbff8007fffc01 0xf17effe001ffff00

def z1081 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xfffbfffffe000000 0x7ffeffffff800000

def z1082 : W := mkw 0x1382cb5805c2aa81 0x04e0b2d60170aaa0 0xde7fcdf807c33fc2 0xf79ff37e01f0cff0

def z1083 : W := mkw 0x0000001100903220 0x0000000440240c88 0xf7d8ac7701b73333 0xbdf62b1dc06dcccc

def z1084 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8be0001bfc001 0xb0762f80006ff000

def z1085 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0x8140ce0007f7c000 0xa050338001fdf000

def z1086 : W := mkw 0x1f02cf6a55428000 0x07c0b3da9550a000 0xf7d8ee7f79f7c001 0xbdf63b9fde7df000

def z1087 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8fe7ff9fff3ff 0xbdf63f9ffe7ffcff

def z1088 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcfe7ff9b733ff 0xbfff3f9ffe6dccff

def z1089 : W := mkw 0x8810042268044154 0x220401089a011055 0xfffcfe7ff9ffc3ff 0xffff3f9ffe7ff0ff

def z1090 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3fc0fffff8000000 0x0ff03ffffe000000

def z1091 : W := mkw 0x2001308480000000 0x08004c2120000000 0xeebf318786083c3f 0x7bafcc61e1820f0f

def z1092 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3fa37ffff8000000 0x0fe8dffffe000000

def z1093 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7f8fe77f9fff33f 0xfdfe3f9dfe7ffccf

def z1094 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8013ac0007f7c000 0xa004eb0001fdf000

def z1095 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xfffbff8fffffc001 0xfffeffe3fffff000

def z1096 : W := mkw 0x98b0057b68957bf5 0x662c015eda255efd 0x3e0401fff8003ffe 0x0f81007ffe000fff

def z1097 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff84003c0 0x8ffefffffe1000f0

def z1098 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7fcfe7761fff3ff 0xfdff3f9dd87ffcff

def z1099 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb7d8ac7761b33332 0x2df62b1dd86ccccc

def z1100 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9e37c1f807c03fc2 0x678df07e01f00ff0

def z1101 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x3ff8fe7ff8000000 0x0ffe3f9ffe000000

def z1102 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf73878678fc3f 0x7bafdce1e19e3f0f

def z1103 : W := mkw 0x3d03ffeed22a8002 0x0f40fffbb48aa000 0x3ffbfffff8330000 0x0ffefffffe0cc000

def z1104 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xc47fc1f007c03fc2 0xf11ff07c01f00ff0

def z1105 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf738f9e383c3f 0x7bafdce3e78e0f0f

def z1106 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xcc37c1f807c03fc2 0xf30df07e01f00ff0

def z1107 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x3ffbbff7f8000000 0x0ffeeffdfe000000

def z1108 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdeffe1f807f03fc3 0xf7bff87e01fc0ff0

def z1109 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8ac7761f7f3f3 0xbdf62b1dd87dfcfc

def z1110 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefbf3387fe383c3f 0x7befcce1ff8e0f0f

def z1111 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xffffd3f8ffccffc3 0xfffff4fe3ff33ff0

def z1112 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xc9fbff8807ffc001 0xf27effe201fff000

def z1113 : W := mkw 0x0800042240000000 0x0200010890000000 0x37d8be77f8000000 0x0df62f9dfe000000

def z1114 : W := mkw 0x1c4005eed0000408 0x8710017bb4000102 0x3e0401fff8000c0c 0x0f81007ffe000303

def z1115 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcec7ff9f733ff 0xffff3b1ffe7dccff

def z1116 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebfbd8787bb3c3f 0x7bafef61e1eecf0f

def z1117 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x9e7fc1f807803fc2 0x279ff07e01e00ff0

def z1118 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffffffffe000c00 0x4fffffffff800300

def z1119 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffbfffff8080001 0x5ffefffffe020000

def z1120 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xc410ac7701b33302 0xb1042b1dc06cccc0

def z1121 : W := mkw 0x3c0135eed2280002 0x0f004d7bb48a0000 0xfebb31fffe380001 0x7faecc7fff8e0000

def z1122 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xc5d8ac7701b73333 0xb1762b1dc06dcccc

def z1123 : W := mkw 0x8010000028044154 0x200400000a011055 0x7bfcfe08f84cc3ff 0xdeff3f823e1330ff

def z1124 : W := mkw 0x33c3fbcc876a8c8b 0x8cf0fef321daa322 0x082753888648cccc 0x4209d4e221923333

def z1125 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffbfffff8400000 0xdffefffffe100000

def z1126 : W := mkw 0x21413085823a942a 0x88504c21608ea50a 0xeebf3187863ffc3f 0x7bafcc61e18fff0f

def z1127 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x31c0be77f8000000 0x0c702f9dfe000000

def z1128 : W := mkw 0x8010000028044154 0x200400000a011055 0x7a245208f84cc3ff 0xde8914823e1330ff

def z1129 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xe5d8ac7761b73031 0xb9762b1dd86dcc0c

def z1130 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1d8fe0001ffc001 0xb0763f80007ff000

def z1131 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1dbbe0007bfc001 0xb076ef8001eff000

def z1132 : W := mkw 0x807000112abd777e 0xe01c00044aaf5ddf 0xc004000007ffffff 0xf001000001ffffff

def z1133 : W := mkw 0x8010000028044154 0x200400000a011055 0x7fff5388f84cc3ff 0xdfffd4e23e1330ff

def z1134 : W := mkw 0x3303fbcc876a8002 0x0cc0fef321daa000 0xfffbffff87ffc001 0xfffeffffe1fff000

def z1135 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcac7761b73333 0xffff2b1dd86dcccc

def z1136 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xd5fbffff7fffc001 0xf57effffdffff000

def z1137 : W := mkw 0x0040008580101428 0x801000216004050a 0xeebf218786303c3f 0x7bafc861e18c0f0f

def z1138 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeeff718786783c3f 0xfbbfdc61e19e0f0f

def z1139 : W := mkw 0x82d000112ffc7fff 0xa0b400044bff1fff 0xc004000007fcffff 0xf001000001ff3fff

def z1140 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xfebf318f86383fff 0x7fafcc63e18e0fff

def z1141 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0x3ffbfffffe080000 0x4ffeffffff820000

def z1142 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0xbffbffffff800000 0x2ffeffffffe00000

def z1143 : W := mkw 0x82b000112dd57bf5 0x60ac00044b755efd 0xc004000007ffffff 0xf001000001ffffff

def z1144 : W := mkw 0x3e83ffeed5400881 0x0fa0fffbb5500220 0x3ffbfffffe000c00 0x0ffeffffff800300

def z1145 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe497318786383c3f 0x7925cc61e18e0f0f

def z1146 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fd3f89fc03fc2 0xf79ff4fe27f00ff0

def z1147 : W := mkw 0x3f43ffeed76a840a 0x8fd0fffbb5daa102 0xffffffffffffcc0d 0xfffffffffffff303

def z1148 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffdcadf761b73f33 0xbff72b7dd86dcfcc

def z1149 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf698ac7761b33333 0x3da62b1dd86ccccc

def z1150 : W := mkw 0x1c02c5eed0000000 0x0700b17bb4000000 0x3e1381fff8000000 0x0f84e07ffe000000

def z1151 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8ee7761f7f333 0xbdf63b9dd87dfccc

def z1152 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0xc1d8be0007ffc001 0xf0762f8001fff000

def z1153 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ee0001f7c001 0xb0763b80007df000

def z1154 : W := mkw 0x204130858238142a 0x88104c21608e050a 0x8417218706303c3e 0x2105c861c18c0f0f

def z1155 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e3b01fff8000000 0x0f8ec07ffe000000

def z1156 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xacb7318786383c3d 0x6b2dcc61e18e0f0f

def z1157 : W := mkw 0x0040008580101428 0x801000216004050a 0xeebf118786083c3f 0x7bafc461e1820f0f

def z1158 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xdffffff807ffc3c3 0xf7fffffe01fff0f0

def z1159 : W := mkw 0x0000001000802200 0x0000000400200880 0xde7fc1f807c03fc2 0xf79ff07e01f00ff0

def z1160 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0xc000000001f7f3f3 0xb0000000007dfcfc

def z1161 : W := mkw 0x8010000028044154 0x200400000a011055 0x7bec7e08f87fc3ff 0xdefb1f823e1ff0ff

def z1162 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8be7761bff333 0xbdf62f9dd86ffccc

def z1163 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0x002353800648c000 0x4008d4e001923000

def z1164 : W := mkw 0x8010000028044154 0x200400000a011055 0x3b645208f84cc3fe 0xced914823e1330ff

def z1165 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0xbffbfffff9b30000 0x2ffefffffe6cc000

def z1166 : W := mkw 0x0c0004a6d0000000 0x03000129b4000000 0x37d8ac77f8000000 0x0df62b1dfe000000

def z1167 : W := mkw 0x03000a00076a8002 0x00c0028001daa000 0xc1000e0007ffc001 0xf040038001fff000

def z1168 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0x082353889e000000 0x0208d4e227800000

def z1169 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc163de0007ffc001 0xf058f78001fff000

def z1170 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0xcfffff8807fffcc3 0xf3ffffe201ffff30

def z1171 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x3740ce7f78000000 0x0dd0339fde000000

def z1172 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc9fbfe089fffc001 0xf27eff8227fff000

def z1173 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xfeffd1f887c03fc2 0xffbff47e21f00ff0

def z1174 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x39e3fffff8000000 0x0e78fffffe000000

def z1175 : W := mkw 0x8010000028044154 0x200400000a011055 0xfbfc7208f87cc3ff 0xfeff1c823e1f30ff

def z1176 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xd1fbfe0807ffc3c1 0xf47eff8201fff0f0

def z1177 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe4bb318786383c3d 0x792ecc61e18e0f0f

def z1178 : W := mkw 0x1c00056a50000000 0x0700015a94000000 0x3600007f78000000 0x0d80001fde000000

def z1179 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xe798ac7761b73033 0x39e62b1dd86dcc0c

def z1180 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xd550ac7761b73333 0xb5542b1dd86dcccc

def z1181 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xd1fbfe087fffc001 0xf47eff821ffff000

def z1182 : W := mkw 0x3c03f5eed0000000 0x0f00fd7bb4000000 0x3efbf1fff8000000 0x0fbefc7ffe000000

def z1183 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0x3ffbfffff9c00000 0x8ffefffffe700000

def z1184 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3fdbadfff8000000 0x0ff6eb7ffe000000

def z1185 : W := mkw 0x03000000076a8002 0x00c0000001daa000 0xc1802c0007ffc001 0xf0600b0001fff000

def z1186 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0xc1fbfe0001f7c001 0xb07eff80007df000

def z1187 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xbffbfffffffbc000 0x6ffefffffffef000

def z1188 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xf6d8ac7701b33333 0xbdb62b1dc06ccccc

def z1189 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0xdffbfff89fffc001 0xf7fefffe27fff000

def z1190 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xe590ac7761b73333 0xb9642b1dd86dcccc

def z1191 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xffffd3f887ccffff 0xfffff4fe21f33fff

def z1192 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0x01803e0001ffc001 0x80600f80007ff000

def z1193 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xa590be77f9bff03d 0x29642f9dfe6ffc0f

def z1194 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0xffffffffffc03c02 0xfffffffffff00f00

def z1195 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7dcbe77f9fff3ff 0xfdf72f9dfe7ffcff

def z1196 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x3fe8dffff8000000 0x0ffa37fffe000000

def z1197 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff80cc001 0x0ffefffffe033000

def z1198 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xd5d8ac7761b73301 0xb5762b1dd86dccc0

def z1199 : W := mkw 0x1382cb5805c2aa81 0x04e0b2d60170aaa0 0xdfffdff807cfffc3 0xf7fff7fe01f3fff0

def z1200 : W := mkw 0x1682cb5815c02a81 0x05a0b2d605700aa0 0xde7fc3f81fc03fc2 0xf79ff0fe07f00ff0

def z1201 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7d8ae7779b7f333 0xbdf62b9dde6dfccc

def z1202 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1c0fe0007ffc001 0xf0703f8001fff000

def z1203 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefbf3387863cfc3f 0x7befcce1e18f3f0f

def z1204 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffbfffff844c000 0x8ffefffffe113000

def z1205 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3be8fe7ff8000000 0x0efa3f9ffe000000

def z1206 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0xfffbfffffff70001 0xfffefffffffdc000

def z1207 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0x8190be0001bfc001 0x20642f80006ff000

def z1208 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xfeffe1ff07c03fc2 0xffbff87fc1f00ff0

def z1209 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xe7d8ac7701b73033 0xb9f62b1dc06dcc0c

def z1210 : W := mkw 0x23013a00076a8002 0x08c04e8001daa000 0xc1bb3e0007ffc001 0xf06ecf8001fff000

def z1211 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ebbbdfff8000000 0x0faeef7ffe000000

def z1212 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xfffbfff8ffffc001 0xfffefffe3ffff000

def z1213 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xfeffc1f807c03ff3 0xffbff07e01f00ffc

def z1214 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xffff738ffe783fff 0xffffdce3ff9e0fff

def z1215 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xefffff8087fffc3f 0xfbffffe021ffff0f

def z1216 : W := mkw 0x1f02cfeed5428000 0x07c0b3fbb550a000 0x3f40cffff9c7c000 0x8fd033fffe71f000

def z1217 : W := mkw 0x1802c56a40000000 0x0600b15a90000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z1218 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1140ee7f78000000 0x04503b9fde000000

def z1219 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd457c1f807c03fc2 0xf515f07e01f00ff0

def z1220 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xd7fbfe7007ffc001 0xf5feff9c01fff000

def z1221 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdf7fcdf807c73fc2 0xf7dff37e01f1cff0

def z1222 : W := mkw 0x3e03ffeed7680002 0x0f80fffbb5da0000 0xfffbfffffff80001 0xfffefffffffe0000

def z1223 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xf7dcee7f79fff3ff 0xfdf73b9fde7ffcff

def z1224 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1413adff78000000 0x0504eb7fde000000

def z1225 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x81b3fe0007ffc001 0x606cff8001fff000

def z1226 : W := mkw 0x3d03ffeed22a8002 0x0f40fffbb48aa000 0xfffbfffffe3fc001 0x7ffeffffff8ff000

def z1227 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xfbfffe0887ffc3ff 0xfeffff8221fff0ff

def z1228 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3f93bffff8000000 0x0fe4effffe000000

def z1229 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7f8fe7761b73333 0xbdfe3f9dd86dcccc

def z1230 : W := mkw 0x21413a85823a942a 0x88504ea1608ea50a 0xeebf3d87863b3c3f 0x7bafcf61e18ecf0f

def z1231 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3feb53fff8000000 0x0ffad4fffe000000

def z1232 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xffffc1f867c03fc2 0xfffff07e19f00ff0

def z1233 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xc414ac7701fff3ff 0xf1052b1dc07ffcff

def z1234 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xa490ac7701b33031 0x29242b1dc06ccc0c

def z1235 : W := mkw 0x3c0135eed0000000 0x0f004d7bb4000000 0x3e8031fff8000000 0x0fa00c7ffe000000

def z1236 : W := mkw 0x3c83ffeed0000881 0x0f20fffbb4000220 0x3ffffffff8000cc0 0x0ffffffffe000330

def z1237 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e2053fff8000000 0x0f8814fffe000000

def z1238 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fc1f807c83fff 0xf79ff07e01f20fff

def z1239 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7d8ec7f61f733f3 0xbdf63b1fd87dccfc

def z1240 : W := mkw 0x3f03ffeed5428000 0x0fc0fffbb550a000 0x3ffbfffff9830000 0x0ffefffffe60c000

def z1241 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffdcac77e1b7333f 0xbff72b1df86dcccf

def z1242 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1d73fffff8000000 0x075cfffffe000000

def z1243 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1fbee0007f7c001 0xf07efb8001fdf000

def z1244 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd65bc1f807c03fc2 0xb596f07e01f00ff0

def z1245 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x8113ae0007b7c000 0x2044eb8001edf000

def z1246 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0xfffbfffffe7cc001 0xfffeffffff9f3000

def z1247 : W := mkw 0x3703fbcc976a8002 0x0dc0fef325daa000 0xfbfbff88ffffc001 0xfefeffe23ffff000

def z1248 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0xc1fbff8007ffcc01 0xf07effe001fff300

def z1249 : W := mkw 0x3c4135eed228040a 0x8f104d7bb48a0102 0x3e2711fffe080c0c 0x4f89c47fff820303

def z1250 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcfe77e1fff33f 0xffff3f9df87ffccf

def z1251 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffffffff800003e 0x0ffffffffe00000f

def z1252 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x2180be77f8000000 0x08602f9dfe000000

def z1253 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcfc7fe1ff33ff 0xffff3f1ff87fccff

def z1254 : W := mkw 0x3f83ffeed76a8883 0x0fe0fffbb5daa220 0x3ffffffffe48ccc0 0x4fffffffff923330

def z1255 : W := mkw 0x004000858238142a 0x80100021608e050a 0xee3f018786383c3f 0x7b8fc061e18e0f0f

def z1256 : W := mkw 0x1c02cfeed0000000 0x0700b3fbb4000000 0x1540cfff78000000 0x055033ffde000000

def z1257 : W := mkw 0x21013a00022a8002 0x08404e80008aa000 0xc1803e0001bfc001 0xb0600f80006ff000

def z1258 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x3ff8fe7ff8000000 0x0ffe3f9ffe000000

def z1259 : W := mkw 0x8010000028044154 0x200400000a011055 0x7fec5388f84cffff 0xdffb14e23e133fff

def z1260 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fd3f807c8ffc2 0xf79ff4fe01f23ff0

def z1261 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xce3f81f007c03fc2 0xf38fe07c01f00ff0

def z1262 : W := mkw 0x3d03ffeed0028000 0x0f40fffbb400a000 0x3ffbfffff807c000 0x0ffefffffe01f000

def z1263 : W := mkw 0x3d03ffeed22a8002 0x0f40fffbb48aa000 0x7ffbfffff87fc001 0xdffefffffe1ff000

def z1264 : W := mkw 0x9ab2c57a6dc56bd5 0x66acb15e9b715af5 0x1140ce7879c7c3c0 0x8450339e1e71f0f0

def z1265 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1a37e0007ffc001 0xf068df8001fff000

def z1266 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fd1f887c83fce 0xf79ff47e21f20ff3

def z1267 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcfe7ff9f733f3 0xffff3f9ffe7dccfc

def z1268 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfff8fe7ff9bff33f 0xbffe3f9ffe6ffccf

def z1269 : W := mkw 0x3783fbcc976a8883 0x0de0fef325daa220 0xc9ffff889fffccc1 0xf27fffe227fff330

def z1270 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde2741f807c03fc2 0xf789d07e01f00ff0

def z1271 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd867c1f807c03fc2 0xf619f07e01f00ff0

def z1272 : W := mkw 0x3d03ffeed22a8002 0x0f40fffbb48aa000 0x3ffbfffff808c000 0x0ffefffffe023000

def z1273 : W := mkw 0x2343fa84876a840a 0x88d0fea121daa102 0xebffff8087ffcc3f 0xfaffffe021fff30f

def z1274 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd47bc1f807c03fc0 0xf51ef07e01f00ff0

def z1275 : W := mkw 0x3d013feed22a8002 0x0f404ffbb48aa000 0x3f803ffff83fc001 0x0fe00ffffe0ff000

def z1276 : W := mkw 0x0300000005428000 0x00c000000150a000 0xc1d8ac0001f7c001 0xb0762b00007df000

def z1277 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffbffffffbb0001 0x7ffeffffffeec000

def z1278 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0xc17bce0007ffc001 0xf05ef38001fff000

def z1279 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xe698ac7701b73333 0xb9a62b1dc06dcccc

def z1280 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xfffbfffffff30000 0xfffefffffffcc000

def z1281 : W := mkw 0x3f03ffeed5428000 0x0fc0fffbb550a000 0xfffbfffff9f7c001 0xbffefffffe7df000

def z1282 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x1f7befff78000000 0x07defbffde000000

def z1283 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffffffff80003c2 0x0ffffffffe0000f0

def z1284 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdf7fc3f87fc03fc2 0xf7dff0fe1ff00ff0

def z1285 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x3e0401fff800003e 0x0f81007ffe00000f

def z1286 : W := mkw 0x3f03ff6a576a8002 0x0fc0ffda95daa000 0xf7fbfe7f7fffc001 0xfdfeff9fdffff000

def z1287 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb750ac7761b73332 0xadd42b1dd86dcccc

def z1288 : W := mkw 0x3303fb48076a8002 0x0cc0fed201daa000 0xd1fbfe7807ffc001 0xf47eff9e01fff000

def z1289 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xd7d8ac7701b73303 0xb5f62b1dc06dccc0

def z1290 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xefffff8787fffc03 0xfbffffe1e1ffff00

def z1291 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7dcac7761bf333f 0xfdf72b1dd86fcccf

def z1292 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xae37318786383c3e 0x6b8dcc61e18e0f0f

def z1293 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x7ffbfffffe4cc001 0xdffeffffff933000

def z1294 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x8413adf707b33c00 0x2104eb7dc1eccf00

def z1295 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xde7cec7f01f333c2 0xf79f3b1fc07cccf0

def z1296 : W := mkw 0x3c03ffeed2280002 0x0f00fffbb48a0000 0xfffffffffe38003f 0x7fffffffff8e000f

def z1297 : W := mkw 0x0302c000076a8002 0x00c0b00001daa000 0xc1fbec0007ffc001 0xf07efb0001fff000

def z1298 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1dbac0007ffc001 0xf076eb0001fff000

def z1299 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xe3fbfe0007ffc033 0xf8feff8001fff00c

def z1300 : W := mkw 0x2c013ea6d0000000 0x0b004fa9b4000000 0x2590be77f8000000 0x09642f9dfe000000

def z1301 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xfbfffe08ffffc3c3 0xfeffff823ffff0f0

def z1302 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffbfffff8040001 0x9ffefffffe010000

def z1303 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc140ce0001f7c001 0xb0503380007df000

def z1304 : W := mkw 0x1c02cf6a50000000 0x0700b3da94000000 0x1550ee7f78000000 0x05543b9fde000000

def z1305 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf1c0ac7761b73333 0xbc702b1dd86dcccc

def z1306 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xe5fbfff7ffffc001 0xf97efffdfffff000

def z1307 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x8410ac7701b73031 0x21042b1dc06dcc0c

def z1308 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xebfbfe0087ffc001 0xfafeff8021fff000

def z1309 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7fbac7767b73333 0xfdfeeb1dd9edcccc

def z1310 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0xfe3f01fffe003c02 0x7f8fc07fff800f00

def z1311 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffffffff8000002 0x5ffffffffe000000

def z1312 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcec7f61fff3ff 0xffff3b1fd87ffcff

def z1313 : W := mkw 0x20413a858238142a 0x88104ea1608e050a 0xefbf3f8786383c3f 0x7befcfe1e18e0f0f

def z1314 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xfebf318ffe383c3f 0x7fafcc63ff8e0f0f

def z1315 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ebb73fff8000000 0x0faedcfffe000000

def z1316 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xeebf318786783fff 0xfbafcc61e19e0fff

def z1317 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc07bec0007ffc001 0xf01efb0001fff000

def z1318 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xfbfffe08ffffc03f 0xfeffff823ffff00f

def z1319 : W := mkw 0x2f03fea6d76a8002 0x0bc0ffa9b5daa000 0xf7fbfe77ffffc001 0xfdfeff9dfffff000

def z1320 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xf3fbfe0067ffc001 0xfcfeff8019fff000

def z1321 : W := mkw 0x1282cb5805c02a81 0x04a0b2d601700aa0 0xdf7fcff807c03fc2 0xf7dff3fe01f00ff0

def z1322 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3f63dffff8000000 0x0fd8f7fffe000000

def z1323 : W := mkw 0x8010000028044154 0x200400000a011055 0x7bef5388fe4ccfff 0xdefbd4e23f9333ff

def z1324 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xb7d8ac7761b73300 0xadf62b1dd86dccc0

def z1325 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefff3187863c3c3f 0xfbffcc61e18f0f0f

def z1326 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x2fbbbff7f8000000 0x0beeeffdfe000000

def z1327 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x2180ac7761b70031 0x08602b1dd86dc00c

def z1328 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf7dbadf767b73f33 0xbdf6eb7dd9edcfcc

def z1329 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfff8ec7f61b73333 0xbffe3b1fd86dcccc

def z1330 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfff8fe7ff9f7f3f3 0xbffe3f9ffe7dfcfc

def z1331 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0x31c0fe7ff9ffc3fd 0x8c703f9ffe7ff0ff

def z1332 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x81d3fe0007ffc001 0xa074ff8001fff000

def z1333 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xdeffd1f807c83fc3 0xf7bff47e01f20ff0

def z1334 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0xf1fbfe7fffffc001 0xfc7eff9ffffff000

def z1335 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x0513aff778000000 0x0144ebfdde000000

def z1336 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xaebf318786303c3e 0x2bafcc61e18c0f0f

def z1337 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x0000ac7701b30000 0x00002b1dc06cc000

def z1338 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0x7e6c41fff84003c2 0xdf9b107ffe1000f0

def z1339 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xc5fbff8707ffc001 0xf17effe1c1fff000

def z1340 : W := mkw 0x0800042240000000 0x0200010890000000 0xc5d8ac7701b70001 0xb1762b1dc06dc000

def z1341 : W := mkw 0x8030001128957374 0x600c00044a255cdd 0x40040000004cf3ff 0xd001000000133cff

def z1342 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xcbfffe0007ffc003 0xf2ffff8001fff000

def z1343 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x8590ac7701b73001 0x21642b1dc06dcc00

def z1344 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x31c0fe7ff9ffc001 0x8c703f9ffe7ff000

def z1345 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xf610ac7761b73333 0xbd842b1dd86dcccc

def z1346 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xe69f218706383c3f 0x79a7c861c18e0f0f

def z1347 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffffbdf7e7bf3f3f 0xffffef7df9efcfcf

def z1348 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x01c0ee0001f7c001 0x80703b80007df000

def z1349 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xee27118786383c3f 0x7b89c461e18e0f0f

def z1350 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xd658ac7701b73333 0xb5962b1dc06dcccc

def z1351 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xffdcac7f61b733f3 0xbff72b1fd86dccfc

def z1352 : W := mkw 0x1c00056a50000000 0x0700015a94000000 0x37d8ac7f78000000 0x0df62b1fde000000

def z1353 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0x85d8ac7701b33000 0x21762b1dc06ccc00

def z1354 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3e7bedfff8000000 0x0f9efb7ffe000000

def z1355 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0x841381f007c03fc0 0xa104e07c01f00ff0

def z1356 : W := mkw 0x3383fb48076a8883 0x0ce0fed201daa220 0xdbffff8807ffcfc3 0xf6ffffe201fff3f0

def z1357 : W := mkw 0x1382c15805c2aa81 0x04e0b0560170aaa0 0xde7fc1f807c7ffc2 0xf79ff07e01f1fff0

def z1358 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1dbee0007f7c001 0xb076fb8001fdf000

def z1359 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0x73c8ac7761b70333 0x9cf22b1dd86dc0cc

def z1360 : W := mkw 0x0820043360953330 0x4208010cd8254ccc 0xfffcfe7f61fff3f3 0xffff3f9fd87ffcfc

def z1361 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x15fbffff78000000 0x057effffde000000

def z1362 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3f53effff8000000 0x0fd4fbfffe000000

def z1363 : W := mkw 0x1c0005eed0000000 0x0700017bb4000000 0xffd8adfff9b70001 0xbff62b7ffe6dc000

def z1364 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc1fffe0007fffc03 0xf07fff8001ffff00

def z1365 : W := mkw 0x9e92cf7a7dc46bd5 0x27a4b3de9f711af5 0x1140ce7879c4c3c0 0x8450339e1e7130f0

def z1366 : W := mkw 0x1382cb5805c2aa81 0x04e0b2d60170aaa0 0xde7fc3f807c0ffc2 0xf79ff0fe01f03ff0

def z1367 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x41e8fe0001ffc001 0xd07a3f80007ff000

def z1368 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcbc77e1fff3ff 0xffff2f1df87ffcff

def z1369 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde7fc1f807f73fc3 0xf79ff07e01fdcff0

def z1370 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xd65f81f007c03fc2 0xf597e07c01f00ff0

def z1371 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefbf3d87863f3c3f 0x7befcf61e18fcf0f

def z1372 : W := mkw 0x3c43ffeed0000408 0x8f10fffbb4000102 0x3ffffffff8000c0c 0x0ffffffffe000303

def z1373 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde1781f807c03fc2 0xf785e07e01f00ff0

def z1374 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefffbd8786383c3f 0x7bffef61e18e0f0f

def z1375 : W := mkw 0x3f03ffeed76a8002 0x0fc0fffbb5daa000 0x9553efff7ff7c000 0xa554fbffdffdf000

def z1376 : W := mkw 0x8010000028044154 0x200400000a011055 0x7ffc720ff84cc3ff 0xdfff1c83fe1330ff

def z1377 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xeebcbc7781bb303f 0x7baf2f1de06ecc0f

def z1378 : W := mkw 0x0302ca00076a8002 0x00c0b28001daa000 0x0140ce0001ffc001 0x80503380007ff000

def z1379 : W := mkw 0x0820043340913220 0x4208010cd0244c88 0xf7d8ac7761b33302 0xbdf62b1dd86cccc0

def z1380 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x3ffffffff808000c 0x4ffffffffe020003

def z1381 : W := mkw 0x3e03ffeed5400000 0x0f80fffbb5500000 0xfffbffffffccc001 0xfffefffffff33000

def z1382 : W := mkw 0x8010000028044154 0x200400000a011055 0x3bc45208f84cc3ff 0x8ef114823e1330ff

def z1383 : W := mkw 0x8830043368957374 0x620c010cda255cdd 0xfffcbe77f9bff33f 0xffff2f9dfe6ffccf

def z1384 : W := mkw 0x8010000028044154 0x200400000a011055 0x3be85208f84cc3fd 0x8efa14823e1330ff

def z1385 : W := mkw 0x2383fa00076a8883 0x08e0fe8001daa220 0xc1fffe0007ffccc1 0xf07fff8001fff330

def z1386 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x7ffffffff84803ff 0xdffffffffe1200ff

def z1387 : W := mkw 0x2303fa84876a8002 0x08c0fea121daa000 0xefffff8787ffc03f 0xfbffffe1e1fff00f

def z1388 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xee3f118786083c3e 0x7b8fc461e1820f0f

def z1389 : W := mkw 0x1282c15805c02a81 0x04a0b05601700aa0 0xde5f81f807803fc2 0xb797e07e01e00ff0

def z1390 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xffff738f867cffff 0xffffdce3e19f3fff

def z1391 : W := mkw 0x204130858238142a 0x88104c21608e050a 0xefff738786383c3f 0x7bffdce1e18e0f0f

def z1392 : W := mkw 0x3c03ffeed0000000 0x0f00fffbb4000000 0x2413adf7f8000000 0x0904eb7dfe000000

def z1393 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0x81fbfe0007bfc001 0x207eff8001eff000

def z1394 : W := mkw 0x2303fa00076a8002 0x08c0fe8001daa000 0xc153ee0007ffc001 0xf054fb8001fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z7]),(0,[z8,z1,z2,z3,z5,z6,z7]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z11,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z6])],[(0,[z13,z1,z14,z3,z4,z5,z6]),(0,[z15,z1,z16,z2,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z3,z19,z5,z6])],[(0,[z2,z3,z20,z4,z5,z6,z7]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z22,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z5,z6,z25]),(0,[z1,z26,z2,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z28,z6,z29])],[(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z31,z3,z4,z5,z6]),(0,[z32,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z33]),(0,[z34,z1,z2,z3,z4,z27,z6]),(0,[z35,z1,z2,z3,z4,z5,z36]),(0,[z37,z1,z2,z3,z4,z38,z6]),(0,[z39,z1,z2,z3,z19,z5,z6])],[(0,[z1,z2,z3,z4,z40,z5,z6]),(0,[z1,z2,z41,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z15,z43,z1,z2,z3,z5,z6]),(1,[z1,z2,z44,z4,z5,z45]),(0,[z46,z1,z2,z47,z3,z4,z6])],[(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z1,z16,z2,z3,z4,z5,z6]),(1,[z49,z1,z2,z4,z5,z6]),(0,[z1,z2,z50,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z52,z3,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6])],[(0,[z55,z2,z3,z20,z4,z5,z6]),(0,[z56,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z57,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z28,z6])],[(0,[z58,z2,z3,z4,z59,z5,z6]),(0,[z55,z2,z47,z3,z4,z5,z6]),(1,[z1,z2,z60,z4,z5,z6])]],
   [[(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z1,z2,z62,z3,z4,z5,z6]),(0,[z63,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z28,z64,z6]),(0,[z1,z16,z2,z3,z4,z28,z6]),(1,[z1,z2,z3,z4,z65,z6]),(0,[z66,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z67])],[(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z6]),(0,[z1,z2,z3,z70,z4,z5,z6]),(0,[z1,z71,z2,z3,z4,z5,z6])],[(0,[z63,z2,z72,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z73,z5,z6]),(0,[z74,z63,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z6]),(0,[z77,z1,z2,z3,z78,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6]),(1,[z55,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z80,z5,z6]),(0,[z81,z1,z2,z3,z4,z5,z6]),(1,[z82,z2,z3,z4,z5,z6])],[(0,[z1,z2,z83,z3,z4,z84,z6]),(0,[z8,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z6,z85,z7]),(0,[z1,z2,z3,z4,z86,z28,z6]),(0,[z18,z1,z2,z3,z4,z5,z25])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z5,z6]),(0,[z1,z2,z3,z4,z28,z88,z6])],[(1,[z1,z2,z3,z4,z89,z6]),(0,[z13,z1,z2,z3,z20,z5,z6]),(0,[z26,z2,z3,z4,z5,z6,z7]),(0,[z1,z90,z2,z3,z4,z5,z6]),(0,[z1,z2,z91,z3,z4,z28,z6])],[(0,[z58,z1,z2,z92,z3,z4,z6]),(0,[z93,z1,z2,z4,z94,z5,z6]),(0,[z93,z1,z2,z47,z3,z4,z6]),(0,[z95,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z96,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z28,z6]),(1,[z1,z2,z3,z4,z98,z99])],[(0,[z100,z1,z2,z3,z4,z5,z6]),(0,[z34,z2,z3,z4,z5,z6,z7]),(0,[z1,z3,z4,z94,z5,z6,z101]),(0,[z1,z2,z23,z4,z5,z6,z102]),(0,[z1,z2,z103,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z104,z5,z6])]],
   [[(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z58,z1,z2,z3,z4,z59,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z109,z6]),(0,[z1,z110,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z47,z3,z4,z6]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z18,z1,z112,z3,z4,z5,z6])],[(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z55,z77,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z114,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z115,z6]),(0,[z1,z2,z3,z19,z4,z5,z6])],[(1,[z1,z2,z3,z4,z116,z6]),(0,[z1,z2,z3,z4,z5,z117,z6]),(0,[z58,z1,z2,z3,z4,z27,z6]),(0,[z43,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z6,z118]),(0,[z119,z1,z2,z3,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z121,z1,z2,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z123,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z124])],[(0,[z1,z2,z4,z86,z125,z5,z6]),(0,[z63,z2,z83,z3,z4,z5,z6]),(1,[z55,z2,z3,z4,z5,z7]),(0,[z1,z2,z126,z3,z4,z5,z6]),(0,[z1,z2,z127,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z128,z5,z6]),(1,[z1,z2,z3,z129,z5,z6]),(0,[z1,z2,z83,z4,z86,z5,z6]),(0,[z18,z77,z1,z2,z3,z5,z6]),(0,[z130,z2,z3,z4,z5,z45,z6]),(0,[z1,z2,z3,z4,z131,z5,z6]),(0,[z1,z2,z3,z19,z4,z28,z6]),(0,[z1,z2,z132,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z133,z5,z6])],[(0,[z134,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z135,z4,z5,z6]),(0,[z2,z3,z4,z5,z36,z6,z7]),(0,[z55,z2,z3,z4,z5,z6,z101]),(0,[z1,z136,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z91,z3,z4,z6])],[(0,[z137,z1,z2,z47,z3,z4,z6]),(0,[z39,z77,z1,z2,z3,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z34,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z13,z39,z1,z2,z3,z5,z6]),(0,[z140,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z141,z4,z5,z6]),(0,[z1,z142,z2,z3,z4,z5,z6])]],
   [[(0,[z137,z2,z72,z3,z4,z5,z6]),(0,[z55,z143,z2,z3,z4,z5,z6]),(0,[z1,z2,z144,z3,z4,z5,z6]),(0,[z134,z1,z2,z3,z4,z28,z6]),(0,[z55,z2,z3,z24,z4,z5,z6]),(0,[z145,z1,z2,z3,z146,z5,z6]),(0,[z1,z26,z3,z4,z5,z27,z6]),(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z28,z6]),(0,[z1,z2,z148,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z149,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z102]),(0,[z2,z3,z4,z150,z5,z28,z6])],[(0,[z2,z72,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z59,z5,z6]),(0,[z140,z134,z1,z2,z3,z4,z6]),(0,[z55,z2,z151,z3,z4,z5,z6]),(0,[z43,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z152,z3,z4,z5,z6]),(0,[z1,z2,z153,z3,z4,z5,z6]),(0,[z1,z154,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z64,z25]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z156,z1,z2,z3,z4,z5,z6])],[(1,[z2,z3,z5,z6,z157,z7]),(0,[z55,z2,z3,z158,z4,z5,z6]),(0,[z1,z2,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z159,z6]),(0,[z160,z1,z2,z3,z4,z5,z6])],[(0,[z161,z1,z2,z47,z3,z4,z6]),(0,[z162,z1,z2,z3,z4,z5,z6])],[(0,[z77,z1,z2,z3,z146,z5,z6]),(0,[z49,z1,z2,z24,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z163,z6]),(0,[z1,z2,z3,z4,z5,z6,z164]),(0,[z165,z1,z2,z3,z4,z5,z6])],[(0,[z74,z143,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z166,z5,z6]),(0,[z58,z2,z3,z4,z5,z6,z7]),(1,[z1,z167,z3,z4,z5,z6]),(0,[z140,z1,z2,z60,z4,z5,z6]),(1,[z1,z2,z3,z168,z5,z6])],[(0,[z13,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z169,z3,z4,z5,z6]),(0,[z58,z1,z2,z3,z4,z109,z6]),(0,[z161,z1,z2,z3,z4,z5,z64]),(0,[z170,z1,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z171,z4,z5,z6]),(1,[z1,z2,z47,z3,z28,z6]),(0,[z162,z1,z2,z3,z4,z28,z6])]],
   [[(0,[z55,z2,z3,z4,z125,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z172]),(0,[z35,z1,z2,z47,z3,z4,z6]),(1,[z37,z1,z2,z92,z4,z6])],[(0,[z173,z1,z2,z3,z4,z5,z6]),(0,[z2,z47,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z6,z174]),(0,[z1,z2,z3,z4,z5,z6,z175]),(0,[z140,z82,z2,z3,z4,z5,z6])],[(0,[z1,z176,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z177]),(1,[z1,z2,z3,z4,z28,z6]),(0,[z178,z2,z3,z4,z5,z28,z6]),(0,[z1,z2,z179,z47,z3,z4,z6])],[(0,[z1,z2,z3,z4,z180,z5,z6]),(0,[z181,z55,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z28,z6,z101]),(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z1,z183,z2,z47,z3,z4,z6]),(0,[z1,z2,z47,z3,z4,z4,z6])],[(0,[z1,z2,z184,z3,z4,z5,z6]),(0,[z2,z3,z24,z4,z5,z6,z7]),(0,[z2,z3,z4,z5,z185,z6,z186])],[(0,[z55,z2,z72,z3,z4,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z6]),(0,[z58,z55,z2,z3,z4,z5,z6]),(0,[z188,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z98,z6]),(0,[z189,z1,z2,z3,z4,z5,z6])],[(0,[z74,z2,z3,z4,z125,z5,z6]),(0,[z13,z134,z2,z3,z4,z5,z6]),(0,[z2,z92,z3,z4,z5,z6,z7]),(0,[z55,z26,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z64]),(0,[z1,z2,z3,z190,z4,z5,z6]),(0,[z1,z2,z191,z3,z4,z5,z6]),(0,[z1,z96,z3,z4,z5,z27,z6])],[(0,[z1,z2,z3,z4,z192,z5,z6]),(1,[z193,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z194])]],
   [[(0,[z2,z3,z4,z98,z5,z6,z7]),(0,[z1,z16,z96,z3,z4,z5,z6]),(1,[z1,z195,z3,z4,z5,z6]),(0,[z196,z2,z3,z4,z5,z185,z6]),(0,[z197,z1,z2,z3,z4,z5,z6])],[(1,[z137,z72,z3,z4,z5,z6]),(0,[z74,z1,z2,z47,z3,z4,z6]),(0,[z134,z1,z2,z92,z3,z4,z6]),(0,[z37,z1,z2,z4,z5,z6,z102]),(0,[z1,z2,z198,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z199,z3,z4,z5,z6])],[(0,[z13,z1,z2,z3,z4,z116,z6]),(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z1,z2,z47,z3,z4,z6,z7]),(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z2,z3,z202,z4,z5,z6]),(0,[z1,z2,z3,z4,z98,z5,z6])],[(0,[z203,z1,z2,z83,z4,z5,z6]),(0,[z134,z1,z2,z3,z4,z59,z6]),(0,[z35,z204,z2,z3,z4,z5,z6])],[(0,[z1,z2,z205,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z206]),(0,[z55,z2,z3,z4,z5,z185,z6]),(0,[z207,z2,z3,z4,z5,z36,z6]),(0,[z37,z1,z2,z92,z4,z5,z6]),(0,[z1,z2,z198,z3,z4,z28,z6]),(0,[z208,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z209,z6]),(0,[z1,z2,z3,z4,z5,z84,z6]),(0,[z134,z1,z2,z3,z4,z27,z6]),(0,[z55,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z4,z5,z6,z211]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z213]),(0,[z1,z2,z3,z4,z98,z28,z6]),(0,[z66,z1,z2,z3,z4,z5,z6])],[(0,[z55,z2,z83,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z214,z6]),(0,[z2,z3,z20,z4,z59,z5,z6]),(0,[z215,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z19,z5,z6]),(1,[z216,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z217])],[(0,[z13,z1,z187,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z218,z5,z6]),(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z28,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z7]),(0,[z1,z96,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z4,z221,z5,z6]),(1,[z39,z1,z2,z47,z3,z6]),(0,[z18,z1,z2,z3,z4,z222,z6])],[(0,[z1,z143,z2,z47,z3,z4,z6]),(0,[z93,z1,z16,z3,z4,z5,z6]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z224,z5,z6]),(1,[z1,z2,z3,z225,z5,z6])],[(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z24,z4,z6])],[(0,[z143,z2,z72,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z7,z29]),(0,[z2,z3,z4,z5,z64,z6,z7]),(0,[z1,z227,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z228]),(0,[z1,z2,z229,z3,z4,z5,z6]),(0,[z1,z2,z230,z3,z4,z5,z6])],[(0,[z203,z2,z3,z4,z125,z5,z6]),(0,[z231,z1,z2,z3,z4,z5,z6]),(0,[z55,z2,z232,z3,z4,z5,z6]),(0,[z55,z96,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z233]),(0,[z43,z1,z2,z3,z4,z28,z6]),(0,[z234,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z235,z6]),(0,[z2,z3,z4,z86,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z236,z6]),(0,[z1,z2,z3,z86,z5,z28,z6]),(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z140,z1,z167,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z168,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z238]),(0,[z1,z2,z3,z4,z239,z5,z6]),(0,[z240,z1,z2,z3,z4,z5,z6])],[(0,[z203,z1,z2,z47,z3,z4,z6]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z6,z25])]],
   [[(1,[z1,z2,z3,z4,z84,z6]),(1,[z77,z2,z3,z20,z5,z6])],[(0,[z93,z1,z3,z4,z94,z5,z6]),(0,[z34,z1,z26,z3,z4,z5,z6]),(0,[z1,z2,z241,z3,z4,z5,z6])],[(0,[z13,z1,z2,z3,z4,z28,z6]),(0,[z134,z1,z2,z3,z4,z109,z6]),(0,[z1,z2,z3,z4,z5,z242,z6]),(0,[z1,z2,z3,z4,z28,z185,z6]),(0,[z2,z3,z4,z5,z99,z6,z243])],[(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z181,z1,z2,z3,z4,z5,z6]),(0,[z106,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z245,z5,z6]),(0,[z1,z2,z3,z4,z94,z5,z6]),(1,[z1,z22,z3,z24,z5,z6]),(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z6])],[(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z2,z83,z3,z4,z5,z6,z7]),(0,[z1,z2,z249,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z250]),(0,[z1,z2,z251,z3,z4,z5,z6]),(0,[z1,z2,z241,z3,z4,z28,z6])],[(0,[z1,z2,z3,z4,z252,z5,z6]),(0,[z2,z3,z4,z5,z28,z6,z7]),(0,[z35,z1,z2,z3,z4,z5,z101]),(0,[z122,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z47,z3,z4,z45,z6]),(1,[z1,z112,z3,z4,z5,z6])],[(0,[z1,z2,z72,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z253]),(0,[z1,z2,z254,z3,z20,z4,z6]),(0,[z2,z3,z4,z5,z6,z7,z25]),(1,[z255,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z94,z28,z6]),(0,[z1,z2,z3,z4,z5,z6,z256]),(0,[z2,z3,z4,z5,z45,z6,z217])],[(0,[z63,z1,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z257]),(0,[z18,z1,z2,z3,z4,z258,z6])]],
   [[(0,[z58,z1,z2,z3,z4,z28,z6]),(1,[z161,z2,z3,z4,z5,z7]),(0,[z93,z1,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z4,z259,z5,z6]),(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z39,z43,z1,z2,z3,z5,z6]),(0,[z1,z2,z92,z3,z4,z28,z6])],[(0,[z1,z2,z3,z4,z5,z6,z250]),(0,[z55,z16,z2,z3,z4,z5,z6]),(0,[z260,z1,z2,z3,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z6,z262])],[(0,[z1,z2,z14,z3,z4,z5,z6]),(0,[z1,z2,z4,z94,z5,z6,z102]),(0,[z1,z2,z3,z4,z263,z5,z6]),(0,[z1,z2,z23,z44,z4,z5,z6]),(0,[z1,z2,z3,z146,z5,z6,z25]),(1,[z1,z26,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z98,z27,z6])],[(0,[z1,z2,z3,z4,z5,z264,z6]),(1,[z58,z2,z3,z4,z59,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z45,z6])],[(0,[z15,z1,z2,z83,z4,z5,z6]),(0,[z13,z2,z3,z4,z59,z5,z6]),(0,[z55,z2,z3,z4,z86,z5,z6]),(0,[z93,z1,z2,z23,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z266,z6]),(0,[z1,z2,z3,z4,z5,z267,z6]),(0,[z268,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z92,z91,z3,z4,z6]),(0,[z1,z2,z269,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z270,z5,z6]),(0,[z1,z2,z3,z4,z5,z271,z6]),(0,[z34,z1,z3,z4,z109,z5,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z273]),(1,[z2,z3,z4,z5,z6,z186])],[(0,[z13,z1,z2,z3,z24,z5,z6]),(0,[z55,z2,z91,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z274,z5,z6]),(0,[z1,z2,z3,z4,z275,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z276])],[(0,[z1,z2,z3,z4,z5,z6,z277]),(0,[z278,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z279]),(0,[z1,z2,z3,z4,z280,z5,z6]),(0,[z1,z2,z3,z4,z281,z5,z6]),(0,[z1,z282,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z283,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z284,z6]),(0,[z18,z1,z2,z47,z3,z4,z6])]],
   [[(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z18,z13,z1,z2,z3,z5,z6]),(0,[z1,z183,z2,z3,z4,z5,z6]),(0,[z1,z2,z151,z3,z86,z5,z6]),(0,[z286,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z5,z185,z6,z25])],[(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z2,z3,z4,z5,z36,z6,z233]),(0,[z1,z2,z3,z4,z5,z287,z6]),(0,[z37,z1,z2,z92,z3,z4,z6]),(0,[z39,z1,z2,z47,z3,z4,z6])],[(0,[z1,z2,z288,z3,z4,z5,z6]),(1,[z2,z3,z4,z28,z6,z7]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z291,z5,z6])],[(0,[z1,z2,z3,z5,z6,z157,z7]),(0,[z122,z1,z2,z3,z4,z292,z6]),(0,[z1,z2,z3,z4,z28,z293,z6]),(0,[z1,z2,z3,z4,z5,z6,z294])],[(0,[z1,z2,z3,z4,z295,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z296]),(0,[z34,z1,z3,z4,z5,z6,z101]),(0,[z297,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z298,z5,z6]),(0,[z1,z2,z3,z299,z4,z5,z6])],[(0,[z1,z2,z300,z3,z4,z5,z6]),(0,[z1,z2,z301,z3,z4,z5,z6]),(0,[z1,z96,z2,z47,z3,z4,z6]),(1,[z1,z2,z3,z4,z302,z6]),(0,[z303,z1,z2,z91,z3,z5,z6]),(1,[z1,z2,z241,z3,z28,z6])],[(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z305,z5,z6]),(0,[z1,z2,z3,z4,z27,z28,z6]),(0,[z1,z2,z3,z4,z306,z5,z6]),(0,[z1,z2,z307,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z86,z5,z6]),(0,[z1,z2,z47,z3,z4,z6,z102]),(0,[z1,z2,z47,z241,z3,z4,z6])],[(1,[z1,z2,z3,z4,z267,z6]),(0,[z1,z2,z3,z24,z4,z267,z6]),(0,[z308,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z2,z23,z3,z4,z5,z6,z7]),(0,[z15,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z302,z5,z6]),(0,[z1,z2,z310,z3,z4,z5,z6])],[(0,[z55,z2,z3,z4,z109,z5,z6]),(0,[z1,z2,z47,z3,z4,z94,z6]),(0,[z1,z2,z3,z4,z311,z5,z6])],[(0,[z1,z2,z312,z3,z4,z5,z6]),(0,[z313,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z314,z5,z6]),(0,[z315,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z6,z316]),(0,[z1,z2,z3,z4,z5,z222,z6])],[(0,[z77,z2,z3,z20,z4,z5,z6]),(0,[z43,z77,z1,z2,z3,z5,z6]),(0,[z317,z1,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z5,z28,z6]),(1,[z318,z2,z3,z4,z5,z6]),(0,[z1,z23,z3,z4,z94,z5,z6]),(0,[z43,z1,z2,z4,z86,z5,z6]),(0,[z1,z2,z3,z4,z5,z319,z6]),(0,[z1,z320,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z321,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z322,z6])],[(1,[z2,z3,z4,z5,z6,z243])],[(0,[z323,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z324,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z7,z102]),(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z92,z3,z4,z27,z6]),(0,[z1,z2,z321,z3,z4,z5,z6])],[(0,[z2,z3,z4,z326,z5,z6,z7]),(0,[z1,z2,z3,z19,z146,z5,z6]),(0,[z1,z2,z47,z3,z4,z38,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z2,z47,z328,z3,z4,z6]),(0,[z1,z2,z3,z329,z4,z5,z6])],[(0,[z15,z1,z2,z151,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z86,z6]),(0,[z43,z1,z2,z3,z5,z6,z25]),(0,[z1,z2,z3,z330,z4,z5,z6])]],
   [[(0,[z1,z331,z2,z3,z4,z5,z6]),(0,[z1,z2,z332,z3,z4,z5,z6]),(0,[z333,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z316])],[(0,[z334,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z59,z5,z210,z6]),(0,[z37,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z335,z6]),(0,[z1,z2,z327,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z168,z5,z6])],[(0,[z178,z1,z2,z3,z4,z5,z6])],[(0,[z13,z2,z3,z4,z5,z6,z7]),(1,[z34,z1,z3,z4,z109,z6]),(0,[z1,z2,z3,z4,z5,z336,z6])],[(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z337,z5,z6]),(0,[z1,z2,z338,z3,z4,z5,z6]),(0,[z339,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z341,z6]),(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z38,z6]),(0,[z37,z1,z2,z44,z4,z5,z6])],[(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z344,z1,z2,z3,z4,z5,z6]),(0,[z178,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z4,z28,z6]),(0,[z1,z2,z3,z4,z345,z5,z6])],[(0,[z2,z3,z20,z4,z78,z5,z6]),(0,[z93,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z346,z4,z5,z6]),(0,[z1,z216,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z217]),(1,[z1,z2,z3,z4,z322,z6])],[(0,[z137,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z4,z59,z28,z6]),(0,[z1,z22,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z86,z5,z6]),(0,[z43,z1,z2,z3,z4,z302,z6])]],
   [[(0,[z348,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z349,z6]),(0,[z1,z2,z3,z350,z4,z5,z6]),(0,[z55,z2,z3,z4,z5,z6,z6]),(0,[z37,z55,z2,z3,z4,z5,z6]),(0,[z93,z351,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z345,z28,z6]),(0,[z1,z2,z3,z4,z5,z352,z6])],[(0,[z1,z2,z3,z353,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z157]),(0,[z1,z2,z23,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z5,z354,z6]),(0,[z1,z2,z3,z4,z355,z5,z6]),(0,[z1,z2,z3,z4,z28,z28,z6]),(0,[z1,z356,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z357]),(0,[z1,z358,z2,z3,z4,z5,z6])],[(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z1,z22,z2,z3,z4,z28,z6]),(0,[z1,z2,z92,z3,z4,z109,z6]),(0,[z37,z1,z2,z91,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z360,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z361]),(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z145,z1,z2,z3,z4,z354,z6]),(0,[z122,z1,z2,z3,z4,z5,z45]),(0,[z1,z2,z3,z4,z5,z6,z363]),(0,[z1,z2,z47,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z364,z6])],[(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z233]),(0,[z122,z1,z367,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z368,z5,z6]),(1,[z1,z16,z23,z4,z5,z6]),(0,[z369,z1,z2,z3,z4,z5,z6]),(0,[z1,z370,z2,z3,z4,z5,z6]),(1,[z1,z2,z114,z4,z5,z6]),(0,[z35,z1,z2,z3,z371,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6])],[(0,[z137,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z373,z4,z5,z6]),(1,[z255,z2,z3,z4,z6,z7]),(0,[z55,z2,z3,z4,z98,z5,z6]),(0,[z1,z16,z3,z4,z5,z6,z101]),(0,[z15,z1,z2,z3,z86,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z374])],[(0,[z1,z375,z2,z3,z4,z5,z6]),(0,[z376,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z377,z5,z6]),(0,[z93,z1,z2,z3,z378,z5,z6]),(1,[z1,z2,z3,z146,z28,z6]),(0,[z1,z2,z379,z3,z24,z4,z6]),(1,[z1,z380,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z381]),(0,[z1,z2,z3,z4,z5,z6,z382])]],
   [[(0,[z22,z2,z3,z4,z5,z6,z7]),(0,[z55,z2,z3,z4,z5,z27,z6]),(0,[z55,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z99,z6,z29])],[(0,[z13,z1,z2,z3,z78,z5,z6]),(0,[z1,z2,z383,z3,z4,z5,z6]),(0,[z15,z1,z2,z4,z5,z6,z102]),(0,[z1,z195,z2,z3,z4,z5,z6])],[(1,[z1,z2,z144,z4,z5,z6]),(0,[z1,z2,z3,z4,z384,z5,z6]),(0,[z1,z16,z2,z4,z86,z5,z6]),(0,[z385,z1,z2,z3,z4,z5,z6])],[(0,[z145,z1,z2,z47,z3,z4,z6]),(0,[z386,z2,z3,z4,z5,z99,z6])],[(0,[z1,z2,z47,z3,z4,z78,z6]),(0,[z387,z1,z2,z3,z4,z5,z6]),(0,[z161,z55,z2,z3,z4,z5,z6]),(0,[z2,z3,z388,z4,z5,z6,z7]),(0,[z55,z2,z3,z4,z5,z6,z7]),(0,[z389,z55,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z354,z6]),(0,[z1,z2,z3,z4,z225,z5,z6]),(1,[z1,z2,z151,z86,z5,z6]),(1,[z1,z2,z3,z4,z258,z6]),(0,[z1,z2,z3,z4,z258,z5,z6])],[(0,[z2,z3,z4,z5,z27,z6,z7]),(0,[z390,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z391,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z25])],[(0,[z77,z1,z2,z3,z5,z185,z6]),(0,[z2,z3,z4,z94,z5,z6,z7]),(0,[z1,z22,z2,z3,z24,z5,z6]),(0,[z1,z392,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z393]),(0,[z1,z2,z3,z4,z394,z5,z6]),(0,[z1,z2,z3,z4,z109,z98,z6]),(0,[z1,z2,z328,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z6,z29])]],
   [[(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z77,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z395,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z35,z55,z2,z3,z4,z5,z6]),(1,[z93,z1,z4,z94,z5,z6]),(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z1,z398,z2,z3,z4,z5,z6])],[(0,[z1,z2,z399,z83,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z361,z6]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z402]),(0,[z1,z2,z3,z4,z5,z6,z403]),(0,[z1,z2,z3,z4,z5,z404,z6]),(0,[z1,z2,z3,z4,z405,z28,z6])],[(0,[z406,z1,z2,z3,z4,z5,z6]),(0,[z407,z1,z2,z3,z4,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6])],[(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z55,z55,z2,z3,z4,z5,z6]),(1,[z1,z2,z171,z4,z5,z6]),(0,[z1,z2,z3,z410,z4,z5,z6])],[(0,[z1,z143,z2,z3,z4,z411,z6]),(0,[z1,z2,z47,z83,z3,z4,z6]),(0,[z13,z2,z3,z4,z78,z5,z6]),(0,[z2,z3,z4,z78,z5,z6,z7]),(0,[z1,z26,z2,z3,z412,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z413]),(1,[z1,z2,z47,z3,z4,z6]),(1,[z1,z2,z3,z19,z28,z6])],[(0,[z414,z1,z2,z3,z4,z5,z6]),(0,[z1,z415,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z64,z6]),(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z19,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z186]),(0,[z1,z2,z3,z4,z5,z6,z29])],[(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z416]),(0,[z43,z1,z2,z3,z146,z5,z6]),(0,[z417,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z418,z6])],[(0,[z317,z2,z3,z4,z5,z6,z7]),(0,[z55,z2,z3,z4,z94,z5,z6]),(0,[z1,z2,z3,z4,z5,z419,z6]),(1,[z1,z127,z3,z4,z5,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z193,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z292,z6]),(1,[z1,z2,z3,z421,z5,z6])]],
   [[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z129,z4,z5,z6]),(1,[z13,z1,z2,z3,z28,z6]),(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z255,z2,z3,z4,z5,z6,z7]),(0,[z1,z96,z3,z4,z94,z5,z6]),(0,[z1,z423,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z424]),(0,[z425,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z99,z6]),(0,[z1,z2,z3,z4,z5,z426,z6])],[(0,[z74,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z427,z5,z6]),(1,[z428,z1,z2,z3,z5,z6]),(0,[z55,z2,z92,z3,z4,z5,z6]),(0,[z429,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z28,z6]),(0,[z18,z1,z2,z269,z4,z5,z6])],[(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z2,z3,z4,z28,z6,z7]),(0,[z1,z2,z431,z3,z4,z5,z6]),(0,[z1,z3,z4,z146,z5,z6,z101]),(1,[z1,z96,z3,z4,z5,z36]),(0,[z1,z2,z367,z3,z4,z5,z6])],[(0,[z1,z2,z3,z432,z4,z5,z6]),(0,[z1,z2,z3,z4,z433,z5,z6]),(0,[z140,z58,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z4,z5,z6,z434]),(0,[z37,z1,z2,z3,z4,z28,z6]),(0,[z18,z1,z2,z3,z4,z5,z185])],[(0,[z435,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z146,z5,z6]),(0,[z55,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z3,z436,z4,z5,z6]),(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z438,z6])],[(0,[z1,z2,z439,z3,z4,z5,z6]),(0,[z440,z1,z2,z3,z4,z5,z6]),(0,[z1,z96,z3,z4,z5,z36,z6])],[(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z324,z4,z5,z6]),(1,[z1,z2,z3,z441,z5,z6]),(0,[z1,z2,z442,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z99,z6])],[(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z1,z444,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z445,z6]),(1,[z204,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z88,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z410,z4,z5,z6])]],
   [[(0,[z1,z72,z3,z4,z146,z5,z6]),(0,[z203,z2,z3,z4,z5,z6,z7]),(1,[z8,z1,z2,z3,z5,z6]),(0,[z1,z22,z3,z24,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z25])],[(0,[z137,z1,z2,z3,z4,z28,z6]),(0,[z93,z1,z2,z3,z368,z5,z6]),(0,[z1,z2,z44,z4,z94,z5,z6]),(0,[z1,z2,z3,z4,z447,z5,z6]),(0,[z1,z2,z3,z4,z448,z5,z6]),(0,[z449,z1,z2,z47,z3,z4,z6])],[(0,[z450,z1,z2,z3,z4,z5,z6]),(0,[z1,z22,z96,z3,z4,z5,z6]),(0,[z1,z26,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z451]),(0,[z15,z43,z1,z2,z4,z5,z6])],[(0,[z1,z2,z452,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z6]),(0,[z34,z1,z2,z47,z3,z4,z6]),(0,[z1,z453,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z19,z5,z6])],[(0,[z1,z2,z3,z4,z5,z454,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z243])],[(0,[z455,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z456,z3,z4,z5,z6]),(0,[z457,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z458,z3,z4,z5,z6]),(0,[z459,z1,z2,z3,z4,z5,z6])],[(0,[z77,z1,z2,z3,z86,z5,z6]),(0,[z122,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z460,z5,z6]),(0,[z1,z2,z3,z4,z38,z6,z29]),(0,[z461,z1,z2,z3,z4,z5,z6])],[(0,[z1,z143,z2,z3,z4,z89,z6]),(0,[z203,z55,z2,z3,z4,z5,z6]),(0,[z462,z1,z2,z3,z4,z5,z6]),(1,[z77,z1,z2,z3,z28,z6]),(0,[z463,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z151,z3,z4,z6]),(0,[z1,z2,z3,z4,z298,z5,z6]),(0,[z1,z2,z3,z4,z464,z5,z6]),(1,[z18,z1,z2,z3,z5,z25]),(0,[z196,z1,z2,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z29])]],
   [[(0,[z465,z1,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z5,z6]),(1,[z178,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z5,z28,z6]),(0,[z466,z1,z2,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z99])],[(0,[z1,z2,z47,z3,z4,z125,z6]),(0,[z55,z2,z3,z4,z80,z5,z6]),(0,[z43,z1,z127,z3,z4,z5,z6]),(0,[z1,z2,z91,z3,z467,z5,z6]),(0,[z122,z1,z2,z44,z4,z5,z6])],[(0,[z1,z2,z179,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z64,z185]),(0,[z1,z2,z468,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z86,z5,z6]),(0,[z1,z2,z3,z4,z28,z36,z6]),(0,[z1,z2,z3,z4,z5,z6,z469])],[(0,[z1,z2,z3,z4,z470,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z24,z4,z146,z5,z6]),(0,[z35,z1,z2,z3,z4,z28,z6]),(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z140,z1,z2,z47,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z473]),(1,[z303,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z123,z5,z6])],[(0,[z1,z22,z72,z3,z4,z5,z6]),(0,[z474,z2,z3,z4,z5,z6,z7]),(0,[z2,z3,z4,z5,z6,z6,z7]),(0,[z122,z55,z2,z3,z4,z5,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z475,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z476,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z45,z6])],[(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z478,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z5,z33,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z1,z2,z3,z4,z5,z480,z6]),(0,[z140,z1,z2,z3,z421,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z481])],[(0,[z1,z2,z3,z4,z482,z5,z6]),(1,[z1,z2,z399,z3,z4,z6]),(0,[z1,z2,z3,z4,z78,z28,z6]),(1,[z1,z2,z254,z3,z4,z6]),(0,[z365,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z483,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z484,z6]),(1,[z1,z2,z3,z28,z6,z25]),(0,[z1,z2,z3,z4,z485,z5,z6])]],
   [[(0,[z134,z2,z3,z20,z4,z5,z6]),(0,[z55,z2,z3,z19,z4,z5,z6]),(0,[z145,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z6,z101]),(0,[z1,z2,z3,z486,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z98,z6])],[(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z487,z5,z6]),(0,[z488,z1,z2,z3,z4,z5,z6])],[(0,[z58,z1,z2,z47,z3,z4,z6]),(0,[z2,z91,z3,z4,z5,z6,z7]),(0,[z1,z2,z489,z3,z4,z5,z6]),(0,[z1,z2,z490,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z492]),(0,[z1,z2,z3,z4,z493,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(0,[z1,z2,z495,z3,z4,z5,z6]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z322,z6])],[(0,[z74,z1,z2,z3,z4,z28,z6]),(0,[z63,z2,z3,z4,z5,z6,z7]),(1,[z1,z2,z3,z4,z433,z6]),(0,[z55,z2,z332,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z497])],[(0,[z77,z1,z2,z3,z5,z28,z6]),(0,[z1,z2,z3,z378,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z484,z6]),(0,[z43,z1,z2,z151,z3,z5,z6]),(0,[z1,z2,z91,z3,z4,z38,z6]),(0,[z1,z2,z4,z5,z38,z6,z102]),(0,[z1,z2,z3,z4,z5,z498,z6]),(0,[z1,z2,z3,z4,z5,z6,z499])],[(0,[z1,z2,z3,z388,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z500])],[(0,[z13,z1,z2,z3,z4,z5,z250]),(0,[z2,z3,z4,z5,z210,z6,z7]),(0,[z2,z3,z4,z5,z6,z7,z101]),(0,[z2,z241,z3,z4,z5,z6,z7]),(0,[z55,z1,z2,z3,z4,z5,z7]),(0,[z255,z1,z2,z3,z4,z5,z6]),(0,[z18,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z501]),(0,[z1,z2,z92,z3,z4,z98,z6]),(0,[z1,z2,z3,z4,z5,z6,z102]),(0,[z1,z502,z2,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z6,z29])]],
   [[(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z59,z5,z6,z7]),(0,[z55,z2,z3,z4,z59,z5,z6]),(0,[z1,z2,z3,z4,z504,z5,z6]),(0,[z1,z2,z3,z4,z505,z5,z6])],[(0,[z1,z143,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z506,z5,z6]),(0,[z15,z2,z3,z4,z5,z6,z7]),(0,[z2,z3,z4,z5,z6,z7,z507]),(0,[z39,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z4,z5,z6]),(0,[z1,z2,z3,z24,z5,z28,z6]),(0,[z1,z2,z3,z4,z5,z6,z508]),(0,[z122,z1,z2,z4,z5,z6,z102])],[(0,[z93,z2,z3,z4,z5,z6,z7]),(0,[z55,z2,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z3,z4,z510,z5,z6]),(0,[z1,z2,z151,z3,z4,z5,z6]),(0,[z1,z2,z47,z511,z3,z4,z6])],[(0,[z63,z55,z2,z3,z4,z5,z6]),(0,[z55,z22,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z47,z3,z4,z6])],[(0,[z1,z2,z3,z4,z512,z5,z6]),(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z1,z514,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z157]),(0,[z1,z2,z3,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z515,z5,z6]),(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z517,z6]),(0,[z15,z1,z2,z44,z4,z5,z6]),(0,[z518,z1,z2,z3,z4,z5,z6])],[(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z203,z1,z2,z4,z125,z5,z6]),(0,[z2,z3,z4,z5,z6,z520,z7]),(0,[z521,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z33]),(0,[z93,z1,z3,z4,z146,z5,z6]),(0,[z1,z16,z2,z4,z94,z5,z6]),(0,[z1,z522,z2,z3,z4,z5,z6]),(0,[z1,z16,z2,z47,z3,z4,z6]),(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z524])],[(0,[z1,z2,z525,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z2,z3,z86,z5,z6,z25]),(1,[z1,z2,z3,z467,z5,z6]),(0,[z303,z1,z2,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z6])],[(0,[z137,z74,z2,z3,z4,z5,z6]),(1,[z55,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z266,z6]),(0,[z145,z1,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z102]),(0,[z516,z1,z2,z3,z4,z28,z6])]],
   [[(0,[z134,z1,z2,z3,z4,z38,z6]),(0,[z428,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z7,z527]),(0,[z15,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z38,z6]),(1,[z1,z110,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z528,z5,z6]),(1,[z1,z2,z3,z4,z222,z6])],[(0,[z1,z2,z3,z4,z125,z5,z6]),(0,[z1,z2,z529,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z45,z6,z102])],[(0,[z1,z2,z3,z4,z5,z6,z530]),(0,[z203,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z428,z1,z2,z3,z59,z5,z6]),(0,[z2,z3,z4,z5,z6,z396,z7]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z2,z3,z4,z146,z28,z6]),(1,[z2,z3,z4,z150,z5,z6])],[(1,[z74,z143,z3,z4,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6])],[(0,[z1,z22,z2,z3,z146,z5,z6]),(0,[z1,z3,z4,z109,z5,z27,z6])],[(0,[z1,z2,z3,z533,z4,z5,z6]),(1,[z2,z3,z4,z150,z28,z6])],[(0,[z1,z2,z72,z3,z4,z5,z6]),(1,[z1,z14,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z1,z2,z3,z4,z5,z101,z102]),(0,[z1,z2,z3,z5,z28,z6,z25]),(1,[z1,z2,z269,z4,z5,z6]),(0,[z140,z1,z2,z329,z4,z5,z6])],[(0,[z58,z1,z2,z3,z4,z99,z6]),(0,[z1,z26,z2,z3,z4,z5,z6]),(0,[z1,z356,z2,z3,z4,z28,z6]),(0,[z1,z2,z103,z47,z3,z4,z6]),(0,[z1,z2,z47,z3,z4,z185,z6]),(0,[z1,z2,z3,z19,z5,z185,z6])]],
   [[(0,[z1,z2,z47,z3,z4,z210,z6]),(0,[z161,z2,z3,z4,z5,z6,z7]),(0,[z535,z55,z2,z3,z4,z5,z6]),(0,[z1,z16,z23,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z28,z6])],[(0,[z1,z143,z2,z3,z192,z5,z6]),(1,[z435,z1,z2,z3,z5,z6]),(0,[z55,z2,z3,z4,z201,z5,z6]),(1,[z1,z2,z3,z412,z5,z6]),(0,[z1,z2,z3,z536,z4,z5,z6])],[(0,[z1,z537,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z538,z5,z6]),(0,[z1,z2,z3,z4,z539,z5,z6]),(0,[z1,z2,z540,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z541,z6]),(0,[z1,z2,z3,z4,z5,z542,z6]),(0,[z93,z15,z1,z2,z4,z5,z6]),(0,[z1,z543,z2,z3,z4,z5,z6]),(0,[z1,z2,z544,z3,z4,z5,z6]),(0,[z35,z342,z2,z3,z4,z5,z6]),(0,[z35,z1,z96,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z545,z6]),(0,[z546,z1,z2,z3,z4,z5,z6])],[(0,[z137,z1,z72,z3,z4,z5,z6]),(0,[z35,z2,z3,z4,z5,z6,z7]),(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z547,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z410,z4,z5,z6])],[(0,[z1,z2,z3,z4,z548,z5,z6]),(0,[z134,z1,z2,z47,z3,z4,z6]),(0,[z1,z96,z2,z3,z4,z5,z101]),(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z122,z193,z2,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z149,z6]),(0,[z1,z2,z3,z4,z5,z405,z6])],[(0,[z77,z1,z2,z3,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z4,z550,z5,z6]),(0,[z1,z2,z551,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z552])],[(0,[z1,z553,z2,z3,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z554,z1,z2,z3,z4,z5,z6]),(0,[z1,z204,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z555,z6]),(0,[z1,z2,z3,z4,z556,z5,z6]),(0,[z286,z1,z2,z3,z4,z5,z6]),(1,[z122,z1,z2,z4,z5,z102])],[(0,[z63,z1,z2,z4,z125,z5,z6]),(1,[z2,z3,z4,z5,z7,z25]),(1,[z43,z1,z2,z3,z28,z6]),(0,[z39,z1,z2,z3,z4,z5,z6])],[(0,[z1,z557,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z146,z6]),(0,[z1,z2,z558,z3,z4,z5,z6]),(0,[z43,z1,z110,z3,z4,z5,z6]),(1,[z140,z1,z2,z3,z4,z29])],[(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z96,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z36,z102]),(0,[z1,z2,z3,z4,z5,z6,z561])],[(0,[z1,z2,z3,z4,z562,z5,z6]),(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z145,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z565,z3,z4,z5,z6]),(0,[z122,z216,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z4,z28,z6])],[(0,[z74,z2,z3,z4,z5,z6,z7]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z232,z3,z4,z5,z6]),(0,[z1,z96,z2,z3,z4,z5,z6]),(0,[z1,z2,z567,z151,z3,z4,z6]),(0,[z1,z2,z3,z4,z98,z38,z6])],[(0,[z1,z2,z568,z3,z4,z5,z6]),(0,[z15,z1,z2,z4,z125,z5,z6]),(0,[z63,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z83,z3,z166,z5,z6]),(0,[z569,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z23,z3,z4,z6]),(0,[z1,z3,z4,z5,z36,z6,z101]),(0,[z1,z2,z567,z3,z4,z5,z6]),(0,[z1,z570,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z3,z4,z572,z5,z6])],[(0,[z573,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z411,z6]),(0,[z134,z2,z3,z4,z5,z210,z6]),(0,[z1,z23,z3,z4,z146,z5,z6]),(0,[z145,z1,z3,z4,z146,z5,z6]),(0,[z1,z2,z3,z4,z38,z27,z6]),(0,[z1,z2,z3,z4,z574,z5,z6])]],
   [[(0,[z55,z2,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z575,z6]),(0,[z1,z2,z3,z4,z5,z576,z6]),(0,[z1,z26,z2,z3,z538,z5,z6]),(0,[z566,z1,z2,z3,z4,z28,z6])],[(0,[z77,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z441,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z520]),(0,[z1,z577,z2,z3,z4,z5,z6]),(0,[z1,z2,z578,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z6,z29]),(1,[z1,z2,z3,z371,z5,z6])],[(0,[z579,z1,z2,z3,z4,z5,z6]),(1,[z8,z2,z3,z5,z6,z7]),(0,[z55,z2,z3,z4,z5,z99,z6]),(0,[z1,z2,z3,z4,z580,z5,z6]),(0,[z1,z2,z3,z4,z5,z284,z6]),(0,[z18,z142,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z581,z6]),(0,[z1,z2,z3,z4,z210,z28,z6]),(0,[z145,z55,z2,z3,z4,z5,z6]),(0,[z15,z1,z2,z3,z4,z28,z6]),(0,[z1,z582,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z583])],[(0,[z584,z1,z2,z3,z4,z5,z6]),(0,[z2,z44,z3,z4,z5,z6,z7]),(0,[z55,z2,z3,z4,z5,z6,z25]),(0,[z145,z1,z2,z3,z4,z65,z6]),(1,[z130,z2,z3,z4,z5,z6]),(0,[z585,z1,z2,z3,z4,z5,z6])],[(0,[z143,z2,z3,z4,z5,z6,z7]),(0,[z13,z77,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z86,z146,z5,z6]),(0,[z1,z2,z379,z3,z4,z5,z6]),(0,[z1,z2,z151,z3,z4,z586,z6])],[(0,[z1,z2,z3,z4,z587,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z5,z293,z6]),(0,[z1,z2,z3,z4,z5,z45,z36]),(0,[z1,z588,z2,z3,z4,z5,z6]),(0,[z589,z1,z2,z47,z3,z4,z6]),(0,[z1,z2,z590,z3,z19,z4,z6]),(0,[z1,z591,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z98,z5,z29])],[(0,[z74,z1,z72,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z6]),(0,[z2,z3,z19,z4,z5,z6,z7]),(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z86,z5,z6]),(0,[z1,z2,z3,z4,z98,z5,z99])]],
   [[(0,[z535,z1,z2,z3,z4,z5,z6]),(0,[z1,z143,z3,z4,z146,z5,z6]),(0,[z1,z2,z3,z59,z441,z5,z6]),(0,[z1,z2,z3,z4,z594,z5,z6]),(0,[z1,z22,z3,z4,z5,z6,z101]),(0,[z39,z1,z2,z3,z24,z5,z6]),(0,[z1,z2,z595,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z38,z6,z7]),(0,[z596,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z199,z47,z3,z4,z6])],[(0,[z1,z2,z597,z3,z4,z5,z6]),(0,[z1,z22,z143,z3,z4,z5,z6]),(0,[z134,z1,z2,z3,z4,z99,z6]),(0,[z55,z2,z3,z4,z5,z45,z6])],[(1,[z145,z1,z3,z146,z5,z6]),(0,[z1,z2,z91,z4,z5,z38,z6])],[(0,[z1,z2,z3,z4,z5,z116,z6]),(1,[z55,z2,z3,z4,z5,z6]),(0,[z1,z598,z2,z3,z4,z5,z6])],[(0,[z13,z1,z2,z144,z4,z5,z6]),(0,[z16,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z86,z5,z6]),(1,[z1,z2,z3,z4,z292,z6])],[(0,[z13,z43,z1,z2,z3,z5,z6]),(0,[z1,z2,z599,z3,z4,z5,z6]),(1,[z351,z2,z3,z4,z5,z6]),(0,[z93,z1,z22,z3,z4,z5,z6]),(0,[z1,z2,z4,z86,z5,z6,z102]),(0,[z1,z2,z3,z4,z600,z5,z6]),(1,[z1,z360,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z1,z602,z2,z3,z4,z5,z6]),(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z604,z6])]],
   [[(0,[z605,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z399,z3,z4,z5,z6]),(1,[z13,z2,z3,z78,z5,z6]),(0,[z55,z2,z3,z4,z78,z5,z6]),(0,[z58,z1,z2,z3,z4,z38,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z99,z6])],[(0,[z43,z1,z2,z47,z3,z4,z6])],[(0,[z1,z2,z3,z20,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z606]),(0,[z161,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z28,z6,z25])],[(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z27,z6,z101]),(0,[z1,z2,z3,z4,z545,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z608]),(0,[z1,z2,z47,z3,z4,z5,z6])],[(0,[z609,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z185,z7]),(0,[z1,z26,z2,z3,z4,z109,z6]),(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z5,z45,z6]),(0,[z1,z2,z47,z44,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z611]),(0,[z1,z167,z2,z3,z4,z5,z6]),(0,[z1,z2,z60,z3,z4,z5,z6])],[(0,[z2,z72,z3,z4,z125,z5,z6]),(0,[z435,z1,z2,z83,z3,z5,z6]),(0,[z13,z1,z2,z3,z5,z185,z6]),(0,[z1,z2,z254,z3,z4,z5,z6]),(0,[z1,z2,z3,z20,z4,z28,z6]),(0,[z2,z3,z4,z5,z45,z6,z7]),(1,[z1,z2,z3,z378,z5,z6]),(0,[z1,z2,z3,z4,z5,z604,z6]),(0,[z18,z111,z2,z3,z4,z5,z6])],[(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z85,z7]),(0,[z1,z2,z612,z3,z4,z5,z6]),(1,[z178,z2,z3,z4,z28,z6]),(0,[z1,z2,z47,z3,z4,z28,z6]),(0,[z1,z2,z3,z19,z5,z28,z6])],[(0,[z1,z2,z3,z4,z5,z613,z6]),(0,[z13,z1,z2,z47,z3,z4,z6]),(0,[z614,z55,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z615]),(1,[z1,z2,z3,z86,z28,z6])],[(0,[z1,z143,z2,z3,z129,z5,z6]),(0,[z1,z2,z616,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z617,z3,z4,z5,z6]),(0,[z1,z2,z590,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z109,z5,z6]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z122,z1,z2,z3,z298,z5,z6]),(0,[z1,z2,z3,z4,z150,z5,z6]),(1,[z1,z2,z329,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z619]),(0,[z1,z620,z2,z3,z4,z5,z6]),(0,[z161,z1,z2,z3,z4,z5,z7]),(0,[z18,z2,z3,z4,z5,z6,z7]),(0,[z55,z2,z3,z4,z5,z6,z102]),(0,[z1,z16,z2,z23,z4,z5,z6]),(0,[z1,z2,z621,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z622,z5,z6])],[(0,[z623,z1,z2,z3,z4,z5,z6]),(1,[z1,z187,z3,z4,z5,z6]),(0,[z1,z624,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z28,z6]),(0,[z625,z1,z2,z3,z4,z5,z6])],[(0,[z203,z63,z2,z3,z4,z5,z6]),(0,[z1,z2,z626,z3,z4,z5,z6]),(0,[z39,z2,z3,z4,z5,z6,z7]),(0,[z1,z627,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z28,z6]),(0,[z18,z1,z2,z3,z5,z6,z25]),(1,[z53,z2,z3,z4,z5,z6])],[(0,[z145,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z628,z5,z6]),(0,[z629,z1,z2,z3,z4,z5,z6])],[(0,[z58,z1,z2,z3,z4,z210,z6]),(0,[z630,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z631]),(0,[z632,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z91,z4,z38,z6]),(0,[z39,z1,z2,z3,z5,z6,z25]),(0,[z1,z2,z3,z4,z98,z99,z6])]],
   [[(0,[z1,z2,z633,z3,z4,z5,z6]),(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z635,z5,z6])],[(0,[z2,z3,z4,z125,z5,z6,z7]),(0,[z2,z3,z4,z146,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z6,z636]),(0,[z1,z2,z3,z4,z5,z637,z6]),(0,[z1,z2,z3,z146,z5,z28,z6]),(0,[z1,z2,z3,z4,z5,z6,z101]),(0,[z1,z2,z3,z4,z467,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z638]),(0,[z1,z2,z112,z3,z4,z5,z6]),(1,[z386,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z20,z4,z639,z6]),(0,[z1,z640,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z641])],[(0,[z77,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z5,z6,z507]),(1,[z2,z3,z4,z6,z85,z7]),(0,[z55,z2,z3,z4,z146,z5,z6]),(0,[z55,z2,z3,z4,z5,z38,z6]),(0,[z140,z55,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z4,z86,z5,z6]),(0,[z1,z2,z642,z3,z4,z5,z6]),(0,[z1,z2,z643,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z644,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z85]),(0,[z645,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z416]),(0,[z1,z96,z3,z4,z146,z5,z6]),(0,[z39,z1,z2,z241,z3,z5,z6]),(0,[z1,z2,z3,z421,z4,z5,z6])],[(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z24,z436,z4,z5,z6]),(0,[z35,z1,z2,z3,z225,z5,z6]),(1,[z35,z1,z3,z4,z5,z101]),(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z185]),(0,[z140,z1,z360,z3,z4,z5,z6])],[(0,[z647,z1,z2,z3,z4,z5,z6]),(1,[z1,z367,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z648,z6]),(0,[z1,z143,z2,z3,z4,z28,z6]),(0,[z2,z3,z4,z5,z185,z6,z7]),(0,[z1,z2,z3,z24,z4,z28,z6]),(0,[z1,z2,z47,z92,z3,z4,z6])]],
   [[(0,[z145,z1,z22,z3,z4,z5,z6]),(0,[z1,z2,z151,z3,z4,z28,z6])],[(0,[z137,z1,z143,z3,z4,z5,z6]),(1,[z63,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z639,z6]),(0,[z1,z2,z47,z3,z4,z59,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z5,z7,z25]),(0,[z1,z2,z3,z4,z5,z6,z416]),(0,[z1,z649,z2,z3,z4,z5,z6]),(1,[z15,z43,z1,z2,z5,z6]),(0,[z1,z2,z92,z3,z4,z6,z29]),(0,[z1,z2,z3,z123,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z6,z102]),(0,[z1,z2,z3,z4,z5,z650,z6])],[(0,[z1,z2,z3,z4,z5,z6,z527]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z2,z3,z4,z5,z6,z652])],[(1,[z1,z2,z3,z166,z5,z6]),(0,[z589,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z27,z6]),(1,[z1,z2,z3,z4,z484,z6])],[(1,[z203,z2,z4,z125,z5,z6]),(0,[z30,z2,z3,z4,z5,z6,z7]),(0,[z49,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z379,z3,z4,z6]),(0,[z1,z2,z3,z4,z412,z5,z6]),(1,[z207,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z149,z6])],[(0,[z13,z1,z2,z3,z86,z5,z6]),(0,[z1,z2,z3,z653,z4,z5,z6]),(0,[z1,z2,z44,z4,z5,z38,z6]),(0,[z1,z2,z3,z4,z38,z28,z6])],[(0,[z2,z3,z4,z5,z99,z6,z7]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z655,z3,z4,z5,z6]),(0,[z1,z380,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z656]),(0,[z1,z2,z3,z4,z125,z28,z6]),(0,[z77,z1,z2,z3,z24,z5,z6]),(0,[z614,z1,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z85]),(1,[z1,z2,z3,z368,z5,z6]),(0,[z657,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z658,z6]),(0,[z1,z2,z511,z3,z4,z5,z6]),(1,[z142,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z659,z4,z5,z6]),(0,[z660,z2,z3,z4,z5,z6,z7]),(0,[z2,z151,z3,z4,z5,z6,z7]),(0,[z661,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z662,z6])],[(0,[z58,z134,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z384,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z35,z1,z3,z4,z5,z6,z101]),(0,[z1,z2,z3,z4,z5,z663,z6]),(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z341,z6]),(0,[z449,z1,z2,z3,z4,z5,z6]),(1,[z196,z2,z3,z4,z5,z6])],[(0,[z2,z525,z3,z4,z5,z6,z7]),(0,[z2,z3,z4,z5,z6,z7,z206]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z664,z6]),(0,[z1,z2,z3,z4,z665,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z45])],[(1,[z134,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z5,z666,z6]),(0,[z30,z55,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z114,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z667])],[(0,[z1,z2,z72,z3,z4,z28,z6]),(1,[z1,z2,z3,z192,z5,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z1,z669,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z639,z6]),(0,[z1,z2,z3,z4,z5,z670,z6]),(0,[z140,z53,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z671,z5,z6]),(0,[z1,z2,z672,z3,z4,z5,z6]),(0,[z93,z318,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z266,z6]),(0,[z1,z26,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z371,z4,z5,z6]),(0,[z122,z1,z380,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z673,z5,z6]),(0,[z2,z3,z4,z5,z6,z7,z7]),(1,[z1,z2,z3,z24,z28,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z5,z28,z6]),(0,[z1,z2,z3,z4,z5,z662,z6])],[(0,[z1,z2,z3,z4,z411,z5,z6]),(0,[z1,z674,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z675,z6]),(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z433,z6]),(0,[z2,z3,z4,z5,z6,z157,z7]),(0,[z1,z2,z3,z4,z677,z5,z6]),(0,[z1,z2,z3,z4,z27,z6,z29]),(0,[z678,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z83,z3,z4,z125,z5,z6]),(0,[z1,z2,z47,z3,z4,z109,z6]),(0,[z1,z2,z3,z4,z5,z185,z6])],[(0,[z39,z1,z2,z47,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z679,z6])],[(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z134,z1,z2,z3,z4,z210,z6]),(0,[z75,z55,z2,z3,z4,z5,z6]),(0,[z1,z681,z2,z3,z4,z5,z6]),(1,[z1,z2,z590,z3,z4,z6])],[(0,[z2,z3,z4,z109,z5,z6,z7]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z682])],[(0,[z1,z2,z3,z4,z5,z683,z6]),(0,[z74,z1,z143,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z5,z28,z6]),(0,[z1,z2,z684,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z7,z238]),(0,[z55,z2,z3,z4,z5,z575,z6]),(0,[z55,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z3,z4,z5,z586,z6]),(0,[z1,z2,z3,z4,z685,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z686,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z83,z3,z4,z28,z6]),(0,[z55,z577,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6]),(0,[z18,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z688,z3,z4,z5,z6])],[(0,[z1,z660,z2,z3,z4,z5,z6]),(0,[z134,z2,z3,z4,z5,z6,z7]),(0,[z255,z1,z2,z3,z4,z6,z7]),(0,[z1,z351,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z146,z5,z6]),(0,[z1,z2,z92,z4,z5,z38,z6]),(0,[z1,z2,z241,z3,z5,z28,z6]),(0,[z140,z1,z2,z3,z4,z28,z6]),(0,[z689,z1,z2,z3,z4,z5,z6])],[(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z691,z3,z4,z5,z6]),(0,[z1,z22,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z171,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z5,z6,z262])]],
   [[(1,[z1,z2,z436,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z45,z101]),(0,[z1,z2,z3,z4,z5,z6,z692])],[(0,[z1,z2,z47,z3,z20,z4,z6]),(0,[z386,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z324,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(1,[z2,z47,z3,z4,z6,z7]),(0,[z55,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z92,z3,z4,z5,z6]),(1,[z111,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z19,z5,z185])],[(0,[z1,z2,z3,z4,z5,z695,z6]),(0,[z1,z2,z3,z696,z4,z5,z6]),(0,[z1,z697,z2,z3,z4,z5,z6]),(0,[z1,z96,z2,z3,z4,z28,z6]),(1,[z1,z2,z567,z3,z4,z6]),(0,[z18,z1,z195,z3,z4,z5,z6])],[(0,[z1,z698,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z699,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z185,z7])],[(0,[z134,z55,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z24,z5,z6]),(0,[z1,z370,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z700])],[(0,[z1,z2,z701,z3,z4,z5,z6]),(0,[z702,z1,z2,z3,z4,z5,z6]),(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z704])],[(0,[z705,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z706,z3,z4,z5,z6]),(1,[z342,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z545,z6]),(1,[z1,z2,z3,z4,z586,z6]),(0,[z1,z2,z151,z4,z86,z5,z6]),(1,[z1,z2,z3,z4,z115,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z8,z255,z2,z3,z4,z6]),(0,[z93,z1,z47,z4,z94,z6]),(0,[z1,z2,z551,z86,z5,z6]),(0,[z707,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z708,z6])],[(0,[z1,z2,z3,z192,z89,z6]),(0,[z77,z2,z3,z150,z5,z6]),(0,[z2,z3,z4,z5,z6,z709]),(0,[z1,z2,z47,z710,z3,z6])],[(0,[z2,z3,z4,z411,z6,z7]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z134,z2,z3,z4,z639,z6]),(0,[z161,z2,z3,z4,z5,z712]),(0,[z1,z2,z713,z4,z5,z6]),(0,[z1,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z28,z6,z611])],[(0,[z1,z2,z3,z4,z5,z714]),(0,[z203,z2,z47,z4,z125,z6]),(0,[z2,z3,z4,z59,z116,z6]),(0,[z2,z3,z20,z5,z6,z157]),(0,[z1,z16,z621,z4,z5,z6]),(0,[z1,z2,z3,z133,z28,z6])],[(0,[z13,z320,z2,z3,z5,z6]),(0,[z1,z2,z41,z3,z28,z6]),(0,[z1,z2,z715,z3,z4,z6]),(0,[z1,z2,z3,z19,z5,z658]),(0,[z122,z1,z2,z298,z5,z102]),(0,[z178,z2,z3,z19,z28,z6])],[(0,[z1,z2,z3,z324,z28,z6]),(0,[z1,z2,z3,z24,z116,z6]),(0,[z43,z1,z2,z3,z267,z6]),(0,[z1,z3,z225,z5,z6,z101])],[(0,[z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z5,z716]),(0,[z1,z2,z3,z28,z6,z615]),(0,[z1,z2,z3,z4,z717,z6]),(0,[z1,z2,z3,z4,z28,z416]),(0,[z1,z2,z718,z3,z4,z6]),(0,[z719,z2,z3,z4,z28,z6])],[(0,[z1,z2,z47,z3,z129,z6]),(0,[z2,z3,z4,z5,z42,z7]),(0,[z55,z2,z436,z4,z5,z6]),(0,[z35,z1,z3,z4,z28,z101]),(0,[z1,z2,z44,z4,z5,z247]),(0,[z720,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z721,z6]),(0,[z63,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z722,z6]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z212,z1,z2,z4,z5,z102]),(0,[z1,z2,z3,z4,z724,z6]),(0,[z725,z2,z3,z4,z28,z6])],[(0,[z55,z2,z324,z4,z5,z6]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z1,z3,z4,z5,z6,z727])],[],[(0,[z193,z2,z3,z4,z5,z6]),(0,[z728,z2,z3,z5,z6,z7]),(0,[z297,z1,z3,z146,z5,z6]),(0,[z15,z43,z1,z2,z28,z6])],[(0,[z1,z2,z3,z729,z5,z6]),(0,[z13,z2,z3,z78,z5,z250]),(1,[z730,z2,z3,z4,z6]),(0,[z1,z110,z3,z146,z5,z6])],[(0,[z1,z2,z731,z4,z5,z6]),(0,[z1,z2,z3,z166,z28,z6]),(0,[z1,z2,z3,z4,z732,z6]),(0,[z2,z3,z28,z6,z157,z7]),(0,[z2,z3,z4,z80,z5,z7]),(0,[z1,z2,z3,z28,z64,z25]),(0,[z1,z2,z3,z28,z6,z631]),(0,[z1,z2,z47,z171,z4,z6]),(0,[z1,z2,z3,z4,z733,z6]),(0,[z1,z367,z3,z4,z149,z6])],[(0,[z1,z2,z734,z4,z5,z6]),(0,[z1,z2,z735,z4,z5,z6]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z3,z4,z6,z85]),(0,[z55,z2,z3,z4,z115,z6]),(0,[z1,z2,z3,z368,z5,z6]),(0,[z1,z2,z3,z368,z5,z416]),(0,[z1,z2,z737,z3,z4,z6]),(0,[z207,z2,z3,z4,z28,z6])],[(0,[z63,z2,z83,z166,z5,z6]),(0,[z2,z738,z4,z5,z6,z7]),(0,[z2,z3,z4,z28,z6,z739])]],
   [[(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z22,z3,z4,z5,z416])],[(0,[z503,z1,z3,z146,z5,z6]),(0,[z1,z2,z3,z4,z98,z418]),(0,[z741,z2,z3,z4,z28,z6]),(0,[z142,z2,z3,z4,z28,z6])],[(0,[z2,z3,z388,z5,z6,z157]),(0,[z55,z2,z3,z4,z5,z33]),(0,[z318,z2,z47,z3,z4,z6]),(1,[z1,z4,z742,z5,z6]),(0,[z1,z2,z379,z436,z4,z6])],[(0,[z1,z2,z3,z192,z5,z6]),(0,[z743,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z744,z6]),(0,[z2,z3,z4,z745,z6,z7]),(0,[z193,z2,z3,z4,z149,z6])],[(0,[z2,z3,z441,z5,z6,z7]),(0,[z428,z1,z2,z47,z3,z6]),(0,[z728,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z746,z6]),(0,[z1,z2,z747,z4,z5,z6]),(0,[z43,z1,z2,z3,z322,z6]),(0,[z216,z367,z3,z4,z5,z6])],[(0,[z8,z161,z2,z3,z5,z7]),(0,[z1,z2,z3,z24,z28,z6]),(0,[z1,z2,z3,z225,z5,z6])],[(0,[z1,z2,z3,z533,z28,z6]),(0,[z2,z3,z4,z748,z5,z6]),(0,[z255,z2,z3,z4,z185,z7]),(0,[z749,z2,z3,z4,z5,z6]),(0,[z35,z1,z3,z225,z5,z101])],[(0,[z13,z134,z2,z3,z28,z6]),(0,[z589,z1,z2,z3,z28,z6]),(0,[z134,z1,z2,z329,z4,z6]),(0,[z1,z4,z94,z5,z6,z416]),(0,[z1,z2,z4,z5,z45,z750])],[(0,[z1,z14,z144,z4,z5,z6]),(0,[z134,z2,z3,z4,z150,z6]),(0,[z195,z3,z4,z5,z6,z7]),(0,[z1,z360,z60,z4,z5,z6])],[(0,[z751,z2,z3,z4,z6,z7]),(0,[z2,z3,z4,z752,z6,z7]),(0,[z1,z2,z753,z4,z5,z6]),(0,[z1,z2,z3,z298,z292,z6]),(0,[z82,z2,z60,z4,z5,z6])],[(0,[z474,z2,z4,z125,z5,z6]),(0,[z37,z55,z2,z92,z4,z6]),(0,[z1,z2,z3,z4,z754,z6]),(0,[z1,z2,z442,z86,z5,z6])],[(0,[z1,z2,z3,z4,z755,z6]),(0,[z1,z2,z3,z756,z5,z6]),(0,[z2,z3,z4,z59,z6,z85]),(0,[z757,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z378,z5,z33]),(0,[z18,z1,z2,z269,z5,z25]),(0,[z758,z2,z3,z4,z6,z186])],[(0,[z1,z2,z759,z3,z4,z6]),(0,[z134,z1,z2,z3,z168,z6]),(1,[z2,z3,z28,z7,z25]),(0,[z34,z1,z3,z4,z635,z6])],[(0,[z13,z1,z2,z3,z222,z6]),(0,[z1,z2,z3,z5,z6,z760])],[(0,[z1,z761,z3,z4,z5,z6]),(0,[z1,z2,z3,z762,z5,z6])],[(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z22,z3,z24,z5,z6]),(0,[z17,z1,z2,z3,z5,z25]),(0,[z764,z2,z3,z4,z28,z6])]],
   [[(0,[z765,z2,z3,z4,z5,z6]),(0,[z766,z2,z3,z4,z5,z6]),(0,[z1,z2,z495,z86,z5,z6]),(0,[z767,z2,z47,z3,z4,z6])],[(0,[z143,z768,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z769,z6]),(0,[z1,z2,z3,z4,z770,z6])],[(0,[z1,z2,z3,z4,z771,z6]),(0,[z255,z1,z2,z3,z4,z6])],[(0,[z1,z2,z772,z3,z4,z6]),(0,[z390,z1,z3,z4,z5,z101])],[(0,[z1,z2,z3,z4,z773,z6]),(0,[z1,z2,z3,z346,z28,z6]),(0,[z1,z2,z774,z4,z5,z6]),(0,[z1,z2,z3,z330,z28,z6]),(0,[z1,z2,z3,z19,z28,z185]),(0,[z286,z1,z2,z4,z604,z6])],[(0,[z1,z2,z3,z4,z5,z775]),(0,[z17,z1,z3,z4,z5,z101])],[(0,[z63,z2,z288,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z776]),(0,[z777,z1,z2,z129,z5,z6]),(0,[z13,z1,z2,z3,z28,z361]),(0,[z1,z2,z3,z4,z778,z6])],[(0,[z55,z779,z3,z4,z5,z6]),(0,[z1,z2,z780,z3,z4,z6]),(0,[z1,z2,z781,z3,z4,z6]),(0,[z53,z2,z60,z4,z5,z6])],[(0,[z782,z2,z4,z5,z6,z7]),(0,[z2,z3,z4,z322,z6,z7]),(0,[z1,z2,z3,z4,z783,z6])],[(0,[z1,z514,z3,z4,z109,z6]),(0,[z342,z2,z3,z4,z28,z6])],[(0,[z39,z55,z2,z47,z3,z6]),(0,[z1,z2,z784,z3,z4,z6])],[(0,[z2,z3,z4,z149,z6,z7]),(0,[z265,z1,z2,z3,z28,z6])],[(0,[z435,z1,z2,z3,z84,z6]),(0,[z1,z2,z3,z785,z5,z6])],[(0,[z1,z2,z3,z786,z5,z6]),(0,[z55,z167,z3,z4,z5,z6]),(0,[z55,z2,z3,z168,z5,z6]),(0,[z475,z1,z2,z3,z28,z6]),(0,[z787,z2,z3,z4,z5,z6]),(0,[z1,z167,z60,z4,z5,z6])],[(0,[z1,z2,z788,z3,z4,z6]),(0,[z1,z789,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z28,z45]),(0,[z196,z2,z3,z19,z5,z185])],[(0,[z1,z2,z3,z4,z790,z6]),(0,[z471,z1,z3,z4,z5,z101]),(0,[z49,z1,z2,z4,z28,z6]),(0,[z18,z111,z2,z3,z5,z25]),(0,[z18,z1,z2,z3,z222,z25])]],
   [[(0,[z1,z2,z3,z4,z791,z6]),(0,[z1,z2,z3,z4,z792,z6])],[(0,[z2,z3,z4,z5,z361,z7]),(0,[z82,z2,z3,z4,z5,z6]),(0,[z2,z3,z168,z5,z6,z7]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z23,z3,z146,z28,z6]),(0,[z1,z2,z60,z4,z28,z6])],[(0,[z2,z3,z467,z5,z6,z7]),(0,[z1,z2,z738,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z794]),(0,[z2,z3,z4,z5,z6,z795]),(0,[z796,z1,z2,z3,z5,z6]),(0,[z1,z367,z3,z298,z5,z6]),(0,[z2,z3,z19,z5,z185,z186])],[(0,[z2,z3,z146,z28,z6,z7]),(0,[z1,z2,z3,z797,z5,z6])],[(0,[z1,z2,z3,z4,z798,z6]),(0,[z1,z2,z799,z3,z4,z6]),(0,[z1,z2,z171,z371,z5,z6]),(0,[z1,z2,z458,z3,z28,z6]),(0,[z1,z380,z3,z4,z292,z6]),(0,[z1,z2,z3,z28,z6,z704])],[(0,[z13,z1,z112,z3,z5,z6]),(0,[z2,z3,z4,z5,z7,z172]),(0,[z1,z2,z3,z275,z28,z6]),(0,[z2,z3,z4,z6,z800,z186])],[(0,[z1,z2,z3,z801,z5,z6]),(0,[z1,z2,z3,z5,z6,z802]),(0,[z2,z3,z4,z5,z7,z174]),(0,[z1,z26,z3,z412,z27,z6])],[(0,[z55,z195,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z803,z6]),(0,[z1,z26,z3,z538,z27,z6]),(0,[z18,z1,z2,z3,z5,z804]),(0,[z1,z2,z3,z4,z805,z6])],[(0,[z2,z3,z4,z5,z235,z7]),(0,[z13,z2,z3,z150,z28,z6]),(0,[z2,z3,z4,z5,z236,z7]),(0,[z342,z2,z3,z225,z5,z6]),(0,[z1,z2,z3,z225,z545,z6])],[(0,[z1,z3,z4,z5,z6,z806]),(0,[z1,z2,z3,z4,z769,z6]),(0,[z1,z2,z3,z291,z28,z6]),(0,[z1,z96,z47,z3,z4,z36]),(0,[z122,z1,z367,z4,z5,z102])],[(0,[z1,z415,z3,z4,z27,z6]),(0,[z43,z2,z3,z5,z7,z25]),(0,[z178,z2,z3,z4,z38,z6])],[(0,[z1,z2,z3,z482,z28,z6]),(0,[z1,z2,z3,z807,z5,z6])],[(0,[z1,z2,z3,z4,z6,z808])],[(0,[z1,z2,z3,z809,z5,z6]),(0,[z2,z3,z4,z28,z185,z7]),(0,[z2,z47,z3,z150,z28,z6])],[(0,[z1,z2,z3,z129,z28,z6]),(0,[z1,z2,z324,z4,z5,z250]),(0,[z204,z2,z47,z3,z4,z6])],[(0,[z55,z2,z3,z4,z5,z541]),(0,[z2,z3,z4,z5,z7,z656]),(0,[z1,z187,z3,z4,z5,z361]),(0,[z1,z779,z3,z4,z5,z6]),(0,[z730,z2,z3,z4,z5,z6]),(0,[z810,z2,z3,z4,z5,z6]),(0,[z34,z1,z3,z4,z109,z6]),(0,[z1,z2,z47,z3,z306,z6]),(0,[z811,z2,z3,z4,z5,z6]),(0,[z111,z112,z3,z4,z5,z6]),(0,[z812,z2,z3,z4,z322,z6])]],
   [[(0,[z1,z187,z3,z146,z5,z6]),(0,[z55,z2,z3,z225,z5,z6]),(0,[z1,z2,z3,z311,z28,z6]),(0,[z204,z2,z3,z371,z5,z6])],[(0,[z93,z351,z4,z94,z5,z6]),(0,[z18,z1,z195,z3,z5,z25]),(0,[z1,z2,z199,z3,z168,z6])],[(0,[z1,z2,z3,z4,z813,z6]),(0,[z1,z2,z3,z4,z814,z6]),(0,[z1,z2,z3,z815,z5,z6])],[(0,[z1,z2,z3,z4,z816,z6]),(0,[z1,z2,z3,z4,z817,z6])],[(0,[z255,z55,z2,z3,z4,z7]),(0,[z106,z2,z3,z158,z5,z6]),(0,[z1,z22,z3,z378,z5,z6]),(0,[z1,z22,z47,z3,z24,z6]),(0,[z1,z2,z818,z4,z5,z6]),(0,[z819,z2,z3,z4,z5,z6])],[(0,[z55,z2,z3,z4,z5,z666]),(0,[z55,z2,z820,z3,z4,z6]),(0,[z1,z2,z436,z5,z6,z25]),(0,[z1,z2,z3,z168,z5,z6])],[(0,[z1,z2,z3,z4,z821,z6]),(0,[z2,z3,z4,z59,z822,z6]),(0,[z343,z1,z2,z3,z28,z6]),(0,[z39,z1,z2,z379,z3,z6])],[(0,[z55,z2,z3,z4,z84,z6]),(0,[z1,z2,z3,z4,z5,z361]),(0,[z1,z14,z3,z5,z28,z6]),(0,[z93,z1,z3,z146,z28,z6]),(0,[z178,z2,z47,z3,z4,z6]),(0,[z18,z1,z112,z3,z5,z25]),(0,[z1,z360,z3,z4,z98,z6])],[(0,[z55,z2,z3,z4,z5,z253]),(0,[z1,z22,z3,z129,z5,z6]),(0,[z1,z2,z3,z4,z823,z6]),(0,[z1,z2,z824,z4,z5,z6])],[(0,[z1,z2,z114,z4,z5,z6]),(1,[z1,z127,z3,z28,z6]),(0,[z2,z3,z4,z5,z6,z825])],[(0,[z826,z55,z2,z3,z5,z6]),(0,[z55,z22,z3,z24,z5,z6]),(0,[z35,z1,z114,z4,z5,z101])],[(0,[z1,z2,z47,z269,z4,z6])],[(0,[z1,z2,z827,z4,z5,z6]),(0,[z8,z2,z828,z5,z6,z7]),(0,[z1,z2,z3,z202,z28,z6])],[(0,[z22,z3,z24,z5,z6,z7]),(0,[z8,z2,z3,z5,z6,z157]),(0,[z625,z1,z2,z3,z28,z6])],[(0,[z1,z829,z3,z4,z5,z6]),(0,[z1,z2,z269,z4,z222,z6])],[(0,[z1,z2,z830,z3,z4,z6]),(0,[z8,z2,z3,z5,z7,z25]),(0,[z1,z195,z3,z4,z5,z6]),(0,[z1,z2,z171,z4,z5,z101]),(0,[z1,z831,z47,z3,z4,z6])]],
   [[(0,[z137,z72,z3,z4,z5,z6]),(0,[z2,z83,z4,z832,z5,z6]),(0,[z13,z1,z14,z3,z28,z6]),(0,[z1,z2,z3,z4,z6,z833]),(0,[z2,z241,z3,z28,z6,z7]),(0,[z2,z60,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z258,z6])],[(0,[z1,z2,z3,z4,z5,z834]),(0,[z614,z2,z3,z4,z201,z6]),(0,[z1,z2,z710,z3,z5,z6])],[(0,[z1,z2,z3,z4,z835,z6]),(0,[z134,z2,z3,z4,z5,z250]),(0,[z351,z2,z4,z86,z5,z6]),(0,[z2,z3,z4,z5,z6,z836]),(1,[z1,z2,z3,z5,z804])],[(0,[z1,z837,z3,z4,z5,z6]),(1,[z2,z3,z748,z5,z6]),(0,[z1,z2,z838,z3,z4,z6]),(0,[z1,z71,z3,z4,z27,z6]),(0,[z839,z2,z3,z4,z5,z6]),(0,[z2,z3,z150,z441,z28,z6]),(0,[z1,z2,z47,z3,z650,z6])],[(0,[z2,z3,z4,z185,z85,z7]),(0,[z93,z1,z4,z94,z5,z416]),(0,[z840,z1,z2,z4,z5,z6]),(0,[z1,z2,z410,z4,z222,z6])],[(0,[z1,z2,z841,z4,z5,z6]),(0,[z1,z2,z129,z731,z5,z6]),(0,[z1,z2,z3,z4,z5,z842]),(0,[z8,z1,z2,z738,z5,z6]),(0,[z1,z2,z3,z843,z5,z6]),(0,[z386,z2,z47,z3,z4,z6])],[(0,[z1,z2,z3,z4,z116,z250]),(0,[z1,z2,z3,z377,z28,z6]),(0,[z2,z3,z4,z484,z6,z7]),(0,[z2,z3,z4,z5,z7,z704]),(0,[z1,z2,z3,z4,z6,z844]),(0,[z2,z3,z4,z6,z85,z243]),(0,[z1,z96,z3,z4,z5,z845]),(0,[z1,z2,z3,z539,z28,z6])],[(0,[z1,z2,z3,z846,z5,z6]),(0,[z1,z356,z3,z146,z28,z6]),(0,[z1,z2,z44,z298,z5,z6]),(0,[z1,z2,z3,z4,z847,z6]),(0,[z1,z2,z3,z28,z6,z175])],[(0,[z39,z1,z2,z3,z433,z6]),(0,[z58,z2,z3,z4,z314,z6]),(0,[z1,z848,z2,z3,z4,z6]),(0,[z216,z2,z3,z4,z28,z6]),(0,[z66,z1,z2,z3,z4,z316])],[(0,[z367,z3,z4,z5,z6,z7]),(0,[z1,z2,z148,z3,z28,z6]),(0,[z1,z2,z3,z123,z292,z6])],[(0,[z1,z2,z849,z4,z5,z6]),(0,[z2,z3,z4,z639,z6,z7]),(0,[z142,z195,z3,z4,z5,z6]),(0,[z1,z2,z329,z4,z6,z29])],[(0,[z1,z850,z3,z4,z5,z6]),(0,[z55,z2,z399,z3,z4,z6]),(0,[z474,z2,z4,z5,z6,z527]),(0,[z2,z3,z5,z6,z7,z802]),(0,[z55,z2,z3,z28,z6,z25]),(0,[z1,z851,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z5,z750]),(0,[z2,z3,z4,z5,z6,z852])],[(0,[z255,z2,z3,z20,z4,z6]),(0,[z55,z2,z241,z3,z28,z6]),(0,[z1,z2,z199,z3,z4,z662])],[(0,[z1,z2,z47,z3,z192,z6]),(0,[z1,z2,z853,z4,z5,z6]),(0,[z1,z854,z3,z4,z5,z6]),(0,[z1,z2,z820,z3,z4,z6]),(0,[z1,z2,z3,z855,z5,z6]),(0,[z1,z2,z92,z3,z467,z6])],[(0,[z1,z2,z3,z394,z28,z6]),(0,[z1,z2,z171,z4,z484,z6])],[(0,[z1,z2,z3,z4,z84,z6]),(0,[z77,z2,z3,z20,z5,z6]),(0,[z13,z2,z3,z5,z185,z7]),(0,[z1,z2,z86,z28,z6,z102]),(0,[z1,z2,z3,z856,z5,z6])]],
   [[(0,[z1,z2,z857,z4,z5,z6]),(0,[z39,z2,z47,z3,z6,z7]),(0,[z178,z2,z3,z86,z28,z6]),(0,[z2,z3,z4,z5,z6,z858])],[(0,[z859,z1,z2,z3,z5,z6]),(0,[z93,z1,z4,z94,z107,z6]),(0,[z1,z681,z3,z4,z27,z6]),(0,[z1,z2,z4,z38,z6,z228]),(0,[z1,z2,z47,z3,z123,z6]),(0,[z1,z860,z3,z4,z5,z6])],[(0,[z74,z143,z3,z4,z411,z6]),(0,[z1,z861,z3,z4,z5,z6]),(0,[z162,z1,z2,z3,z4,z29]),(0,[z140,z53,z2,z3,z4,z29])],[(0,[z2,z3,z4,z5,z349,z7]),(0,[z2,z3,z4,z6,z7,z862]),(0,[z1,z2,z3,z6,z85,z157]),(0,[z686,z1,z2,z92,z4,z6])],[(0,[z751,z1,z2,z3,z6,z157])],[(0,[z1,z2,z86,z125,z28,z6]),(0,[z1,z14,z47,z3,z4,z6]),(0,[z93,z1,z4,z94,z266,z6]),(0,[z1,z16,z476,z4,z5,z6]),(0,[z1,z2,z3,z863,z5,z6])],[(0,[z1,z2,z3,z166,z84,z6]),(0,[z1,z2,z3,z4,z28,z250]),(0,[z77,z2,z3,z685,z5,z6]),(0,[z2,z3,z4,z107,z6,z7]),(0,[z2,z3,z4,z5,z363,z7]),(0,[z55,z2,z3,z5,z157,z7]),(0,[z1,z2,z590,z3,z421,z6])],[(0,[z161,z2,z3,z4,z5,z7]),(0,[z1,z112,z3,z4,z28,z6])],[(0,[z1,z697,z3,z4,z27,z6]),(0,[z864,z2,z3,z4,z5,z6])],[(0,[z8,z1,z2,z3,z722,z6]),(0,[z865,z2,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z421,z29])],[(0,[z1,z2,z3,z866,z5,z6]),(0,[z1,z2,z3,z433,z28,z6]),(0,[z58,z2,z3,z4,z59,z6]),(0,[z8,z2,z3,z5,z185,z7]),(0,[z55,z2,z3,z467,z5,z6]),(0,[z204,z2,z3,z4,z484,z6]),(0,[z142,z2,z3,z4,z5,z25])],[(0,[z1,z2,z3,z4,z98,z662])],[(0,[z1,z2,z346,z86,z5,z6]),(0,[z342,z2,z114,z4,z5,z6]),(0,[z1,z2,z114,z4,z545,z6])],[(0,[z867,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z868,z6]),(0,[z13,z2,z3,z80,z5,z6]),(0,[z869,z1,z2,z3,z5,z6]),(0,[z1,z370,z2,z3,z412,z6]),(0,[z1,z2,z870,z3,z19,z6])],[(0,[z1,z2,z184,z86,z5,z6]),(0,[z2,z324,z4,z5,z6,z7]),(0,[z1,z2,z3,z5,z6,z871]),(0,[z1,z2,z642,z4,z38,z6]),(0,[z140,z1,z2,z3,z4,z808])],[(0,[z1,z2,z3,z4,z872,z6]),(0,[z18,z1,z2,z3,z5,z250]),(0,[z77,z2,z3,z20,z639,z6]),(0,[z77,z1,z2,z436,z5,z6]),(0,[z2,z3,z4,z267,z6,z7]),(0,[z2,z114,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z873,z6])]],
   [[(0,[z1,z375,z2,z3,z28,z6]),(0,[z1,z187,z3,z4,z433,z6]),(0,[z1,z3,z146,z28,z6,z101]),(0,[z303,z1,z2,z91,z38,z6]),(0,[z1,z2,z60,z168,z5,z6])],[(0,[z1,z2,z3,z874,z5,z6]),(0,[z2,z3,z762,z5,z6,z7]),(0,[z1,z2,z3,z875,z5,z6]),(0,[z43,z2,z3,z150,z28,z6])],[(0,[z55,z2,z3,z4,z5,z361]),(0,[z231,z2,z3,z4,z5,z7]),(0,[z93,z1,z4,z139,z5,z6]),(0,[z1,z2,z876,z3,z24,z6]),(0,[z1,z367,z3,z123,z5,z6]),(0,[z1,z2,z3,z222,z6,z25])],[(0,[z1,z2,z399,z3,z4,z6]),(0,[z428,z55,z2,z3,z5,z6]),(0,[z8,z1,z2,z3,z5,z185]),(0,[z1,z2,z3,z190,z28,z6]),(0,[z1,z2,z3,z28,z6,z25]),(0,[z1,z112,z3,z19,z5,z6])],[(0,[z203,z2,z4,z832,z5,z6]),(0,[z2,z3,z412,z5,z6,z7]),(0,[z55,z2,z114,z4,z5,z6]),(0,[z1,z2,z877,z3,z4,z6]),(0,[z1,z2,z3,z28,z6,z256]),(0,[z1,z2,z3,z878,z5,z6]),(0,[z1,z2,z241,z3,z28,z6])],[(0,[z74,z143,z3,z4,z89,z6]),(0,[z13,z1,z127,z3,z5,z6]),(0,[z879,z2,z3,z4,z5,z6]),(0,[z1,z110,z3,z378,z5,z6]),(0,[z880,z2,z3,z4,z5,z6])],[(0,[z488,z2,z3,z4,z5,z7]),(0,[z13,z14,z3,z78,z5,z6]),(0,[z49,z43,z1,z2,z5,z6]),(0,[z1,z2,z3,z298,z28,z6]),(0,[z1,z2,z3,z405,z28,z25]),(0,[z111,z2,z47,z3,z4,z6])],[(0,[z2,z3,z4,z6,z881,z233]),(0,[z140,z82,z2,z3,z4,z29]),(0,[z1,z2,z3,z5,z6,z882])],[(0,[z1,z2,z883,z3,z4,z6]),(0,[z1,z2,z3,z4,z884,z6]),(0,[z1,z2,z3,z4,z433,z6]),(0,[z106,z1,z2,z3,z28,z6]),(0,[z77,z1,z2,z3,z639,z6]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z3,z24,z846,z5,z6])],[(0,[z58,z1,z2,z329,z4,z6]),(0,[z8,z2,z3,z6,z85,z7]),(0,[z39,z1,z2,z590,z3,z6])],[(0,[z134,z2,z321,z3,z4,z6]),(0,[z58,z2,z3,z4,z150,z6]),(0,[z8,z55,z2,z3,z5,z6]),(0,[z1,z96,z3,z4,z5,z494]),(0,[z1,z96,z171,z4,z5,z6])],[(0,[z55,z2,z3,z4,z5,z675]),(0,[z1,z2,z886,z4,z5,z6]),(0,[z55,z2,z3,z4,z258,z6]),(0,[z1,z16,z3,z4,z5,z416]),(0,[z1,z2,z327,z4,z38,z6]),(0,[z1,z2,z3,z887,z5,z6]),(0,[z193,z2,z3,z298,z5,z6]),(0,[z130,z2,z47,z3,z4,z6])],[(0,[z13,z1,z2,z3,z115,z6]),(0,[z888,z2,z3,z4,z5,z33]),(0,[z2,z3,z4,z889,z5,z6])],[(0,[z63,z2,z47,z83,z4,z6]),(0,[z13,z2,z144,z78,z5,z6]),(0,[z318,z2,z3,z4,z28,z6]),(0,[z2,z3,z4,z5,z6,z890]),(0,[z1,z2,z91,z467,z38,z6]),(1,[z1,z367,z4,z5,z102]),(0,[z122,z1,z2,z4,z292,z102]),(0,[z1,z2,z3,z19,z5,z804])],[(0,[z58,z1,z2,z3,z168,z6]),(0,[z1,z2,z784,z3,z371,z6]),(0,[z43,z1,z2,z86,z28,z6]),(0,[z891,z2,z3,z5,z6,z243])],[(0,[z2,z3,z4,z258,z6,z7]),(0,[z35,z1,z3,z4,z5,z845]),(0,[z1,z2,z558,z3,z28,z6]),(0,[z15,z1,z110,z4,z5,z6])]],
   [[(0,[z96,z3,z4,z5,z36,z7]),(0,[z1,z2,z3,z371,z892,z6])],[(0,[z1,z2,z4,z893,z5,z6]),(0,[z1,z2,z3,z894,z5,z6]),(0,[z1,z2,z3,z4,z745,z6]),(0,[z1,z2,z4,z742,z5,z6]),(0,[z93,z1,z2,z86,z28,z6]),(0,[z93,z1,z391,z4,z5,z6]),(0,[z1,z2,z590,z3,z28,z6])],[(0,[z1,z2,z3,z467,z5,z6]),(0,[z895,z2,z3,z4,z5,z6])],[(0,[z1,z2,z83,z86,z28,z6]),(0,[z1,z3,z4,z94,z5,z416]),(0,[z2,z3,z19,z150,z28,z6])],[(0,[z1,z2,z144,z4,z116,z6]),(0,[z1,z2,z3,z4,z896,z6]),(0,[z1,z110,z3,z4,z5,z6])],[(0,[z1,z2,z897,z3,z4,z6]),(0,[z898,z1,z2,z3,z5,z6]),(0,[z43,z1,z2,z3,z116,z6]),(0,[z2,z3,z4,z326,z6,z85]),(0,[z351,z2,z47,z3,z4,z6]),(0,[z318,z2,z3,z368,z5,z6]),(0,[z703,z1,z4,z94,z5,z6]),(0,[z1,z360,z47,z3,z4,z6])],[(0,[z2,z3,z4,z899,z6,z7]),(0,[z255,z2,z3,z388,z4,z6]),(0,[z55,z127,z3,z4,z5,z6]),(0,[z303,z55,z2,z3,z5,z6]),(0,[z629,z1,z2,z4,z5,z102])],[(0,[z74,z143,z3,z4,z5,z6]),(0,[z37,z2,z92,z4,z6,z7]),(0,[z1,z2,z3,z28,z6,z497]),(0,[z1,z2,z900,z3,z4,z6]),(0,[z122,z1,z2,z123,z5,z102])],[(0,[z435,z63,z2,z83,z5,z6]),(0,[z1,z2,z3,z4,z901,z6]),(0,[z1,z360,z3,z421,z5,z6])],[(0,[z1,z2,z902,z3,z4,z6]),(0,[z1,z2,z47,z329,z4,z6])],[(0,[z34,z3,z4,z109,z6,z7]),(0,[z903,z2,z3,z4,z5,z6]),(0,[z904,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z905,z5,z6]),(0,[z906,z1,z2,z3,z5,z6]),(0,[z1,z2,z907,z4,z5,z6]),(0,[z15,z908,z1,z2,z5,z6]),(0,[z909,z1,z2,z3,z5,z6]),(0,[z1,z2,z910,z4,z5,z6])],[(0,[z178,z2,z3,z4,z210,z6]),(0,[z58,z255,z2,z3,z4,z6])],[(0,[z1,z2,z3,z911,z5,z6]),(0,[z55,z2,z3,z441,z5,z6])],[(0,[z2,z3,z4,z433,z6,z7]),(0,[z2,z3,z912,z5,z6,z7]),(0,[z1,z2,z3,z4,z913,z6]),(0,[z1,z26,z3,z4,z914,z6]),(0,[z122,z1,z2,z47,z4,z102]),(0,[z97,z1,z2,z198,z4,z6]),(0,[z1,z2,z3,z28,z6,z316]),(0,[z1,z2,z47,z3,z168,z6])],[(0,[z1,z915,z3,z4,z5,z6]),(0,[z1,z2,z3,z916,z5,z6]),(0,[z2,z3,z86,z28,z6,z7]),(0,[z2,z47,z3,z4,z7,z25]),(0,[z2,z917,z3,z5,z6,z7]),(0,[z1,z16,z23,z4,z28,z6]),(0,[z1,z3,z4,z5,z845,z101]),(0,[z1,z2,z3,z4,z918,z6])]],
   [[(0,[z8,z919,z3,z5,z6,z7]),(0,[z181,z55,z2,z3,z28,z6]),(0,[z1,z2,z3,z920,z5,z6]),(0,[z1,z2,z47,z3,z225,z6]),(0,[z1,z921,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z922]),(0,[z1,z2,z3,z28,z6,z524])],[(0,[z203,z2,z4,z384,z5,z6]),(0,[z77,z2,z3,z748,z5,z6]),(0,[z2,z3,z4,z5,z33,z7]),(0,[z55,z923,z3,z4,z5,z6]),(0,[z1,z2,z900,z3,z368,z6]),(0,[z1,z2,z3,z86,z586,z6]),(0,[z1,z2,z3,z115,z6,z25]),(0,[z1,z380,z3,z4,z28,z6])],[(0,[z1,z2,z3,z4,z924,z6]),(0,[z8,z77,z2,z3,z5,z6]),(0,[z1,z2,z436,z4,z267,z6]),(0,[z925,z2,z3,z4,z5,z6]),(0,[z657,z1,z2,z3,z28,z6])],[(0,[z1,z2,z926,z3,z4,z6]),(0,[z161,z2,z3,z5,z157,z7]),(0,[z389,z2,z332,z4,z5,z6]),(0,[z1,z110,z3,z24,z5,z6])],[(0,[z39,z1,z14,z3,z5,z6]),(0,[z1,z2,z144,z4,z28,z6]),(0,[z2,z3,z368,z5,z6,z7]),(0,[z927,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z928,z5,z6]),(0,[z53,z2,z47,z3,z4,z6])],[(0,[z2,z3,z4,z5,z416,z7]),(0,[z2,z3,z4,z5,z7,z25]),(0,[z43,z1,z2,z3,z28,z6]),(0,[z1,z2,z929,z4,z5,z6])],[(0,[z1,z2,z930,z3,z5,z6]),(0,[z1,z2,z151,z86,z28,z6]),(0,[z193,z380,z3,z4,z5,z6]),(0,[z1,z2,z931,z3,z4,z6])],[(0,[z932,z2,z3,z5,z6,z7]),(0,[z93,z1,z4,z94,z5,z6]),(0,[z49,z1,z2,z86,z5,z6]),(0,[z53,z2,z3,z421,z5,z6])],[(0,[z933,z1,z2,z3,z4,z6]),(0,[z8,z1,z2,z828,z5,z6]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z178,z2,z3,z4,z284,z6])],[(0,[z1,z2,z3,z4,z5,z935]),(0,[z936,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z123,z937,z6])],[(0,[z1,z2,z3,z938,z5,z6]),(0,[z1,z3,z4,z109,z914,z6]),(0,[z939,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z5,z352]),(0,[z1,z167,z47,z3,z4,z6])],[(0,[z1,z2,z3,z4,z411,z6]),(0,[z1,z2,z3,z4,z940,z6]),(0,[z1,z2,z324,z5,z28,z6]),(0,[z859,z2,z3,z5,z6,z7]),(0,[z1,z2,z3,z4,z941,z6])],[(0,[z2,z3,z4,z506,z5,z7]),(0,[z2,z3,z4,z5,z257,z7]),(0,[z2,z3,z4,z5,z608,z7]),(0,[z1,z2,z3,z942,z5,z6]),(0,[z178,z2,z3,z4,z293,z6])],[(0,[z1,z2,z171,z4,z28,z6]),(0,[z1,z367,z47,z3,z4,z6]),(0,[z1,z167,z3,z421,z5,z6])],[(0,[z730,z2,z3,z4,z6,z7]),(0,[z55,z2,z329,z4,z5,z6]),(0,[z93,z1,z4,z263,z5,z6]),(0,[z1,z127,z3,z4,z5,z6]),(0,[z1,z2,z943,z4,z5,z6]),(0,[z46,z1,z3,z4,z109,z6]),(0,[z142,z2,z3,z4,z258,z6])],[(0,[z768,z72,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z28,z6]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z161,z255,z2,z3,z4,z7]),(0,[z2,z3,z4,z5,z517,z7]),(0,[z2,z3,z4,z28,z6,z217]),(0,[z1,z2,z3,z168,z98,z6])]],
   [[(0,[z932,z1,z2,z3,z5,z6]),(0,[z2,z3,z4,z78,z5,z250]),(0,[z2,z3,z5,z185,z7,z25])],[(0,[z2,z3,z4,z5,z6,z945]),(0,[z2,z3,z4,z5,z6,z946]),(0,[z318,z2,z3,z4,z5,z33]),(0,[z947,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z948,z5,z6]),(0,[z949,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z950,z5,z6]),(0,[z1,z2,z327,z86,z28,z6]),(0,[z951,z2,z3,z4,z5,z6]),(0,[z1,z2,z952,z3,z123,z6]),(0,[z1,z2,z3,z421,z28,z6]),(0,[z39,z1,z2,z710,z3,z6])],[(0,[z178,z2,z3,z4,z116,z6]),(0,[z106,z2,z3,z4,z5,z7]),(0,[z2,z3,z4,z953,z28,z6]),(0,[z1,z2,z47,z3,z412,z6]),(0,[z111,z2,z3,z4,z222,z6])],[(0,[z55,z2,z3,z4,z433,z6]),(0,[z428,z1,z2,z3,z28,z6]),(0,[z55,z2,z91,z4,z38,z6]),(0,[z1,z2,z378,z86,z5,z6]),(0,[z1,z2,z954,z3,z4,z6]),(0,[z193,z2,z47,z3,z4,z6]),(0,[z1,z2,z47,z955,z4,z6])],[(0,[z1,z2,z3,z4,z956,z6]),(0,[z1,z2,z3,z371,z484,z6]),(0,[z1,z96,z3,z4,z28,z36])],[(0,[z1,z2,z3,z441,z5,z6]),(0,[z8,z1,z919,z3,z5,z6]),(0,[z2,z3,z4,z28,z6,z233]),(0,[z957,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z912,z5,z6]),(0,[z1,z2,z599,z3,z28,z6]),(0,[z1,z2,z452,z3,z28,z6])],[(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z2,z3,z959,z5,z6]),(0,[z960,z2,z3,z4,z28,z6])],[(0,[z1,z2,z3,z961,z5,z6]),(0,[z1,z14,z324,z4,z5,z6]),(0,[z1,z2,z3,z146,z5,z250]),(0,[z8,z255,z2,z3,z5,z6]),(0,[z15,z43,z55,z2,z5,z6]),(0,[z1,z2,z3,z283,z28,z6]),(0,[z196,z2,z47,z3,z4,z6]),(0,[z111,z2,z269,z4,z5,z6])],[(0,[z2,z3,z192,z5,z6,z7]),(0,[z1,z923,z3,z4,z5,z6]),(0,[z2,z3,z421,z5,z6,z7]),(0,[z1,z2,z3,z580,z28,z6]),(0,[z204,z2,z3,z4,z28,z6]),(0,[z182,z1,z2,z3,z28,z6]),(0,[z1,z2,z367,z4,z5,z102])],[(0,[z134,z2,z3,z4,z628,z6]),(0,[z2,z47,z3,z4,z185,z7]),(0,[z2,z3,z19,z5,z185,z7]),(0,[z8,z1,z2,z3,z28,z6]),(0,[z122,z55,z2,z4,z5,z102]),(0,[z459,z1,z3,z4,z109,z6]),(0,[z1,z2,z3,z4,z962,z6]),(0,[z1,z963,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z7,z500]),(0,[z1,z2,z3,z964,z5,z6]),(0,[z1,z367,z3,z4,z292,z6])],[(0,[z1,z2,z965,z4,z5,z6]),(0,[z1,z2,z171,z225,z5,z6])],[(0,[z1,z2,z4,z832,z5,z6]),(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z967,z3,z4,z5,z6])],[(0,[z2,z3,z123,z5,z6,z7]),(0,[z111,z2,z410,z4,z5,z6])],[(0,[z13,z1,z2,z144,z28,z6]),(0,[z1,z2,z691,z86,z5,z6]),(0,[z55,z110,z3,z4,z5,z6]),(0,[z37,z1,z2,z198,z4,z6])]],
   [[(0,[z435,z1,z968,z3,z5,z6]),(0,[z1,z2,z3,z4,z969,z6]),(0,[z970,z2,z3,z4,z28,z6])],[(0,[z1,z2,z971,z3,z4,z6]),(0,[z1,z96,z3,z146,z28,z6]),(0,[z1,z2,z3,z4,z972,z6]),(0,[z18,z1,z2,z3,z28,z25]),(0,[z1,z112,z3,z4,z258,z6]),(0,[z1,z2,z590,z3,z19,z185])],[(0,[z134,z53,z2,z3,z4,z6]),(0,[z2,z3,z4,z973,z28,z6]),(0,[z8,z1,z2,z3,z6,z85]),(0,[z34,z1,z3,z4,z345,z6]),(0,[z178,z2,z3,z4,z28,z6]),(0,[z974,z2,z3,z4,z28,z6])],[(0,[z137,z768,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z975,z6]),(0,[z2,z3,z4,z822,z5,z6]),(0,[z1,z22,z379,z3,z24,z6]),(0,[z1,z976,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z28,z25])],[(0,[z74,z768,z3,z4,z5,z6]),(0,[z1,z968,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z107,z6])],[(0,[z977,z2,z3,z4,z5,z6]),(0,[z303,z1,z2,z3,z28,z6]),(0,[z1,z2,z3,z978,z5,z6]),(0,[z1,z2,z329,z4,z5,z6]),(0,[z1,z2,z3,z123,z28,z6]),(0,[z2,z3,z4,z28,z6,z186])],[(0,[z1,z2,z3,z4,z979,z6]),(0,[z13,z1,z2,z410,z5,z6]),(0,[z58,z2,z3,z59,z441,z6]),(0,[z18,z2,z3,z5,z7,z25]),(0,[z980,z2,z3,z4,z5,z6]),(0,[z981,z2,z3,z4,z28,z6])],[(0,[z1,z187,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z982,z6]),(0,[z2,z3,z4,z116,z6,z7]),(0,[z589,z1,z2,z3,z441,z6]),(0,[z204,z2,z3,z225,z5,z6]),(0,[z1,z2,z3,z476,z28,z6]),(0,[z1,z2,z127,z3,z28,z6])],[(0,[z435,z1,z2,z86,z5,z6]),(0,[z1,z2,z644,z3,z28,z6]),(0,[z2,z3,z4,z6,z983,z7]),(0,[z55,z2,z3,z4,z266,z6])],[(0,[z2,z3,z371,z5,z6,z7])],[(0,[z1,z2,z3,z4,z5,z984]),(0,[z1,z2,z3,z4,z985,z6]),(0,[z1,z2,z986,z4,z5,z6]),(0,[z1,z2,z91,z4,z38,z6]),(0,[z193,z2,z3,z123,z5,z6]),(0,[z2,z3,z4,z987,z28,z6]),(0,[z234,z1,z2,z47,z3,z6])],[(0,[z13,z1,z2,z3,z28,z250]),(0,[z2,z3,z4,z5,z6,z988]),(0,[z989,z1,z2,z3,z4,z6])],[(0,[z37,z1,z2,z617,z4,z6]),(0,[z566,z2,z3,z4,z150,z6]),(0,[z1,z2,z3,z299,z28,z6])],[(0,[z1,z2,z3,z378,z107,z6]),(0,[z278,z1,z2,z3,z28,z6]),(0,[z1,z2,z3,z246,z28,z6])],[(0,[z74,z143,z3,z129,z5,z6]),(0,[z1,z2,z990,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z991,z5,z6]),(0,[z1,z14,z3,z4,z116,z6]),(0,[z1,z2,z3,z4,z5,z416]),(0,[z992,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z719,z2,z3,z4,z5,z6])],[(0,[z1,z994,z2,z3,z192,z6]),(0,[z995,z2,z3,z4,z5,z6]),(0,[z178,z2,z3,z24,z28,z6]),(0,[z1,z2,z3,z618,z28,z6]),(0,[z1,z2,z643,z3,z28,z6]),(0,[z1,z2,z3,z5,z185,z804])],[(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z2,z3,z378,z266,z6]),(0,[z1,z2,z47,z3,z4,z33])],[(0,[z74,z577,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z1,z2,z3,z998,z5,z6]),(0,[z1,z2,z999,z3,z4,z6]),(0,[z1,z2,z1000,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1001]),(0,[z919,z3,z4,z5,z6,z7]),(0,[z1,z2,z876,z3,z28,z6]),(1,[z1,z3,z4,z5,z845]),(0,[z1,z127,z3,z5,z6,z25]),(0,[z629,z1,z2,z3,z4,z29])],[(0,[z15,z43,z1,z2,z5,z6]),(0,[z2,z3,z4,z5,z6,z739]),(0,[z2,z3,z4,z28,z6,z243])],[(0,[z55,z2,z3,z4,z411,z6]),(0,[z1,z1002,z3,z4,z5,z6]),(0,[z1,z2,z3,z1003,z5,z6]),(0,[z1,z2,z3,z4,z1004,z6])],[(0,[z1,z2,z3,z4,z1005,z6]),(0,[z435,z2,z3,z5,z6,z7]),(0,[z1,z187,z3,z24,z5,z6]),(0,[z178,z2,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z1006,z6])],[(0,[z207,z2,z3,z4,z5,z6]),(0,[z2,z269,z4,z5,z6,z7]),(0,[z1007,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z267,z6]),(0,[z35,z342,z3,z4,z5,z101])],[(0,[z2,z567,z3,z4,z6,z7]),(0,[z160,z1,z4,z94,z5,z6]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1009,z5,z6]),(0,[z82,z2,z47,z3,z4,z6]),(0,[z18,z1,z2,z410,z5,z25])],[(0,[z1,z2,z3,z129,z924,z6]),(0,[z13,z2,z324,z78,z5,z6]),(0,[z8,z2,z3,z59,z5,z6]),(0,[z1,z2,z3,z146,z322,z6])],[(0,[z535,z577,z3,z4,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1010]),(0,[z15,z43,z1,z127,z5,z6]),(0,[z1,z127,z3,z4,z302,z6]),(0,[z2,z3,z4,z150,z28,z6]),(0,[z82,z2,z3,z421,z5,z6])],[(0,[z1,z2,z1011,z3,z4,z6]),(0,[z8,z2,z738,z5,z6,z7]),(0,[z1,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z4,z107,z416]),(0,[z1,z2,z3,z11,z28,z6]),(0,[z1,z2,z1012,z4,z5,z6]),(0,[z1013,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1014,z5,z6])],[(0,[z1,z2,z3,z1015,z5,z6]),(0,[z106,z2,z3,z5,z157,z7]),(0,[z1,z2,z3,z1016,z5,z6])],[(0,[z134,z2,z3,z4,z210,z6]),(0,[z2,z44,z4,z5,z45,z7]),(0,[z55,z2,z1017,z4,z5,z6]),(0,[z2,z3,z5,z6,z882,z243])]],
   [[(0,[z435,z1,z2,z3,z5,z6]),(0,[z1,z14,z3,z4,z28,z6]),(0,[z55,z2,z44,z4,z5,z45]),(0,[z1018,z2,z3,z4,z5,z6]),(0,[z1019,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z292,z6]),(0,[z1,z2,z269,z4,z28,z6]),(0,[z1,z195,z3,z4,z222,z6])],[(0,[z1,z2,z1020,z3,z4,z6]),(0,[z143,z3,z4,z5,z6,z520]),(0,[z1,z2,z3,z1021,z5,z6]),(0,[z58,z53,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z266,z6]),(0,[z1,z2,z3,z4,z266,z416]),(1,[z1,z3,z4,z914,z6])],[(0,[z1,z2,z3,z1022,z5,z6]),(0,[z1,z2,z3,z4,z1023,z6]),(0,[z55,z2,z47,z3,z4,z7]),(0,[z1,z2,z3,z28,z6,z157]),(0,[z49,z1,z2,z379,z4,z6]),(0,[z1,z2,z171,z4,z5,z36]),(0,[z1,z2,z3,z4,z1024,z6])],[(0,[z1,z2,z3,z129,z411,z6]),(0,[z1,z2,z3,z4,z99,z277]),(0,[z1,z2,z3,z412,z28,z6]),(0,[z1,z392,z3,z24,z5,z6])],[(0,[z1,z2,z3,z4,z1025,z6]),(0,[z187,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z28,z7,z25]),(0,[z1,z2,z3,z538,z28,z6]),(0,[z178,z2,z3,z4,z109,z6])],[(0,[z1,z22,z3,z24,z267,z6])],[(0,[z1,z3,z4,z484,z6,z101]),(0,[z1,z2,z103,z3,z467,z6]),(0,[z1,z2,z590,z3,z4,z6]),(0,[z1,z2,z410,z4,z28,z6]),(0,[z1,z195,z269,z4,z5,z6]),(0,[z1,z2,z3,z19,z222,z6])],[],[(0,[z1,z2,z3,z1026,z5,z6]),(0,[z1,z2,z3,z4,z433,z250]),(0,[z13,z2,z3,z5,z6,z186]),(0,[z1,z2,z3,z1027,z5,z6]),(0,[z1,z2,z3,z146,z354,z6]),(0,[z122,z1,z2,z4,z5,z750])],[(0,[z55,z2,z3,z4,z89,z6]),(0,[z1,z2,z3,z4,z5,z1028]),(0,[z13,z1,z2,z324,z28,z6]),(0,[z764,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z665,z28,z6]),(1,[z1,z2,z4,z5,z750]),(0,[z1029,z2,z3,z4,z28,z6]),(0,[z140,z1,z2,z3,z4,z29]),(0,[z1,z2,z3,z4,z99,z808])],[(0,[z1,z2,z3,z4,z1030,z6]),(0,[z49,z1,z2,z378,z5,z6]),(0,[z43,z178,z2,z3,z5,z6]),(0,[z122,z1,z2,z4,z28,z102])],[(0,[z1,z2,z3,z1031,z5,z6]),(0,[z77,z1,z2,z3,z267,z6]),(0,[z344,z1,z3,z146,z5,z6]),(0,[z1,z2,z44,z86,z28,z6])],[(1,[z768,z3,z4,z5,z6]),(0,[z13,z2,z3,z427,z5,z6]),(0,[z55,z2,z3,z378,z5,z6]),(0,[z1,z4,z94,z5,z101,z102]),(0,[z1,z2,z436,z5,z28,z6]),(0,[z1,z26,z328,z3,z4,z6]),(0,[z1,z2,z47,z44,z4,z45])],[(0,[z55,z2,z3,z4,z5,z619]),(0,[z13,z2,z3,z28,z6,z7]),(0,[z8,z2,z3,z5,z6,z206]),(0,[z1,z2,z3,z19,z5,z517]),(0,[z1,z1032,z3,z4,z5,z6]),(0,[z178,z2,z241,z3,z28,z6]),(0,[z1033,z2,z3,z4,z5,z6])],[(1,[z1,z14,z3,z28,z6]),(0,[z15,z43,z1,z2,z47,z6]),(0,[z1,z2,z3,z4,z1034,z6])],[(0,[z74,z176,z3,z4,z5,z6]),(0,[z2,z3,z6,z85,z157,z7]),(0,[z1,z2,z3,z368,z1035,z6]),(0,[z1,z2,z1036,z3,z4,z6])]],
   [[(0,[z435,z1,z2,z144,z5,z6]),(0,[z1,z2,z3,z901,z28,z6]),(0,[z1,z2,z1037,z4,z5,z6])],[],[(0,[z680,z1,z2,z3,z28,z6]),(0,[z13,z2,z3,z78,z116,z6]),(0,[z2,z47,z3,z28,z6,z7]),(0,[z1,z1038,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1039]),(0,[z342,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1040,z6]),(0,[z55,z187,z3,z4,z5,z6]),(0,[z2,z3,z4,z85,z7,z25]),(0,[z1,z2,z3,z4,z1041,z6]),(0,[z1,z2,z3,z371,z28,z6]),(0,[z1,z2,z3,z4,z586,z6]),(0,[z15,z43,z1,z110,z5,z6])],[(0,[z1,z2,z883,z3,z129,z6]),(0,[z1,z2,z47,z3,z166,z6]),(0,[z2,z3,z4,z5,z7,z473]),(0,[z2,z590,z3,z4,z6,z7]),(0,[z1,z612,z23,z4,z5,z6]),(0,[z1,z356,z3,z4,z27,z6]),(0,[z1,z2,z4,z5,z750,z102]),(0,[z162,z1,z2,z3,z4,z262])],[(0,[z1,z2,z3,z4,z1042,z6]),(0,[z134,z2,z3,z4,z116,z6]),(0,[z2,z3,z4,z5,z6,z1043]),(0,[z1,z2,z3,z1044,z5,z6]),(0,[z703,z1,z3,z4,z5,z101])],[(0,[z2,z3,z4,z354,z6,z7]),(0,[z1,z2,z3,z4,z6,z862]),(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z2,z229,z4,z38,z6]),(0,[z130,z2,z3,z4,z28,z6]),(0,[z53,z360,z3,z4,z5,z6])],[(0,[z1,z2,z1017,z4,z5,z6]),(0,[z1,z2,z3,z4,z1046,z6]),(0,[z757,z2,z3,z4,z5,z185]),(0,[z1,z195,z47,z3,z4,z6])],[(0,[z137,z72,z47,z3,z4,z6]),(0,[z8,z2,z3,z28,z6,z7]),(0,[z1,z2,z3,z412,z27,z6]),(0,[z272,z1,z2,z3,z28,z6]),(0,[z1,z2,z44,z4,z5,z45])],[(0,[z1,z1047,z3,z4,z5,z6]),(0,[z77,z2,z3,z4,z5,z250]),(0,[z13,z453,z2,z3,z5,z6]),(0,[z77,z1,z2,z3,z222,z6]),(0,[z49,z1,z2,z4,z5,z6]),(0,[z1,z110,z4,z86,z5,z6]),(0,[z1,z367,z44,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1048,z6]),(0,[z1049,z2,z3,z4,z5,z6]),(0,[z145,z1,z3,z146,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z436,z5,z6]),(0,[z1,z96,z3,z4,z484,z6])],[(0,[z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z1051,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z55,z2,z3,z4,z5,z416]),(0,[z1053,z2,z3,z4,z5,z6]),(0,[z1054,z1,z2,z3,z5,z6]),(0,[z689,z1,z3,z4,z109,z6]),(0,[z1,z2,z60,z4,z5,z6]),(0,[z1,z1055,z3,z4,z5,z6])],[(0,[z2,z3,z4,z1056,z6,z7]),(0,[z1057,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z664,z7]),(0,[z1,z1058,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1059])],[(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z2,z1061,z4,z5,z6]),(0,[z1,z3,z4,z914,z27,z6]),(0,[z1062,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z187,z3,z129,z5,z6]),(0,[z2,z3,z4,z671,z5,z7]),(0,[z1,z2,z1063,z4,z5,z6]),(0,[z351,z2,z3,z4,z28,z6]),(0,[z390,z1,z2,z3,z4,z29]),(0,[z1,z360,z3,z4,z28,z6]),(0,[z891,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z89,z6]),(0,[z1,z2,z1064,z4,z5,z6]),(0,[z2,z3,z5,z6,z7,z1010]),(0,[z8,z2,z3,z326,z5,z6]),(0,[z751,z1,z2,z3,z4,z6])],[(0,[z55,z2,z3,z166,z5,z6]),(0,[z1,z2,z3,z1065,z5,z6]),(0,[z13,z2,z3,z78,z28,z6]),(0,[z343,z1,z3,z146,z5,z6]),(0,[z1,z2,z3,z4,z1066,z6]),(0,[z1,z2,z3,z4,z98,z99])],[(0,[z317,z72,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z185,z7]),(0,[z2,z3,z4,z5,z6,z1067]),(0,[z55,z2,z3,z4,z149,z6]),(0,[z1,z2,z3,z4,z5,z1068])],[(0,[z1,z2,z3,z378,z5,z6]),(0,[z1,z2,z3,z378,z5,z416]),(0,[z1,z2,z1069,z3,z4,z6]),(0,[z178,z2,z3,z146,z5,z6]),(0,[z193,z2,z3,z4,z292,z6])],[(0,[z309,z2,z4,z125,z5,z6]),(0,[z1,z2,z3,z411,z192,z6]),(0,[z2,z3,z4,z65,z6,z7]),(0,[z255,z2,z3,z4,z6,z507]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z1,z110,z3,z4,z302,z6]),(0,[z549,z1,z2,z3,z28,z6])],[(0,[z1,z669,z3,z146,z5,z6]),(0,[z8,z2,z3,z722,z6,z7]),(0,[z8,z2,z3,z1071,z6,z7]),(0,[z1,z1072,z3,z4,z5,z6]),(0,[z1,z2,z230,z3,z28,z6]),(0,[z140,z1,z360,z3,z4,z29])],[(0,[z1073,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z129,z5,z6]),(0,[z351,z2,z3,z368,z5,z6]),(0,[z1,z2,z4,z5,z6,z750]),(0,[z516,z1,z3,z4,z345,z6])],[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z2,z3,z5,z185,z250]),(0,[z145,z1,z3,z846,z5,z6]),(0,[z1,z2,z198,z86,z28,z6]),(0,[z1,z367,z4,z5,z6,z102]),(0,[z1,z2,z199,z3,z28,z6]),(0,[z1,z2,z47,z410,z4,z6])],[(0,[z1,z2,z47,z3,z427,z6]),(0,[z2,z3,z5,z6,z871,z233])],[(0,[z55,z77,z2,z3,z28,z6]),(0,[z55,z2,z3,z4,z639,z6]),(0,[z8,z255,z1,z2,z3,z6]),(0,[z1,z3,z4,z5,z36,z845]),(0,[z18,z1,z2,z3,z258,z25]),(0,[z53,z167,z3,z4,z5,z6])],[(0,[z1,z1075,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z28,z6])],[(0,[z134,z2,z3,z4,z6,z85])],[],[(0,[z161,z2,z47,z3,z4,z7]),(0,[z1,z1076,z3,z4,z5,z6]),(0,[z1077,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z298,z918,z6]),(0,[z53,z2,z3,z4,z28,z6])]],
   [[(0,[z2,z768,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z39,z1,z2,z3,z5,z250]),(0,[z2,z3,z4,z6,z833,z7]),(0,[z2,z1079,z3,z4,z6,z7]),(0,[z255,z2,z3,z6,z157,z7]),(0,[z1,z2,z3,z1080,z5,z6])],[(0,[z2,z3,z4,z832,z5,z6]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z55,z2,z590,z3,z4,z6]),(0,[z1,z502,z23,z4,z5,z6]),(0,[z1,z2,z3,z28,z6,z608])],[(0,[z2,z3,z4,z6,z85,z7])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z5,z25]),(0,[z1,z2,z3,z4,z1081,z6]),(0,[z93,z1,z423,z4,z5,z6]),(0,[z1,z1082,z3,z4,z5,z6]),(0,[z1,z2,z3,z131,z28,z6]),(0,[z386,z2,z3,z4,z28,z6])],[(0,[z272,z2,z4,z125,z5,z6]),(0,[z93,z1,z368,z94,z5,z6]),(0,[z1083,z2,z3,z4,z5,z6]),(0,[z35,z1,z3,z4,z5,z101]),(0,[z37,z1,z2,z92,z4,z6])],[(0,[z112,z3,z4,z5,z6,z7]),(0,[z725,z2,z3,z4,z5,z6]),(0,[z1084,z2,z3,z5,z6,z233]),(0,[z1085,z1,z2,z3,z5,z6])],[(0,[z1,z2,z1086,z3,z4,z6]),(0,[z1,z2,z144,z4,z433,z6]),(0,[z342,z2,z3,z4,z545,z6]),(0,[z1,z367,z3,z4,z5,z45])],[(0,[z8,z255,z2,z3,z6,z7]),(0,[z365,z2,z3,z4,z575,z6]),(0,[z2,z3,z4,z5,z6,z1087]),(0,[z2,z3,z4,z5,z6,z1088])],[(0,[z1,z367,z3,z4,z28,z6]),(0,[z2,z3,z4,z28,z6,z1089])],[(0,[z1,z2,z3,z4,z1071,z6]),(0,[z55,z2,z3,z19,z5,z185]),(0,[z1,z2,z3,z4,z1090,z6])],[(0,[z334,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z166,z5,z6]),(0,[z55,z2,z567,z3,z4,z6]),(0,[z1,z2,z1091,z4,z5,z6])],[(0,[z63,z2,z83,z4,z28,z6]),(0,[z14,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z748,z5,z6]),(0,[z1,z2,z24,z436,z28,z6]),(0,[z1,z2,z3,z4,z149,z6])],[(0,[z1,z2,z3,z4,z1092,z6])],[(0,[z15,z435,z1,z2,z5,z6]),(1,[z8,z255,z2,z3,z6]),(0,[z2,z3,z4,z5,z6,z1093]),(0,[z193,z367,z3,z4,z5,z6]),(0,[z1,z2,z3,z604,z28,z6])],[(0,[z203,z2,z4,z125,z28,z6]),(0,[z142,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z5,z277]),(0,[z1,z2,z47,z3,z6,z157]),(0,[z55,z2,z3,z4,z545,z6]),(0,[z55,z2,z3,z4,z586,z6]),(0,[z741,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1094,z5,z6]),(0,[z1,z2,z3,z1095,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z1096]),(0,[z1,z2,z47,z3,z699,z6]),(0,[z1,z2,z3,z4,z1097,z6]),(0,[z2,z47,z3,z4,z6,z1098])],[(0,[z1,z14,z3,z4,z5,z361]),(0,[z1,z2,z3,z86,z5,z250]),(0,[z1,z2,z3,z368,z28,z6]),(0,[z1,z356,z3,z146,z5,z6]),(0,[z39,z1,z2,z3,z302,z6]),(0,[z1099,z2,z3,z4,z5,z6])],[(0,[z216,z2,z3,z4,z5,z6]),(0,[z1,z1100,z3,z4,z5,z6]),(0,[z2,z1101,z3,z4,z6,z7]),(0,[z34,z55,z3,z4,z109,z6]),(0,[z2,z47,z3,z4,z6,z233]),(0,[z989,z2,z3,z4,z6,z217])],[(0,[z1,z2,z3,z4,z639,z6]),(0,[z2,z379,z3,z4,z6,z7]),(0,[z140,z2,z3,z4,z7,z29]),(0,[z196,z2,z3,z4,z28,z6])],[(0,[z1,z2,z324,z4,z116,z6]),(0,[z1,z2,z1102,z4,z5,z6]),(0,[z351,z3,z4,z146,z5,z6]),(0,[z351,z2,z3,z4,z5,z33]),(0,[z49,z1,z4,z146,z5,z6]),(0,[z1,z2,z86,z5,z6,z500]),(0,[z39,z1,z2,z47,z3,z6])],[(0,[z428,z1,z2,z3,z433,z6]),(0,[z2,z3,z4,z5,z117,z7]),(0,[z1,z22,z24,z436,z5,z6]),(0,[z1,z2,z3,z4,z1103,z6]),(0,[z37,z1,z2,z1012,z4,z6]),(0,[z1,z1104,z3,z4,z5,z6])],[(0,[z1,z2,z3,z192,z28,z6]),(0,[z1,z2,z1105,z4,z5,z6]),(0,[z43,z2,z3,z28,z6,z7]),(0,[z55,z2,z60,z4,z5,z6]),(0,[z145,z1,z3,z146,z65,z6]),(0,[z1,z282,z3,z4,z5,z36]),(0,[z162,z178,z2,z3,z4,z6]),(0,[z2,z3,z4,z5,z6,z1098])],[(0,[z1,z1106,z3,z4,z5,z6]),(0,[z2,z3,z24,z5,z7,z25]),(0,[z55,z2,z3,z4,z65,z6])],[(0,[z2,z3,z4,z5,z6,z233]),(0,[z1,z2,z3,z4,z1107,z6]),(0,[z1,z187,z3,z4,z5,z250]),(0,[z1,z2,z144,z4,z5,z361]),(0,[z162,z1,z2,z3,z28,z25])],[(0,[z1,z2,z3,z200,z28,z6]),(0,[z2,z91,z4,z38,z6,z7]),(0,[z55,z2,z3,z4,z302,z6]),(0,[z93,z1,z86,z146,z5,z6]),(0,[z1,z2,z876,z3,z4,z6])],[(0,[z1,z1108,z3,z4,z5,z6]),(0,[z1,z96,z3,z4,z5,z670]),(0,[z2,z3,z4,z5,z6,z1109]),(0,[z216,z2,z3,z4,z149,z6]),(0,[z1,z2,z269,z4,z258,z6])],[(0,[z1,z2,z1110,z4,z5,z6]),(0,[z1,z1111,z3,z4,z28,z6]),(0,[z82,z360,z3,z4,z5,z6])],[(0,[z137,z232,z3,z4,z5,z6]),(0,[z13,z2,z3,z441,z5,z6]),(0,[z196,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z225,z484,z6]),(0,[z1,z110,z47,z3,z4,z6])],[(0,[z2,z3,z4,z89,z6,z7]),(0,[z1,z2,z3,z1112,z5,z6]),(0,[z39,z1,z2,z324,z5,z6]),(0,[z1,z2,z3,z109,z412,z6]),(0,[z1113,z1,z2,z3,z4,z6])],[(0,[z1,z2,z1114,z3,z4,z6]),(0,[z2,z3,z4,z5,z6,z1115]),(0,[z2,z3,z150,z28,z6,z25])],[(0,[z74,z143,z47,z3,z4,z6]),(0,[z1,z2,z1116,z4,z5,z6]),(0,[z8,z134,z2,z3,z5,z6]),(0,[z178,z2,z3,z28,z6,z25]),(0,[z1,z1117,z3,z4,z5,z6]),(0,[z1,z195,z410,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1118,z6]),(0,[z1,z2,z3,z4,z5,z250]),(0,[z2,z3,z4,z59,z639,z6]),(0,[z2,z3,z20,z441,z5,z6]),(0,[z1,z2,z3,z4,z1119,z6]),(0,[z43,z908,z1,z2,z5,z6]),(0,[z1,z2,z410,z4,z258,z6]),(0,[z140,z1,z2,z60,z4,z29])],[(0,[z13,z1,z2,z3,z901,z6]),(0,[z1,z112,z3,z4,z5,z6]),(0,[z1120,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1121,z28,z6]),(0,[z1122,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z5,z185])],[(0,[z462,z1,z2,z3,z28,z6]),(0,[z1,z2,z47,z3,z4,z361]),(0,[z1,z2,z436,z4,z28,z6]),(0,[z1,z2,z567,z3,z4,z6])],[(0,[z55,z2,z3,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z1123]),(0,[z2,z254,z3,z4,z6,z7]),(0,[z2,z3,z4,z1124,z5,z6]),(0,[z1,z2,z3,z4,z1125,z6]),(0,[z2,z47,z3,z4,z6,z186])],[(0,[z1,z2,z324,z4,z28,z6]),(0,[z8,z2,z47,z3,z6,z7]),(0,[z1,z23,z4,z742,z5,z6]),(0,[z1,z2,z3,z86,z267,z6]),(0,[z1,z2,z1126,z4,z5,z6]),(0,[z1,z2,z47,z3,z467,z6]),(0,[z111,z2,z3,z4,z28,z6])],[(0,[z1,z2,z3,z4,z1127,z6]),(0,[z1,z2,z3,z4,z5,z1128]),(0,[z15,z351,z2,z4,z5,z6]),(0,[z1,z2,z4,z86,z5,z416]),(0,[z1129,z2,z3,z4,z5,z6]),(0,[z1,z2,z410,z19,z5,z6])],[(0,[z63,z2,z4,z832,z5,z6]),(0,[z8,z1,z854,z3,z5,z6]),(0,[z1,z2,z3,z4,z545,z6]),(0,[z1,z2,z114,z371,z5,z6])],[(0,[z435,z1,z2,z399,z3,z6]),(0,[z449,z2,z3,z4,z59,z6]),(0,[z757,z2,z3,z4,z5,z7]),(0,[z35,z1,z3,z4,z545,z101])],[(0,[z134,z2,z3,z4,z822,z6]),(0,[z2,z3,z19,z28,z6,z7]),(0,[z165,z1,z2,z3,z28,z6])],[(0,[z1,z2,z3,z1130,z5,z6]),(0,[z1,z2,z3,z129,z89,z6]),(0,[z15,z1,z2,z378,z5,z6])],[(0,[z1,z2,z3,z1131,z5,z6]),(0,[z2,z3,z4,z6,z1132,z7]),(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z3,z1134,z5,z6]),(0,[z111,z195,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1135,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1136,z6]),(0,[z1,z2,z47,z3,z421,z6]),(0,[z1,z2,z3,z4,z5,z804])],[(0,[z1137,z1,z2,z4,z5,z6]),(0,[z16,z23,z4,z5,z6,z7]),(1,[z1,z4,z94,z5,z416]),(0,[z1,z2,z1138,z4,z5,z6]),(0,[z1,z2,z91,z4,z604,z6]),(0,[z1,z2,z3,z4,z5,z808])],[(0,[z2,z3,z4,z222,z6,z7]),(0,[z1,z2,z3,z4,z28,z33])],[(0,[z140,z1,z2,z3,z4,z606]),(0,[z1,z2,z3,z21,z28,z6]),(0,[z55,z2,z47,z3,z28,z6]),(0,[z1,z2,z3,z4,z6,z1139]),(0,[z1,z2,z1140,z4,z5,z6]),(0,[z2,z3,z4,z98,z99,z243])],[(0,[z1,z2,z3,z4,z1141,z6]),(0,[z1,z2,z3,z24,z5,z250]),(0,[z1,z2,z3,z4,z65,z6]),(0,[z204,z2,z114,z4,z5,z6]),(0,[z1,z360,z3,z168,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z209,z7]),(0,[z1,z2,z3,z4,z1142,z6]),(0,[z1,z2,z3,z298,z5,z6]),(0,[z82,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z808,z29])],[(0,[z2,z3,z4,z6,z1143,z7]),(0,[z1,z2,z3,z4,z302,z6]),(0,[z1,z2,z3,z4,z6,z800])],[(0,[z1,z2,z3,z4,z1144,z6]),(0,[z13,z142,z2,z3,z5,z6]),(0,[z1,z2,z3,z653,z28,z6]),(0,[z2,z47,z3,z4,z6,z243])],[(0,[z13,z2,z3,z78,z5,z361]),(0,[z1,z2,z1145,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z2,z3,z86,z322,z6]),(0,[z1,z2,z47,z3,z19,z185])],[(0,[z1,z1146,z3,z4,z5,z6]),(1,[z1,z2,z436,z28,z6]),(0,[z82,z2,z3,z4,z28,z6])],[(0,[z13,z2,z3,z150,z5,z6]),(0,[z2,z3,z5,z6,z7,z1096]),(0,[z1,z2,z3,z368,z5,z33])],[(0,[z55,z2,z3,z4,z5,z393]),(0,[z1,z2,z3,z4,z1147,z6]),(0,[z1,z2,z688,z86,z5,z6]),(0,[z15,z43,z1,z2,z302,z6]),(0,[z1,z127,z47,z3,z4,z6])],[(0,[z77,z2,z3,z158,z5,z6]),(0,[z134,z2,z310,z3,z4,z6]),(0,[z2,z3,z4,z5,z7,z177]),(0,[z1148,z2,z3,z4,z5,z6]),(0,[z1,z3,z171,z4,z5,z101]),(0,[z1149,z2,z3,z4,z5,z6])],[(0,[z167,z3,z4,z5,z6,z7]),(0,[z255,z55,z2,z3,z4,z6]),(0,[z15,z1,z2,z4,z5,z416]),(0,[z1,z2,z592,z4,z38,z6]),(0,[z1,z96,z3,z225,z5,z6]),(0,[z1,z2,z3,z57,z28,z6]),(0,[z1,z2,z3,z298,z149,z6])],[(0,[z1,z2,z1150,z3,z4,z6]),(0,[z1,z2,z328,z3,z28,z6])],[(0,[z407,z72,z3,z4,z5,z6]),(0,[z2,z4,z832,z125,z5,z6]),(0,[z93,z1,z4,z742,z5,z6]),(0,[z1151,z2,z3,z4,z5,z6]),(0,[z178,z2,z3,z4,z341,z6])],[(0,[z1,z2,z3,z1152,z5,z6]),(0,[z1,z2,z3,z146,z116,z6]),(0,[z8,z854,z3,z5,z6,z7]),(0,[z1,z2,z103,z3,z28,z6]),(0,[z1153,z2,z3,z5,z6,z217]),(0,[z1,z2,z1154,z4,z28,z6])],[(0,[z2,z151,z86,z5,z6,z7]),(0,[z2,z3,z4,z722,z6,z7]),(0,[z1,z2,z1155,z3,z4,z6])],[(0,[z1,z2,z3,z166,z1147,z6]),(0,[z55,z2,z3,z4,z28,z7]),(0,[z8,z142,z2,z3,z5,z6]),(0,[z351,z22,z3,z4,z5,z6])],[(0,[z1,z2,z1156,z4,z5,z6]),(0,[z1157,z1,z2,z4,z5,z6]),(0,[z1,z2,z92,z1012,z4,z6]),(0,[z53,z2,z3,z168,z5,z6]),(0,[z1,z2,z3,z1158,z5,z6])],[(0,[z1,z2,z144,z86,z5,z6]),(0,[z1159,z3,z4,z5,z6,z7]),(0,[z569,z232,z3,z4,z5,z6]),(0,[z1,z2,z3,z302,z28,z6]),(0,[z2,z3,z4,z6,z1160,z217])]],
   [[(0,[z1,z2,z3,z4,z5,z1161]),(0,[z317,z3,z4,z5,z6,z238]),(0,[z1,z16,z2,z86,z28,z6]),(0,[z1,z2,z3,z4,z914,z6])],[(0,[z1162,z2,z3,z4,z5,z6])],[(0,[z1,z14,z3,z4,z433,z6]),(0,[z465,z2,z3,z4,z5,z7]),(0,[z1,z2,z1155,z3,z378,z6]),(0,[z1,z2,z47,z3,z298,z6]),(0,[z811,z2,z3,z4,z28,z6]),(0,[z2,z3,z4,z1163,z5,z6])],[(0,[z2,z3,z166,z5,z6,z7]),(0,[z43,z1,z14,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1164]),(0,[z435,z1,z2,z47,z3,z6]),(0,[z1,z2,z3,z4,z1165,z6]),(0,[z77,z1,z112,z3,z5,z6]),(0,[z2,z3,z4,z821,z6,z7]),(0,[z318,z2,z3,z4,z107,z6]),(0,[z1,z1166,z2,z3,z4,z6]),(0,[z18,z142,z2,z3,z5,z25]),(0,[z1,z167,z3,z168,z5,z6])],[(0,[z2,z3,z129,z5,z6,z7]),(0,[z1167,z1,z2,z3,z5,z6]),(0,[z369,z1,z2,z4,z5,z102]),(0,[z1,z591,z3,z4,z27,z6]),(0,[z2,z3,z4,z1168,z5,z6])],[(0,[z1,z2,z3,z1169,z5,z6]),(0,[z1,z2,z3,z1170,z5,z6]),(0,[z702,z2,z83,z4,z5,z6]),(0,[z1,z187,z144,z4,z5,z6]),(0,[z1,z2,z1171,z3,z4,z6]),(0,[z134,z1,z360,z3,z4,z6]),(0,[z360,z3,z4,z5,z6,z7]),(0,[z1,z2,z47,z3,z28,z6])],[(0,[z77,z2,z3,z150,z28,z6]),(0,[z58,z2,z3,z4,z822,z6]),(0,[z1,z2,z3,z1172,z5,z6]),(0,[z1,z2,z3,z70,z28,z6]),(0,[z178,z2,z3,z4,z345,z6]),(0,[z1,z112,z3,z5,z6,z25])],[(0,[z1,z3,z129,z146,z5,z6]),(0,[z77,z1,z2,z3,z115,z6]),(0,[z2,z3,z4,z5,z7,z228]),(0,[z318,z2,z3,z4,z266,z6]),(0,[z1,z1173,z3,z4,z5,z6]),(0,[z1,z2,z3,z168,z28,z6]),(0,[z1,z167,z3,z4,z28,z6])],[(0,[z1,z16,z23,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1174,z6]),(0,[z1,z2,z3,z4,z5,z1175]),(0,[z255,z2,z3,z4,z6,z7]),(0,[z55,z2,z1116,z4,z5,z6]),(0,[z1,z2,z3,z1176,z5,z6]),(0,[z1,z2,z1177,z4,z5,z6])],[(0,[z1,z2,z1178,z3,z166,z6]),(0,[z55,z2,z3,z4,z5,z250]),(0,[z106,z55,z2,z3,z28,z6]),(0,[z1,z380,z3,z4,z5,z6])],[(0,[z605,z1,z2,z3,z28,z6]),(0,[z2,z171,z4,z5,z6,z7]),(0,[z55,z112,z3,z4,z5,z6]),(0,[z1,z3,z345,z146,z28,z6]),(0,[z1,z2,z870,z3,z28,z6])],[(0,[z1,z2,z14,z3,z28,z6]),(0,[z1179,z2,z3,z4,z5,z6]),(0,[z1180,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1181,z5,z6])],[(0,[z1,z2,z3,z4,z1182,z6]),(0,[z2,z3,z24,z150,z28,z6])],[(0,[z2,z930,z3,z5,z6,z7]),(0,[z2,z47,z3,z4,z6,z217])]],
   [[(0,[z1,z187,z47,z3,z4,z6]),(0,[z2,z3,z748,z78,z5,z6]),(0,[z2,z3,z150,z441,z5,z6]),(0,[z1,z2,z3,z4,z1183,z6]),(0,[z1,z2,z114,z4,z484,z6]),(0,[z1,z2,z151,z86,z5,z6]),(0,[z1,z2,z3,z467,z38,z6])],[(0,[z1,z2,z3,z4,z1184,z6]),(0,[z2,z3,z5,z185,z157,z7]),(0,[z55,z26,z3,z4,z27,z6]),(0,[z1,z2,z3,z24,z322,z6]),(0,[z193,z2,z3,z4,z28,z6]),(0,[z1,z2,z329,z421,z5,z6])],[(0,[z1185,z1,z2,z3,z5,z6]),(0,[z380,z3,z4,z5,z6,z7]),(0,[z2,z3,z4,z5,z416,z945]),(0,[z1,z195,z3,z4,z28,z6])],[(0,[z137,z72,z3,z4,z28,z6]),(0,[z1,z380,z3,z4,z149,z6]),(0,[z1,z2,z329,z4,z98,z6])],[(0,[z1,z2,z3,z1186,z5,z6]),(0,[z196,z2,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z1187,z6]),(0,[z1,z370,z2,z3,z28,z6]),(0,[z1,z588,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z1121,z6]),(0,[z1,z2,z710,z3,z28,z6])],[(0,[z2,z3,z4,z5,z6,z217]),(0,[z63,z2,z399,z83,z4,z6]),(0,[z888,z2,z3,z4,z5,z6]),(0,[z1,z2,z92,z511,z4,z6])],[(0,[z1188,z2,z3,z4,z5,z6]),(0,[z908,z1,z2,z86,z5,z6])],[(0,[z1,z2,z171,z4,z5,z6]),(0,[z34,z1,z3,z4,z914,z6]),(0,[z1,z356,z3,z4,z341,z6])],[(0,[z1,z2,z3,z1189,z5,z6]),(0,[z1,z2,z4,z94,z5,z416]),(0,[z1,z2,z3,z28,z6,z177]),(0,[z35,z1,z171,z4,z5,z101]),(0,[z1,z2,z1012,z4,z38,z6]),(0,[z1,z2,z3,z19,z28,z6])],[],[(0,[z1,z2,z3,z28,z6,z382])],[(0,[z3,z4,z5,z6,z7,z806]),(0,[z55,z2,z3,z298,z5,z6]),(0,[z1,z2,z3,z225,z28,z6]),(0,[z1,z127,z3,z5,z28,z6])],[(0,[z49,z2,z4,z5,z6,z7]),(0,[z2,z3,z28,z6,z7,z25]),(0,[z2,z3,z4,z953,z5,z6]),(0,[z49,z1,z2,z4,z267,z6]),(0,[z1190,z2,z3,z4,z5,z6]),(0,[z178,z2,z3,z4,z99,z6])],[(0,[z15,z43,z2,z5,z6,z7]),(0,[z178,z2,z3,z86,z5,z6]),(0,[z1,z1191,z3,z4,z5,z6]),(0,[z178,z2,z3,z4,z88,z6])],[(0,[z1,z2,z3,z6,z844,z157]),(0,[z55,z2,z3,z4,z267,z6]),(0,[z1,z2,z3,z1192,z5,z6])],[(0,[z2,z3,z4,z337,z5,z7]),(0,[z2,z3,z4,z5,z6,z1193]),(0,[z1,z2,z529,z4,z5,z45]),(0,[z589,z178,z2,z3,z28,z6])]],
   [[(0,[z13,z1,z2,z436,z5,z6]),(0,[z56,z2,z3,z4,z5,z7]),(0,[z122,z1,z380,z4,z5,z102])],[(0,[z668,z1,z2,z3,z28,z6]),(0,[z1,z2,z3,z4,z1194,z6]),(0,[z960,z2,z3,z4,z5,z6])],[(0,[z77,z2,z3,z20,z28,z6]),(0,[z2,z3,z378,z5,z6,z7]),(0,[z2,z525,z4,z5,z6,z396]),(0,[z2,z3,z4,z5,z6,z1195]),(0,[z1,z2,z1196,z3,z4,z6])],[(0,[z2,z3,z4,z5,z352,z7])],[(0,[z63,z2,z83,z4,z84,z6]),(0,[z13,z2,z3,z78,z433,z6]),(0,[z8,z1,z2,z3,z5,z6]),(0,[z2,z828,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z1197,z6]),(0,[z1198,z2,z3,z4,z5,z6]),(0,[z1,z1199,z3,z4,z5,z6]),(0,[z1,z860,z3,z4,z28,z6])],[(0,[z503,z1,z2,z3,z28,z6]),(0,[z1,z2,z324,z4,z5,z361]),(0,[z1,z3,z378,z146,z5,z6]),(0,[z1,z22,z3,z24,z28,z6]),(0,[z1013,z2,z47,z3,z4,z6])],[(0,[z1,z1200,z3,z4,z5,z6]),(0,[z1,z2,z324,z146,z5,z6]),(0,[z2,z3,z4,z5,z6,z1201]),(0,[z207,z96,z3,z4,z5,z36])],[(1,[z1,z2,z324,z28,z6]),(0,[z1,z2,z3,z1202,z5,z6]),(0,[z1,z2,z1203,z4,z5,z6]),(0,[z1,z2,z3,z4,z1204,z6])],[(0,[z2,z3,z1021,z5,z6,z7]),(0,[z43,z55,z2,z3,z28,z6]),(0,[z2,z3,z5,z6,z760,z217])],[(0,[z435,z1,z837,z3,z5,z6]),(0,[z13,z1,z2,z3,z639,z6]),(0,[z8,z2,z3,z5,z250,z7]),(0,[z1,z2,z3,z4,z1205,z6]),(0,[z1,z3,z4,z742,z5,z6]),(0,[z1,z26,z3,z4,z27,z6]),(0,[z449,z2,z179,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1206,z6]),(0,[z161,z2,z3,z4,z28,z7]),(0,[z93,z55,z4,z94,z5,z6])],[(0,[z77,z1,z2,z3,z28,z6]),(0,[z1,z2,z3,z1207,z5,z6]),(0,[z318,z2,z3,z378,z5,z6]),(0,[z1,z2,z3,z146,z115,z6]),(0,[z49,z1,z22,z4,z5,z6]),(0,[z18,z1,z2,z3,z5,z25])],[(0,[z1,z1208,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z186]),(0,[z2,z3,z4,z973,z5,z6]),(0,[z55,z2,z3,z4,z222,z6]),(0,[z1209,z2,z3,z4,z5,z6])],[(0,[z55,z2,z3,z4,z322,z6]),(0,[z1,z2,z3,z1210,z5,z6]),(0,[z908,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1211,z6])],[(0,[z77,z2,z3,z5,z185,z7]),(0,[z1,z2,z828,z4,z5,z6]),(0,[z1,z3,z846,z146,z5,z6]),(0,[z1,z2,z3,z1212,z5,z6]),(0,[z1,z2,z955,z4,z5,z6]),(0,[z111,z2,z3,z4,z258,z6]),(0,[z140,z1,z167,z3,z4,z29])],[(0,[z1,z1213,z3,z4,z5,z6]),(0,[z77,z2,z3,z259,z5,z6]),(0,[z55,z2,z3,z4,z1165,z6]),(0,[z1,z2,z1214,z4,z5,z6]),(0,[z120,z1,z2,z92,z4,z6]),(0,[z142,z112,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z59,z5,z250]),(0,[z55,z2,z3,z5,z6,z157]),(0,[z1,z2,z3,z1215,z5,z6]),(0,[z303,z1,z2,z3,z5,z6]),(0,[z1,z2,z1216,z3,z4,z6])],[(0,[z1,z2,z1217,z3,z4,z6]),(0,[z2,z3,z4,z28,z6,z7]),(0,[z1,z2,z436,z19,z5,z6]),(0,[z1,z2,z3,z4,z1218,z6]),(0,[z1,z1219,z3,z4,z5,z6]),(0,[z122,z193,z2,z4,z5,z102])],[(0,[z13,z55,z2,z3,z28,z6]),(0,[z43,z1,z2,z3,z586,z6])],[(0,[z1,z2,z3,z1220,z5,z6]),(0,[z1,z1221,z3,z4,z5,z6]),(0,[z2,z83,z4,z5,z6,z396]),(0,[z1,z2,z3,z4,z1222,z6]),(0,[z678,z1,z2,z47,z3,z6]),(0,[z1,z2,z151,z86,z586,z6]),(0,[z2,z3,z4,z5,z6,z1223]),(0,[z82,z2,z3,z168,z5,z6])],[(0,[z2,z3,z4,z5,z404,z7]),(0,[z55,z16,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z405,z99])],[(0,[z134,z1,z2,z3,z441,z6]),(0,[z2,z3,z4,z987,z5,z6]),(0,[z1,z2,z3,z4,z1224,z6])],[(0,[z1,z2,z3,z1225,z5,z6]),(0,[z730,z1,z2,z3,z4,z6]),(0,[z55,z2,z3,z146,z28,z6]),(0,[z55,z380,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1226,z6]),(0,[z1,z2,z3,z4,z267,z6])],[(0,[z265,z72,z3,z4,z5,z6]),(0,[z1,z2,z3,z28,z6,z250]),(0,[z826,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1227,z5,z6]),(0,[z1,z2,z3,z4,z1228,z6]),(0,[z1,z2,z3,z4,z5,z750]),(0,[z1229,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1230,z4,z5,z6]),(0,[z1,z2,z3,z19,z115,z6]),(0,[z1,z367,z3,z4,z5,z102])],[(0,[z55,z2,z144,z4,z5,z6]),(0,[z1,z2,z3,z4,z1231,z6]),(0,[z1,z1232,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1233]),(0,[z212,z1,z3,z4,z5,z101]),(0,[z1234,z2,z3,z4,z5,z6]),(0,[z1113,z2,z3,z4,z6,z233])],[(0,[z318,z2,z3,z4,z5,z6]),(0,[z181,z1,z2,z3,z28,z6]),(0,[z318,z2,z3,z4,z5,z416]),(0,[z1,z2,z3,z4,z1235,z6]),(0,[z145,z1,z3,z146,z354,z6]),(0,[z49,z1,z22,z24,z5,z6]),(0,[z342,z2,z171,z4,z5,z6]),(0,[z1,z2,z171,z4,z545,z6])],[(0,[z1,z14,z3,z86,z5,z6]),(0,[z2,z3,z4,z5,z6,z243]),(0,[z55,z2,z3,z4,z354,z6]),(0,[z55,z2,z151,z86,z5,z6]),(0,[z93,z1,z4,z94,z5,z33]),(0,[z178,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z141,z28,z6]),(0,[z342,z2,z47,z3,z4,z6])],[(0,[z110,z3,z4,z5,z6,z7])],[(0,[z1,z2,z3,z4,z1236,z6]),(0,[z1,z2,z3,z4,z116,z361]),(0,[z1,z2,z1237,z3,z4,z6]),(0,[z1,z1238,z3,z4,z5,z6])],[(0,[z1,z2,z205,z3,z28,z6]),(0,[z1,z2,z3,z4,z899,z6]),(0,[z1239,z2,z3,z4,z5,z6]),(0,[z1,z127,z3,z4,z115,z6])],[(0,[z2,z3,z4,z5,z6,z712]),(0,[z2,z436,z4,z5,z6,z7]),(0,[z2,z3,z4,z1071,z6,z7]),(0,[z1,z2,z3,z4,z1240,z6]),(0,[z496,z1,z2,z3,z28,z6])]],
   [[(0,[z2,z3,z4,z266,z6,z7])],[(1,[z2,z3,z4,z822,z6]),(0,[z1241,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z28,z6,z481]),(0,[z46,z1,z370,z3,z4,z6])],[(0,[z2,z3,z4,z84,z6,z7]),(0,[z55,z2,z171,z4,z5,z6]),(0,[z216,z2,z3,z298,z5,z6])],[(0,[z1,z2,z3,z4,z1242,z6]),(0,[z77,z1,z2,z410,z5,z6]),(0,[z58,z2,z3,z4,z574,z6]),(0,[z55,z2,z47,z3,z4,z6]),(0,[z869,z55,z2,z3,z5,z6]),(0,[z55,z2,z3,z19,z28,z6])],[(0,[z77,z1,z127,z3,z5,z6]),(0,[z1,z2,z3,z4,z222,z6])],[(0,[z35,z3,z4,z5,z7,z101]),(0,[z730,z2,z3,z4,z28,z6]),(0,[z1,z22,z3,z57,z5,z6]),(0,[z1,z2,z3,z4,z322,z6])],[(0,[z1243,z1,z2,z3,z5,z6]),(0,[z2,z3,z4,z150,z5,z6]),(0,[z2,z3,z20,z748,z5,z6]),(0,[z8,z55,z2,z3,z5,z7]),(0,[z55,z2,z3,z421,z5,z6]),(0,[z1,z2,z612,z3,z28,z6]),(0,[z1,z2,z60,z421,z5,z6]),(0,[z1,z2,z3,z4,z98,z808])],[(0,[z2,z3,z5,z6,z157,z186]),(0,[z1,z2,z3,z505,z28,z6])],[(0,[z1,z2,z184,z3,z28,z6]),(0,[z1,z1244,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z157]),(0,[z1,z2,z3,z5,z185,z615]),(0,[z1,z2,z3,z506,z28,z6]),(0,[z1,z2,z3,z1245,z5,z6]),(0,[z547,z1,z2,z3,z5,z25]),(0,[z767,z2,z3,z4,z5,z6])],[(0,[z55,z96,z3,z4,z5,z36]),(0,[z1,z2,z3,z509,z28,z6]),(0,[z1,z171,z4,z5,z6,z101])],[(0,[z1,z14,z3,z4,z5,z6]),(0,[z1,z2,z269,z4,z5,z6]),(0,[z1,z2,z3,z4,z1246,z6])],[(0,[z39,z2,z3,z5,z7,z25]),(0,[z55,z2,z3,z4,z85,z7]),(0,[z181,z2,z3,z80,z5,z6]),(0,[z55,z2,z3,z1247,z5,z6]),(0,[z1,z2,z3,z515,z28,z6])],[(0,[z1,z2,z3,z4,z6,z1143]),(0,[z1,z2,z3,z1248,z5,z6]),(0,[z1,z2,z3,z4,z1249,z6]),(0,[z854,z3,z4,z5,z6,z7]),(0,[z1,z3,z146,z5,z6,z257]),(0,[z1,z2,z3,z4,z98,z336]),(0,[z1250,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1251,z6]),(0,[z1,z2,z3,z4,z1252,z6])],[(1,[z1,z2,z3,z28,z250]),(0,[z1,z2,z3,z4,z28,z361]),(0,[z1253,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1254,z6]),(0,[z1255,z1,z2,z4,z5,z6]),(0,[z140,z178,z2,z3,z4,z6]),(0,[z1,z2,z1256,z3,z4,z6])],[(0,[z1,z2,z3,z1257,z5,z6]),(0,[z1,z2,z3,z146,z28,z6]),(0,[z2,z3,z146,z150,z28,z6]),(0,[z1,z2,z910,z4,z28,z6])],[(0,[z2,z3,z4,z115,z6,z7]),(0,[z1,z2,z114,z4,z28,z6]),(0,[z142,z2,z3,z4,z222,z6])]],
   [[(0,[z1,z2,z3,z4,z1258,z6])],[(0,[z1,z2,z144,z4,z5,z6]),(0,[z55,z2,z3,z4,z292,z6]),(0,[z1,z360,z3,z4,z6,z29])],[(0,[z1,z2,z3,z4,z5,z1259]),(0,[z585,z1,z2,z3,z28,z6])],[(0,[z1,z1260,z3,z4,z5,z6]),(0,[z2,z3,z5,z157,z7,z25]),(0,[z1,z2,z3,z4,z354,z6]),(0,[z1029,z2,z3,z4,z5,z6])],[(0,[z1,z768,z3,z4,z5,z6]),(0,[z58,z1,z2,z3,z441,z6]),(0,[z2,z47,z3,z6,z157,z7]),(0,[z1,z1261,z3,z4,z5,z6])],[(0,[z255,z1,z2,z3,z6,z157]),(0,[z1,z2,z47,z114,z4,z6])],[(0,[z1,z2,z324,z4,z433,z6]),(0,[z2,z3,z4,z150,z639,z6]),(0,[z55,z2,z3,z1207,z5,z6]),(0,[z1,z2,z3,z4,z1262,z6]),(0,[z1,z2,z3,z4,z1263,z6])],[(0,[z74,z143,z3,z192,z5,z6]),(0,[z58,z2,z3,z4,z201,z6]),(0,[z428,z2,z3,z5,z6,z7]),(0,[z1084,z1,z2,z3,z5,z6])],[(0,[z1,z2,z1079,z3,z4,z6]),(0,[z2,z4,z5,z6,z7,z1264])],[(0,[z1,z2,z3,z1265,z5,z6]),(0,[z1,z1266,z3,z4,z5,z6])],[(0,[z2,z3,z146,z5,z7,z25]),(0,[z93,z1,z4,z94,z28,z6]),(0,[z1267,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1268]),(0,[z1,z2,z298,z5,z6,z102])],[(0,[z1,z2,z47,z3,z4,z6]),(0,[z55,z2,z3,z123,z5,z6]),(0,[z1,z2,z47,z3,z4,z416]),(0,[z1,z2,z3,z1269,z5,z6])],[(0,[z2,z144,z4,z5,z6,z7]),(0,[z35,z1,z47,z3,z4,z101]),(0,[z1,z3,z4,z5,z6,z845]),(0,[z1,z195,z3,z4,z258,z6])],[(0,[z1,z1270,z3,z4,z5,z6]),(0,[z1,z2,z3,z371,z5,z6]),(0,[z216,z380,z3,z4,z5,z6])],[(0,[z1,z1271,z3,z4,z5,z6]),(0,[z13,z2,z47,z3,z78,z6]),(0,[z55,z2,z254,z3,z4,z6]),(0,[z8,z2,z3,z5,z6,z7]),(0,[z189,z1,z3,z146,z5,z6]),(0,[z1,z2,z114,z225,z5,z6]),(0,[z35,z1,z3,z371,z5,z101]),(0,[z1,z2,z327,z86,z5,z6]),(0,[z1,z2,z3,z421,z5,z6]),(0,[z1,z2,z327,z4,z88,z6])],[(0,[z1,z2,z3,z4,z1272,z6]),(0,[z122,z2,z4,z5,z7,z102])]],
   [[(0,[z130,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z1132]),(0,[z428,z1,z2,z3,z5,z6]),(0,[z49,z1,z2,z47,z4,z6]),(0,[z1,z360,z329,z4,z5,z6])],[(0,[z55,z2,z3,z1273,z5,z6]),(0,[z1,z2,z47,z3,z378,z6]),(0,[z1,z96,z3,z4,z5,z36]),(0,[z1,z1274,z3,z4,z5,z6]),(0,[z1,z127,z3,z4,z28,z6]),(0,[z1,z2,z870,z3,z4,z6])],[(0,[z1,z2,z1101,z3,z4,z6]),(0,[z43,z1,z2,z144,z5,z6]),(0,[z1,z2,z3,z24,z354,z6]),(0,[z1,z2,z3,z4,z1275,z6]),(0,[z1,z2,z47,z436,z4,z6]),(0,[z1276,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1277,z6])],[(0,[z435,z55,z2,z3,z5,z6]),(0,[z77,z2,z47,z3,z20,z6]),(0,[z1,z2,z3,z1247,z5,z6]),(0,[z207,z2,z47,z3,z4,z6]),(0,[z1,z2,z3,z19,z322,z185])],[(0,[z13,z187,z3,z78,z5,z6]),(0,[z1,z2,z3,z86,z116,z6]),(0,[z55,z2,z3,z4,z1231,z6]),(0,[z1278,z1,z2,z3,z5,z6]),(0,[z1279,z2,z3,z4,z5,z6])],[(0,[z134,z2,z3,z4,z6,z243]),(0,[z1,z2,z47,z3,z368,z6]),(0,[z35,z204,z3,z4,z5,z101]),(0,[z1,z2,z3,z4,z1280,z6]),(0,[z2,z47,z3,z4,z150,z6])],[(0,[z204,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z302,z6,z7]),(0,[z142,z2,z47,z3,z4,z6])],[(0,[z435,z1,z2,z3,z1281,z6]),(0,[z1,z2,z3,z4,z6,z983]),(0,[z1,z2,z3,z4,z1282,z6]),(0,[z1,z2,z3,z4,z1283,z6]),(0,[z1,z22,z3,z846,z5,z6]),(0,[z1,z110,z3,z4,z115,z6]),(0,[z1,z183,z328,z3,z4,z6])],[(0,[z1,z2,z3,z441,z28,z6]),(0,[z58,z1,z360,z3,z4,z6]),(0,[z1,z2,z567,z151,z86,z6]),(0,[z908,z1,z2,z4,z5,z6]),(0,[z1,z1284,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z292,z6]),(0,[z1,z2,z1285,z3,z4,z6]),(0,[z1,z2,z710,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1286,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z303,z2,z3,z5,z6,z7]),(0,[z1,z2,z3,z28,z6,z413]),(0,[z1287,z2,z3,z4,z5,z6]),(0,[z216,z2,z47,z3,z4,z6]),(0,[z2,z3,z4,z28,z6,z858])],[(0,[z1,z2,z47,z144,z4,z6]),(0,[z255,z53,z2,z3,z4,z6]),(0,[z1,z2,z3,z1288,z5,z6]),(0,[z1289,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1290,z5,z6]),(0,[z2,z241,z3,z150,z28,z6]),(1,[z1,z2,z3,z4,z808])],[(0,[z55,z2,z3,z4,z5,z530]),(0,[z13,z2,z3,z78,z5,z6]),(0,[z140,z55,z2,z3,z4,z29]),(0,[z632,z1,z3,z146,z5,z6]),(0,[z1291,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z587,z28,z6]),(0,[z1,z2,z1292,z4,z5,z6]),(0,[z2,z3,z4,z1258,z6,z7]),(0,[z8,z1,z2,z3,z1071,z6]),(0,[z55,z2,z3,z4,z1293,z6]),(0,[z1294,z2,z3,z4,z5,z6]),(0,[z970,z2,z3,z4,z5,z6]),(0,[z1,z2,z718,z3,z298,z6]),(0,[z1,z2,z3,z4,z6,z1160]),(0,[z1,z1104,z47,z3,z4,z6])],[(0,[z1,z2,z144,z4,z5,z250]),(0,[z2,z3,z4,z5,z542,z7]),(0,[z1295,z2,z3,z4,z5,z6]),(0,[z758,z1,z2,z3,z4,z6])],[(0,[z178,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z250,z7]),(0,[z43,z1,z2,z3,z5,z250]),(0,[z1,z3,z24,z146,z28,z6]),(0,[z156,z43,z1,z2,z5,z6]),(0,[z974,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1296,z6]),(0,[z53,z2,z329,z4,z5,z6])]],
   [[(0,[z43,z1,z2,z132,z5,z6])],[(0,[z1297,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1298,z5,z6]),(0,[z43,z1,z127,z3,z28,z6])],[(0,[z1,z2,z3,z1299,z5,z6]),(0,[z1,z2,z917,z3,z5,z6]),(0,[z2,z3,z1248,z5,z6,z7])],[(0,[z63,z2,z332,z4,z5,z6]),(0,[z106,z2,z3,z4,z5,z250]),(0,[z2,z3,z86,z5,z7,z25]),(0,[z1,z2,z3,z4,z1300,z6]),(0,[z1,z2,z3,z1301,z5,z6]),(0,[z1,z2,z3,z123,z5,z6])],[(0,[z2,z3,z4,z5,z33,z1087]),(0,[z1,z2,z3,z267,z6,z25]),(0,[z96,z3,z4,z5,z36,z233]),(0,[z1,z2,z3,z86,z28,z6]),(0,[z981,z2,z3,z4,z5,z6])],[(0,[z782,z1,z2,z4,z5,z6]),(0,[z55,z14,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1302,z6]),(0,[z1303,z1,z2,z3,z5,z6]),(0,[z55,z2,z1304,z3,z4,z6]),(0,[z55,z2,z269,z4,z5,z6]),(0,[z1305,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1306,z6])],[(0,[z1,z2,z254,z3,z4,z6]),(0,[z1,z2,z379,z3,z28,z6])],[(0,[z2,z3,z538,z5,z6,z7]),(0,[z351,z2,z3,z4,z107,z6]),(0,[z1,z831,z3,z4,z5,z6])],[(0,[z161,z2,z3,z4,z85,z7]),(0,[z55,z2,z3,z412,z5,z6]),(0,[z1307,z2,z3,z4,z5,z6]),(0,[z160,z1,z2,z4,z5,z102]),(1,[z908,z1,z2,z5,z6]),(0,[z1,z2,z3,z1308,z5,z6])],[(0,[z1,z2,z439,z4,z38,z6]),(0,[z55,z2,z3,z538,z5,z6]),(0,[z1,z2,z3,z1273,z5,z6]),(0,[z1309,z2,z3,z4,z5,z6]),(0,[z1,z2,z1310,z3,z4,z6]),(0,[z1122,z2,z47,z3,z4,z6]),(0,[z1,z112,z47,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1311,z6]),(0,[z2,z3,z4,z5,z6,z1312])],[(0,[z55,z2,z410,z4,z5,z6]),(0,[z351,z2,z3,z4,z266,z6]),(0,[z1,z2,z1313,z4,z5,z6]),(0,[z1,z2,z593,z3,z28,z6]),(0,[z1,z380,z3,z298,z5,z6]),(0,[z1,z2,z3,z123,z149,z6]),(0,[z1,z2,z4,z292,z6,z102]),(0,[z1,z2,z1314,z4,z5,z6])],[(0,[z1,z72,z3,z146,z28,z6]),(0,[z1,z2,z3,z4,z1315,z6]),(0,[z585,z2,z3,z4,z5,z7]),(0,[z49,z55,z2,z4,z5,z6]),(0,[z1,z2,z1316,z4,z5,z6]),(0,[z39,z1,z127,z3,z5,z6]),(0,[z140,z1,z2,z3,z4,z316])],[(0,[z386,z2,z3,z4,z5,z6]),(0,[z145,z55,z3,z146,z5,z6]),(0,[z1,z2,z3,z1317,z5,z6]),(0,[z1,z2,z3,z1318,z5,z6]),(0,[z1,z2,z47,z3,z480,z6]),(0,[z589,z2,z321,z3,z4,z6]),(0,[z812,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1319,z6]),(0,[z77,z2,z254,z3,z20,z6]),(0,[z1,z2,z3,z1320,z5,z6]),(0,[z1,z1321,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1089])],[(0,[z1,z2,z3,z4,z1322,z6]),(0,[z1,z2,z1178,z3,z4,z6]),(0,[z178,z77,z2,z3,z28,z6]),(0,[z908,z1,z2,z151,z5,z6]),(0,[z1,z2,z540,z4,z38,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1323]),(0,[z13,z1,z187,z3,z28,z6]),(0,[z342,z2,z3,z371,z5,z6]),(0,[z1,z2,z3,z371,z545,z6])],[(0,[z1,z2,z44,z4,z5,z637]),(0,[z1324,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1325,z4,z5,z6]),(0,[z13,z2,z3,z59,z28,z6]),(0,[z429,z1,z4,z94,z5,z6]),(0,[z1,z367,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1326,z6]),(0,[z216,z2,z3,z123,z5,z6]),(0,[z2,z3,z4,z889,z28,z6])],[(0,[z178,z2,z92,z3,z4,z6])],[(0,[z8,z1,z2,z3,z5,z250]),(0,[z58,z2,z3,z4,z6,z243]),(0,[z1,z2,z3,z4,z6,z881]),(0,[z1327,z2,z3,z4,z5,z6])],[(0,[z13,z2,z3,z748,z5,z6]),(0,[z178,z2,z3,z4,z59,z6]),(0,[z2,z3,z4,z1144,z6,z7]),(0,[z1,z2,z3,z4,z1293,z6]),(0,[z1328,z2,z3,z4,z5,z6]),(0,[z1329,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z586,z6,z7]),(0,[z2,z3,z4,z5,z6,z1330])],[(0,[z1,z2,z47,z3,z538,z6]),(0,[z1,z2,z3,z4,z484,z6]),(0,[z2,z3,z4,z1168,z322,z6]),(0,[z140,z1,z2,z329,z4,z29])],[(0,[z203,z2,z4,z125,z5,z6]),(0,[z255,z2,z3,z4,z210,z6]),(0,[z2,z3,z4,z5,z6,z1331]),(0,[z2,z3,z225,z5,z6,z7]),(0,[z55,z2,z3,z371,z5,z6]),(0,[z1,z2,z3,z1332,z5,z6]),(0,[z1,z2,z379,z3,z4,z6]),(0,[z35,z1,z3,z4,z484,z101]),(0,[z1,z2,z3,z467,z28,z6]),(0,[z130,z2,z44,z4,z5,z45])],[(0,[z204,z2,z3,z4,z545,z6]),(0,[z1,z1333,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z486,z6])],[(0,[z2,z3,z298,z5,z6,z7]),(0,[z2,z3,z6,z844,z157,z7]),(0,[z1,z2,z3,z4,z1334,z6]),(0,[z1,z2,z3,z4,z1335,z6]),(0,[z1,z110,z3,z4,z28,z6]),(0,[z1,z2,z1336,z4,z5,z6])],[(0,[z1,z2,z44,z4,z5,z242])],[(0,[z13,z1,z2,z3,z267,z6]),(0,[z1337,z2,z3,z4,z5,z6]),(0,[z1337,z2,z3,z4,z5,z416]),(0,[z145,z1,z47,z3,z146,z6]),(0,[z140,z1,z2,z3,z168,z29])],[(0,[z74,z143,z3,z4,z28,z6]),(0,[z13,z77,z2,z3,z28,z6]),(0,[z196,z2,z3,z4,z5,z6]),(0,[z1,z2,z1304,z3,z4,z6]),(0,[z1,z2,z1338,z3,z4,z6]),(0,[z1,z2,z3,z1339,z5,z6]),(0,[z1340,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z1341]),(0,[z1,z2,z3,z1342,z5,z6]),(0,[z1343,z2,z3,z4,z5,z6]),(0,[z178,z2,z198,z3,z4,z6]),(0,[z1,z2,z103,z511,z4,z6])],[(0,[z751,z2,z3,z6,z157,z7])]],
   [[(0,[z1159,z1,z3,z4,z5,z6]),(0,[z26,z3,z4,z27,z6,z7]),(0,[z1,z2,z3,z4,z1344,z6]),(0,[z1,z2,z3,z412,z5,z6]),(0,[z1345,z2,z3,z4,z5,z6])],[(0,[z1,z2,z23,z4,z5,z416]),(0,[z1,z2,z3,z538,z5,z6])],[(0,[z93,z1,z378,z94,z5,z6]),(0,[z1,z2,z3,z436,z28,z6]),(0,[z162,z1,z2,z3,z5,z25])],[(0,[z1,z2,z3,z192,z997,z6]),(0,[z435,z1,z2,z3,z28,z6]),(0,[z1,z2,z410,z4,z5,z6]),(0,[z1153,z1,z2,z3,z5,z6])],[(0,[z55,z2,z3,z4,z5,z606]),(0,[z2,z3,z4,z822,z210,z6]),(0,[z1,z2,z1346,z4,z5,z6]),(0,[z2,z1217,z3,z4,z6,z7]),(0,[z1,z2,z3,z4,z1035,z6]),(0,[z1347,z2,z3,z4,z5,z6])],[(0,[z1348,z1,z2,z3,z5,z6]),(0,[z1,z2,z47,z324,z4,z6]),(0,[z55,z360,z3,z4,z5,z6]),(0,[z178,z2,z3,z4,z150,z6]),(0,[z1,z1111,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1264]),(0,[z1,z187,z324,z4,z5,z6]),(0,[z1,z2,z1349,z4,z5,z6]),(0,[z93,z4,z94,z5,z6,z7]),(0,[z145,z3,z146,z5,z6,z7])],[(0,[z35,z55,z3,z4,z5,z101]),(0,[z1,z3,z4,z914,z5,z6]),(0,[z122,z1,z2,z4,z5,z102])],[(0,[z8,z1,z2,z47,z3,z6]),(0,[z1,z2,z3,z368,z107,z6]),(0,[z1350,z2,z3,z4,z5,z6]),(0,[z142,z2,z269,z4,z5,z6])],[(0,[z134,z2,z3,z4,z575,z6]),(0,[z1351,z2,z3,z4,z5,z6]),(0,[z1,z2,z1012,z91,z4,z6]),(0,[z1,z2,z710,z241,z3,z6])],[(0,[z10,z143,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1281,z6]),(0,[z55,z2,z3,z4,z5,z615]),(0,[z2,z3,z4,z98,z99,z7]),(0,[z1,z2,z1352,z3,z4,z6]),(0,[z547,z1,z2,z4,z5,z102]),(0,[z142,z2,z3,z4,z5,z185])],[(0,[z2,z633,z3,z4,z5,z7]),(0,[z2,z399,z3,z4,z6,z7]),(0,[z1,z2,z952,z3,z4,z6]),(0,[z1353,z2,z3,z4,z5,z6])],[(0,[z75,z2,z4,z384,z5,z6]),(0,[z1,z2,z3,z368,z266,z6]),(0,[z1,z2,z436,z4,z5,z6]),(0,[z1,z2,z3,z4,z1354,z6]),(0,[z43,z1,z110,z3,z28,z6]),(0,[z1,z1355,z3,z4,z5,z6])],[(0,[z1,z2,z3,z432,z28,z6]),(0,[z1,z2,z3,z5,z28,z250]),(0,[z2,z410,z4,z5,z6,z7]),(0,[z43,z178,z2,z3,z28,z6])],[(0,[z1,z2,z324,z4,z5,z6]),(0,[z55,z2,z3,z4,z116,z6]),(0,[z111,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z545,z6,z7]),(0,[z2,z47,z3,z4,z6,z7]),(0,[z55,z2,z3,z4,z1300,z6]),(0,[z351,z2,z3,z378,z5,z6]),(0,[z1,z2,z47,z151,z86,z6]),(0,[z142,z2,z410,z4,z5,z6])],[(0,[z609,z1,z2,z3,z28,z6]),(0,[z2,z3,z4,z5,z712,z7]),(0,[z2,z3,z4,z28,z7,z25]),(0,[z55,z2,z3,z86,z28,z6]),(0,[z122,z1,z2,z4,z149,z102]),(0,[z18,z1,z2,z47,z3,z25])]],
   [[(1,[z1,z171,z4,z5,z101])],[(0,[z15,z496,z1,z2,z5,z6]),(0,[z303,z1,z2,z3,z302,z6])],[(0,[z1,z2,z47,z60,z4,z6])],[(0,[z55,z2,z3,z1356,z5,z6]),(0,[z1,z3,z4,z27,z6,z174]),(0,[z1,z2,z3,z4,z115,z6]),(0,[z1,z1357,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z1121,z6]),(0,[z1,z380,z47,z3,z4,z6])],[(0,[z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z1358,z5,z6]),(0,[z13,z2,z3,z447,z5,z6]),(0,[z1359,z2,z3,z4,z5,z6]),(0,[z1360,z2,z3,z4,z5,z6]),(0,[z303,z1,z2,z47,z3,z6]),(0,[z82,z2,z329,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1361,z6]),(0,[z1,z2,z47,z1314,z4,z6]),(0,[z1,z112,z3,z4,z222,z6])],[(0,[z1,z2,z3,z4,z892,z6]),(0,[z1,z2,z3,z4,z1362,z6])],[(0,[z13,z178,z2,z3,z28,z6]),(0,[z77,z2,z3,z5,z6,z186]),(0,[z1,z2,z47,z3,z441,z6]),(0,[z1,z2,z3,z4,z5,z33]),(0,[z1,z3,z4,z146,z5,z416])],[(0,[z1,z2,z1363,z3,z4,z6]),(1,[z1,z3,z846,z5,z6]),(0,[z15,z43,z1,z2,z115,z6]),(0,[z122,z216,z2,z4,z5,z102]),(1,[z1,z2,z710,z3,z6]),(0,[z2,z3,z4,z28,z6,z852])],[(0,[z1,z2,z3,z1364,z5,z6]),(0,[z1,z2,z4,z5,z6,z1365]),(0,[z1,z2,z3,z4,z937,z6]),(0,[z1,z2,z3,z168,z6,z29])],[(0,[z1,z14,z3,z4,z5,z250]),(0,[z2,z3,z4,z5,z658,z7]),(0,[z342,z2,z3,z4,z484,z6]),(0,[z2,z3,z86,z150,z28,z6]),(0,[z1,z2,z1012,z3,z4,z6])],[(0,[z1,z1366,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z7,z492]),(0,[z660,z3,z4,z5,z6,z520]),(0,[z2,z3,z4,z292,z6,z7]),(0,[z1,z112,z269,z4,z5,z6])],[(0,[z77,z2,z3,z28,z6,z7]),(0,[z127,z3,z4,z5,z6,z7]),(0,[z2,z3,z4,z5,z663,z7]),(0,[z1,z2,z3,z1367,z5,z6]),(1,[z1,z2,z1012,z4,z6]),(0,[z2,z3,z4,z5,z6,z1368])],[(0,[z351,z2,z3,z4,z5,z6]),(0,[z1,z2,z324,z24,z5,z6]),(0,[z55,z367,z3,z4,z5,z6]),(0,[z351,z2,z3,z4,z5,z416]),(0,[z145,z1,z3,z146,z28,z6]),(0,[z1,z360,z3,z4,z5,z6])],[(0,[z777,z1,z2,z4,z5,z6]),(0,[z1,z187,z3,z4,z116,z6]),(0,[z1,z1369,z3,z4,z5,z6]),(0,[z1,z1370,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z28,z6]),(0,[z1053,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z263,z28,z6]),(0,[z1,z2,z3,z5,z804,z25])],[(0,[z1,z2,z47,z3,z371,z6]),(0,[z386,z2,z3,z4,z98,z99])]],
   [[(0,[z1,z2,z1371,z4,z5,z6]),(0,[z1,z2,z3,z4,z1372,z6]),(0,[z1,z127,z3,z19,z5,z6]),(0,[z1,z1373,z3,z4,z5,z6])],[(0,[z1,z143,z3,z146,z28,z6]),(0,[z1,z2,z1374,z4,z5,z6]),(0,[z1,z2,z3,z4,z1375,z6]),(0,[z1,z112,z410,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1376]),(0,[z1377,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z484,z6]),(0,[z1,z2,z3,z24,z115,z6]),(0,[z178,z2,z47,z3,z28,z6])],[(0,[z1,z2,z92,z626,z4,z6]),(0,[z2,z3,z24,z28,z6,z7]),(0,[z55,z2,z379,z3,z4,z6]),(0,[z1378,z1,z2,z3,z5,z6]),(0,[z1379,z2,z3,z4,z5,z6]),(0,[z449,z1,z2,z3,z28,z6])],[(0,[z1,z2,z3,z4,z1380,z6]),(0,[z1,z2,z3,z4,z107,z33]),(0,[z1,z2,z379,z3,z538,z6]),(0,[z1,z2,z3,z4,z1381,z6])],[(1,[z2,z4,z832,z5,z6]),(0,[z13,z255,z2,z3,z4,z6]),(0,[z1,z919,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1382]),(0,[z2,z3,z4,z5,z6,z1383]),(0,[z1,z2,z1154,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z804])],[(0,[z1,z2,z3,z4,z116,z6]),(0,[z1,z2,z3,z4,z822,z6]),(0,[z255,z2,z3,z4,z6,z85]),(0,[z55,z2,z3,z4,z6,z85]),(0,[z55,z2,z3,z368,z5,z6]),(0,[z1,z3,z4,z846,z5,z6])],[(0,[z55,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z378,z717,z6]),(0,[z1,z2,z3,z378,z28,z6]),(0,[z1,z2,z3,z4,z5,z1384]),(0,[z178,z2,z3,z146,z28,z6]),(0,[z1,z2,z990,z3,z225,z6])],[(0,[z2,z329,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z266,z33]),(0,[z1,z96,z3,z4,z5,z163]),(0,[z1,z167,z329,z4,z5,z6]),(0,[z1,z2,z329,z168,z5,z6])],[(0,[z1,z2,z3,z1385,z5,z6]),(0,[z1,z2,z3,z190,z5,z185]),(0,[z1,z2,z3,z4,z1386,z6]),(0,[z1,z16,z4,z742,z5,z6]),(0,[z1,z16,z47,z23,z4,z6]),(0,[z1,z2,z410,z5,z6,z25])],[(0,[z8,z2,z3,z78,z5,z6]),(0,[z204,z2,z171,z4,z5,z6]),(0,[z1,z2,z3,z1387,z5,z6])],[(0,[z55,z2,z3,z192,z5,z6]),(0,[z1,z2,z47,z3,z4,z250]),(0,[z58,z428,z2,z3,z59,z6]),(0,[z255,z2,z3,z4,z7,z25]),(0,[z1,z2,z3,z1356,z5,z6]),(0,[z49,z1,z2,z24,z28,z6]),(0,[z216,z2,z3,z4,z292,z6]),(0,[z1,z380,z3,z123,z5,z6])],[(0,[z1,z2,z1388,z4,z5,z6]),(0,[z53,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z746,z6]),(0,[z93,z318,z4,z94,z5,z6]),(0,[z1,z4,z742,z94,z5,z6]),(0,[z1,z2,z3,z4,z405,z284]),(0,[z1,z2,z329,z4,z28,z6])],[(0,[z435,z1,z2,z3,z791,z6]),(0,[z1,z1389,z3,z4,z5,z6]),(0,[z2,z3,z4,z6,z844,z7]),(0,[z55,z2,z3,z24,z28,z6]),(0,[z2,z44,z4,z5,z45,z217])],[(0,[z1,z187,z3,z4,z28,z6]),(0,[z77,z142,z2,z3,z5,z6]),(0,[z2,z3,z5,z28,z7,z25]),(0,[z1,z2,z1390,z4,z5,z6]),(0,[z1,z2,z1391,z4,z5,z6])],[(0,[z1,z994,z2,z3,z4,z6]),(0,[z1,z2,z399,z3,z166,z6]),(0,[z1,z2,z3,z4,z433,z361]),(0,[z13,z2,z3,z5,z6,z157]),(0,[z2,z3,z5,z6,z157,z7]),(0,[z1,z2,z3,z4,z1392,z6]),(0,[z1,z2,z3,z1393,z5,z6]),(0,[z1,z2,z3,z225,z962,z6]),(0,[z1,z2,z3,z1394,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 482).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 967).take 474) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1441).take 48) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1489)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [482, 485, 474, 48] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 184).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 275).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 367).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 462).take 50).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 93, 91, 92, 95, 50] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_36352

theorem PEqualNP.Outside.L_meta_36352 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36352.solve