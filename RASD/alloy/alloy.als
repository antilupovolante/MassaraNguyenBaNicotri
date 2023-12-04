-- Signatures

sig Nickname {}
sig EmailAddr {}
sig Password {}
sig Name {}
sig Surname {}
sig GitHubAccount {}
sig Date {
	value: Int  -- value represents the distance in days from 1-1-1900
} {value >= 0}
sig CodeKata {}

abstract sig User {
	nickname: Nickname,
	emailAddr: EmailAddr,
	password: Password,
	name: Name,
	surname: Surname,
	dateOfBirth: Date,
}

sig Educator extends User {}

sig Student extends User {
	githubAccount: GitHubAccount
}

sig SubscribedStudent {
	student: Student,
	var score: Int
} {score >= 0}

abstract sig TournamentStatus{}
one sig TAvailable, TActive, TEnded extends TournamentStatus{}
abstract sig BattleStatus{}
one sig BAvailable, BActive, BEnded extends BattleStatus{}

sig Tournament {
	name: Name,
	creator: Educator,
	educators: some Educator,
	subscribedStudents: set SubscribedStudent,
	registrationDeadline: Date,
	battles: set Battle,
	var status: TournamentStatus
}

sig Rules {
	minimumNumberOfStudents: Int,
	maximumNumberOfStudents: Int
} {minimumNumberOfStudents > 0}

sig Team {
	students: some Student,
	var score: Int
} {score >= 0}

sig Battle {
	creator: Educator,
	codeKata: CodeKata,
	registrationDeadline: Date,
	submissionDeadline: Date,
	subscribedStudents: set Student,
	rules: Rules,
	teams: set Team,
	var status: BattleStatus
}

-- Facts

-- Date
fact dateIsUnique {
	no disj d1 , d2 : Date | d1.value = d2.value
}

-- User
fact nicknamesAreUnique {
	no disj u1 , u2 : User | u1.nickname = u2.nickname
}

fact emailsAreUnique {
	no disj u1 , u2 : User | u1.emailAddr = u2.emailAddr
}

fact usernameExistsOnlyWithUser {
	all nn : Nickname | one u : User | nn in u.nickname
}

fact emailAddrExistsOnlyWithUser {
	all email : EmailAddr | one u : User | u.emailAddr in email
}

fact passwordExistsOnlyWithUser {
	all pw : Password | one u : User | u.password in pw
}

fact nameExistsOnlyWithUser {
	all nm : Name | one u : User | u.name in nm
}

fact surnameExistsOnlyWithUser {
	all sm : Surname | one u : User | u.surname in sm
}

fact dateOfBirthExistsOnlyWithUser {
	all dob : Date | one u : User | u.dateOfBirth in dob
}

-- Student

fact githubAccountsAreUnique {
	no disj u1 , u2 : Student | u1.githubAccount = u2.githubAccount
}

fact githubAccountExistsOnlyWithUser {
	all gha: GitHubAccount | one s : Student | s.githubAccount in gha
}

-- Code Kata

fact codeKataExistsOnlyWithBattle {
	all ck: CodeKata | one b : Battle | b.codeKata in ck
}

-- Tournament

fact tournamentNameIsUnique {
	no disj t1, t2: Tournament | t1.name = t2.name
}

fact tournamentExistsOnlyWithCreator {
	all t: Tournament | one e : Educator | e in t.creator
}

fact creatorHasAccessToTournament {
	all t: Tournament | t.creator in t.educators 
}

fact registrationDeadlineIsAfterCreatorDateOfBirth {
	all t: Tournament | t.registrationDeadline.value > t.creator.dateOfBirth.value
}

fact registrationDeadlineIsAfterEducatorsDatesOfBirth {
	all t: Tournament, e: t.educators | t.registrationDeadline.value > e.dateOfBirth.value
}

fact registrationDeadlineIsAfterStudentsDatesOfBirth {
	all t: Tournament, s: t.subscribedStudents.student | t.registrationDeadline.value > s.dateOfBirth.value
}

-- Rules
fact minimumNumberOfStudentsIsLessThanMaximumNumberOfStudents {
	all r: Rules | r.minimumNumberOfStudents <= r.maximumNumberOfStudents
}

fact rulesExistsOnlyWithBattle {
	all r: Rules | one b: Battle | b.rules in r
}

-- Battle
fact creatorHasPermissionToCreateBattle {
	all t: Tournament, b: t.battles | b.creator in t.educators
}

fact registrationDeadlineIsAfterTournamentRegistrationDeadline {
	all t: Tournament, b: t.battles | b.registrationDeadline.value > t.registrationDeadline.value
}

fact submissionDeadlineIsAfterRegistrationDeadline {
	all b: Battle | b.submissionDeadline.value > b.registrationDeadline.value
}

fact subscribedStudentsAreSubscribedToTournament {
	all t: Tournament, b: t.battles, s: b.subscribedStudents | s in t.subscribedStudents.student
}

fact teamExistsOnlyWithBattle {
	all t: Team | one b: Battle | t in b.teams
}

fact teamHasAtLeastMinimumNumberOfStudents {
	all b: Battle, t: b.teams| #t.students >= b.rules.minimumNumberOfStudents
}

fact teamHasAtMostMaximumNumberOfStudents {
	all b: Battle, t: b.teams| #t.students <= b.rules.maximumNumberOfStudents
}

fact teamStudentsAreSubscribedToBattle {
	all b: Battle, t: b.teams, s: t.students | s in b.subscribedStudents
}

fact availableTournamentHasNoBattle {
	all t: Tournament | t.status = TAvailable implies t.battles = none
}

fact endedTournamentHasNoaActiveBattle {
	all t: Tournament | t.status = TEnded implies all b: t.battles | b.status = BEnded
}

fact activeBattleImpliesActiveTournament {
	all t: Tournament, b: t.battles | b.status = BActive implies t.status = TActive
}

-- Predicates

pred tournamentDeadlineExpires[t: Tournament] {
	t.status = TAvailable
	t.status' = TActive
	all s: t.subscribedStudents | s.score' = 0
}

pred tournamentEnds[t: Tournament] {
	t.status = TActive
	t.status' = TEnded
}

pred battleRegistrationDeadlineExpires[b: Battle] {
	b.status = BAvailable
	b.status' = BActive
	all team: b.teams | team.score' = 0
}

pred battleEnds[b: Battle] {
	b.status = BActive
	b.status' = BEnded
}

pred show [t: Tournament, b: Battle] {
	#t.subscribedStudents > 0
	#t.battles > 0
	#b.teams > 0
}

-- Assertions

assert activeTournamentWasOnceAvailable {
	all t: Tournament | tournamentDeadlineExpires[t] implies once t.status = TAvailable
}

assert endedTournamentWasOnceActive {
	all t: Tournament | tournamentEnds[t] implies once t.status = TActive
}

assert activeBattleWasOnceAvailable {
	all b: Battle | battleRegistrationDeadlineExpires[b] implies once b.status = BAvailable
}

assert endedBattleWasOnceActive {
	all b: Battle | battleEnds[b] implies once b.status = BActive
}

check activeTournamentWasOnceAvailable for 5 but 1 Tournament, 1 Battle, 2 Student
check endedTournamentWasOnceActive for 5 but 1 Tournament, 1 Battle, 2 Student
check activeBattleWasOnceAvailable for 5 but 1 Tournament, 1 Battle, 2 Student
check endedBattleWasOnceActive for 5 but 1 Tournament, 1 Battle, 2 Student

-- Run
run show for 5 but 1 Tournament, 1 Battle, 2 Student
