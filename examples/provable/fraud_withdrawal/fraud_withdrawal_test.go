package fraudwithdrawal_test

import (
	"testing"

	"github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal"
	"github.com/frederik-jatzkowski/go-lean/examples/provable/fraud_withdrawal/memory"
)

func TestWithdraw(t *testing.T) {
	for _, tc := range []struct {
		name                      string
		id, balance, amount, want uint64
		withdrawn                 bool
	}{
		{"blocked with sufficient funds", 1, 100, 80, 100, false},
		{"unknown account", 0, 100, 10, 100, false},
		{"approved", 1, 100, 20, 80, true},
		{"exact balance", 1, 50, 50, 0, true},
		{"zero amount", 1, 100, 0, 100, false},
		{"overdraft", 1, 25, 30, 25, false},
		{"absent account", 2, 0, 10, 0, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			repo := &recordingBalances{current: tc.balance, reported: tc.want}
			service := fraudwithdrawal.NewWithdrawalService(memory.Fraud{BlockAt: 80}, repo)
			balance, withdrawn := service.Withdraw(tc.id, tc.amount)
			if balance != tc.want || withdrawn != tc.withdrawn {
				t.Fatalf("Withdraw returned (%d, %t), want (%d, %t)", balance, withdrawn, tc.want, tc.withdrawn)
			}
			if repo.reads != 1 || repo.readID != tc.id {
				t.Fatalf("read account %d %d times, want account %d once", repo.readID, repo.reads, tc.id)
			}
			if tc.withdrawn {
				if repo.writes != 1 || repo.writeID != tc.id || repo.saved != tc.want {
					t.Fatalf("wrote balance %d for account %d %d times, want balance %d for account %d once", repo.saved, repo.writeID, repo.writes, tc.want, tc.id)
				}
			} else if repo.writes != 0 {
				t.Fatalf("rejected withdrawal wrote %d times", repo.writes)
			}
		})
	}
}

func TestWithdrawReturnsRepositoryReportedBalance(t *testing.T) {
	repo := &recordingBalances{current: 100, reported: 79}
	service := fraudwithdrawal.NewWithdrawalService(memory.Fraud{BlockAt: 80}, repo)
	balance, withdrawn := service.Withdraw(1, 20)
	if balance != 79 || !withdrawn || repo.saved != 80 || repo.writes != 1 {
		t.Fatalf("Withdraw returned (%d, %t) and saved %d in %d writes, want (79, true) and 80 in one write", balance, withdrawn, repo.saved, repo.writes)
	}
}

func TestWithdrawPersistsBalance(t *testing.T) {
	repo := memory.Balances{1: 100}
	service := fraudwithdrawal.NewWithdrawalService(memory.Fraud{BlockAt: 80}, repo)
	for _, step := range []struct{ amount, want uint64 }{{30, 70}, {70, 0}} {
		balance, withdrawn := service.Withdraw(1, step.amount)
		if !withdrawn || balance != step.want || repo.Balance(1) != step.want {
			t.Fatalf("Withdraw(%d) returned (%d, %t) and stored %d, want (%d, true) and stored %d", step.amount, balance, withdrawn, repo.Balance(1), step.want, step.want)
		}
	}
	if balance, withdrawn := service.Withdraw(2, 1); balance != 0 || withdrawn {
		t.Fatalf("withdrawal on absent account returned (%d, %t), want (0, false)", balance, withdrawn)
	}
}

type recordingBalances struct {
	current, reported      uint64
	readID, writeID, saved uint64
	reads, writes          int
}

func (repo *recordingBalances) Balance(accountID uint64) uint64 {
	repo.reads++
	repo.readID = accountID
	return repo.current
}

func (repo *recordingBalances) SetBalance(accountID, balance uint64) uint64 {
	repo.writes++
	repo.writeID = accountID
	repo.saved = balance
	return repo.reported
}
