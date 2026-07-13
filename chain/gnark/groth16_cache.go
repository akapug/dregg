// THE TRUSTED-SETUP PARAM CACHE — reuse the dev Groth16 params across runs
// instead of re-running the ceremony on an unchanged circuit.
//
// groth16.Setup on the multi-million-constraint SettlementCircuit is a
// minutes-long single-party ceremony whose output depends only on the compiled
// constraint system (plus the ceremony randomness, which the DEV setup is
// allowed to reuse — see the warning below). This cache keys the (pk, vk)
// pair by a CONTENT HASH of the serialized R1CS: an unchanged circuit loads
// the cached params and skips Setup entirely; any change to the circuit —
// constraint count, wiring, coefficients, public arity — changes the
// serialization, misses the cache, and forces a fresh Setup.
//
// Fingerprint honesty: the key is sha256 over gnark's own ccs.WriteTo (CBOR)
// serialization of the compiled system — the full constraint content, not a
// proxy like the constraint count. It is stable for the same circuit + gnark
// version on any machine; a gnark upgrade that changes the serialization
// format conservatively MISSES (a fresh Setup, never a wrong hit).
//
// ⚠ DEV PARAMS ONLY: these are single-party-ceremony params — whoever ran
// Setup (or holds this cache) knows the toxic waste and can forge proofs for
// this VK. Caching them REUSES that same waste across runs, which is exactly
// right for dev speed + reproducibility (the Foundry fixture, the bridge
// calldata pin, and the exported Solidity verifier all stay coherent between
// regenerations of the same circuit) and exactly wrong for production: a real
// deployment needs an MPC ceremony, and its output would NOT live here.
//
// Layout (gitignored — see .gitignore):
//
//	.groth16-cache/<fp>.pk  — groth16.ProvingKey via WriteDump (fast raw dump)
//	.groth16-cache/<fp>.vk  — groth16.VerifyingKey via WriteRawTo
package friverifier

import (
	"bufio"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
)

const groth16CacheDir = ".groth16-cache"

// groth16CircuitFingerprint content-hashes the compiled constraint system:
// sha256 over gnark's canonical (CBOR) serialization, hex-truncated to 128
// bits for the filename.
func groth16CircuitFingerprint(ccs constraint.ConstraintSystem) (string, error) {
	h := sha256.New()
	if _, err := ccs.WriteTo(h); err != nil {
		return "", fmt.Errorf("fingerprint: serialize ccs: %w", err)
	}
	return hex.EncodeToString(h.Sum(nil))[:32], nil
}

// groth16LoadOrSetup returns the Groth16 params for ccs: a cache hit loads
// them from .groth16-cache/ and SKIPS groth16.Setup; a miss runs the (dev,
// single-party) Setup and writes the cache for the next run. cacheHit reports
// which path ran. A corrupt or unreadable cache entry falls back to a fresh
// Setup (and rewrites the entry) rather than failing the run.
func groth16LoadOrSetup(ccs constraint.ConstraintSystem, curve ecc.ID,
	logf func(format string, args ...any)) (pk groth16.ProvingKey, vk groth16.VerifyingKey, cacheHit bool, err error) {
	fpStart := time.Now()
	fp, err := groth16CircuitFingerprint(ccs)
	if err != nil {
		return nil, nil, false, err
	}
	logf("param cache: circuit fingerprint %s (%d constraints; hashed in %s)",
		fp, ccs.GetNbConstraints(), time.Since(fpStart).Round(time.Millisecond))
	pkPath := filepath.Join(groth16CacheDir, fp+".pk")
	vkPath := filepath.Join(groth16CacheDir, fp+".vk")

	if pk, vk, err := readGroth16Cache(curve, pkPath, vkPath); err == nil {
		logf("param cache: HIT — loaded dev params from %s + %s, groth16.Setup SKIPPED", pkPath, vkPath)
		return pk, vk, true, nil
	} else if !os.IsNotExist(err) {
		logf("param cache: entry unreadable (%v) — falling back to a fresh Setup", err)
	} else {
		logf("param cache: MISS — running the (UNSAFE dev single-party) groth16.Setup")
	}

	pk, vk, err = groth16.Setup(ccs)
	if err != nil {
		return nil, nil, false, err
	}
	if werr := writeGroth16Cache(pk, vk, pkPath, vkPath); werr != nil {
		// The cache is an accelerator, never a gate: log and keep the params.
		logf("param cache: WRITE FAILED (%v) — params still valid for this run", werr)
	} else {
		logf("param cache: wrote %s + %s (next run for this circuit skips Setup)", pkPath, vkPath)
	}
	return pk, vk, false, nil
}

func readGroth16Cache(curve ecc.ID, pkPath, vkPath string) (groth16.ProvingKey, groth16.VerifyingKey, error) {
	pkf, err := os.Open(pkPath)
	if err != nil {
		return nil, nil, err
	}
	defer pkf.Close()
	vkf, err := os.Open(vkPath)
	if err != nil {
		return nil, nil, err
	}
	defer vkf.Close()

	pk := groth16.NewProvingKey(curve)
	if err := pk.ReadDump(bufio.NewReaderSize(pkf, 1<<20)); err != nil {
		return nil, nil, fmt.Errorf("read pk dump %s: %w", pkPath, err)
	}
	vk := groth16.NewVerifyingKey(curve)
	// UnsafeReadFrom skips subgroup checks (this is OUR local dump) but still
	// runs the pairing Precompute the verifier needs.
	if _, err := vk.UnsafeReadFrom(bufio.NewReaderSize(vkf, 1<<20)); err != nil {
		return nil, nil, fmt.Errorf("read vk %s: %w", vkPath, err)
	}
	return pk, vk, nil
}

// writeGroth16Cache writes both keys atomically (tmp + rename) so an
// interrupted run never leaves a half-written entry that a later run would
// trust.
func writeGroth16Cache(pk groth16.ProvingKey, vk groth16.VerifyingKey, pkPath, vkPath string) error {
	if err := os.MkdirAll(filepath.Dir(pkPath), 0o755); err != nil {
		return err
	}
	writeAtomic := func(path string, write func(f *os.File) error) error {
		tmp, err := os.CreateTemp(filepath.Dir(path), filepath.Base(path)+".tmp-*")
		if err != nil {
			return err
		}
		defer os.Remove(tmp.Name()) // no-op after a successful rename
		if err := write(tmp); err != nil {
			tmp.Close()
			return err
		}
		if err := tmp.Close(); err != nil {
			return err
		}
		return os.Rename(tmp.Name(), path)
	}
	if err := writeAtomic(pkPath, func(f *os.File) error {
		bw := bufio.NewWriterSize(f, 1<<20)
		if err := pk.WriteDump(bw); err != nil {
			return err
		}
		return bw.Flush()
	}); err != nil {
		return fmt.Errorf("write pk dump: %w", err)
	}
	if err := writeAtomic(vkPath, func(f *os.File) error {
		_, err := vk.WriteRawTo(f)
		return err
	}); err != nil {
		return fmt.Errorf("write vk: %w", err)
	}
	return nil
}
