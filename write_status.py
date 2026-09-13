"""Collect evidence without promoting finite checks to a Lean Ramsey theorem."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

HERE=Path(__file__).resolve().parent

def main():
    def read(name):return json.loads((HERE/name).read_text())
    exact=read('certificates/quantized/verification.json')
    lean=read('runs/support_weighted_complete.json')
    assert exact['status']=='PASS_FINITE_CHAIN_NOT_LEAN'
    assert exact['terminal']['status']=='PASS_TARGET'
    assert exact['simple_terminal']['status']=='PASS_TARGET'
    assert lean['status']=='PASS_SUPPORT_LIBRARY_NOT_RAMSEY_THEOREM'
    resources={}
    for label,name in [('quantized_replay','verify_quantized'),('support_library','support_weighted_complete'),
                       ('terminal_lean','lean_terminal_final'),('blue1024_kernel','lean_blue1024_kernel'),
                       ('full_log_catalog_kernel','kernel_catalog_full'),
                       ('full_initial_tangents_kernel','initial_kernel_all'),
                       ('initial_profile_assembly','initial_profile_assembly'),
                       ('terminal_graph_transfer','terminal_asymptotic_second'),
                       ('terminal_target','terminal_target_second'),
                       ('packed_catalog','packed_kernel_catalog'),
                       ('all_profile_checks','profile_kernel_all_second'),
                       ('full_record_soundness','chain_sound_second'),
                       ('full_round_soundness','round_sound_second'),
                       ('strict_terminal_target','terminal_strict'),
                       ('actual_record_run_batches','actual_chain_bench_second'),
                       ('complete_first_round_guards','chain_r00_full_second'),
                       ('complete_first_round_outer','outer_r00_full'),
                       ('pinned_support_recheck','pinned_support_recheck'),
                       ('largest_round_data_preparation','chain_data_r07'),
                       ('actual_largest_round_samples','r07_actual_run_samples'),
                       ('closed_3_72_checkpoint','closed_first_numeric')]:
        r=read('runs/'+name+'.resources.json')
        assert r['status']=='PASS_PROCESS'
        resources[label]={k:r[k] for k in ['elapsed_seconds','peak_sampled_rss_kib','rss_limit_mib']}
    paths=sorted([p for pattern in ['*.py','*.cpp','*.md','lean/**/*.lean','lean/*.toml']
                  for p in HERE.glob(pattern)])
    paths.append(HERE/'lean/lean-toolchain')
    hashes={str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    certificate_hashes={}
    for p in sorted((HERE/'certificates/quantized').iterdir()):
        if not p.is_file():continue
        digest=hashlib.sha256()
        with p.open('rb') as f:
            for block in iter(lambda:f.read(2**20),b''):digest.update(block)
        certificate_hashes[str(p.relative_to(HERE))]=digest.hexdigest()
    build_log=(HERE/'runs/support_weighted_complete.resources.log').read_text()
    assert 'sorryAx' not in build_log and 'error:' not in build_log
    expected_axioms="'Ramsey3683Bootstrap.isGood_of_density_weighted_card_product' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert expected_axioms in build_log
    assert 'Ramsey3683Bootstrap/WeightedUniform' in lean['modules']
    for name in ['initial_profile_assembly','terminal_asymptotic_second','terminal_target_second']:
        log=(HERE/('runs/'+name+'.resources.log')).read_text()
        assert 'sorryAx' not in log and 'error:' not in log
    checkpoint_log=(HERE/'runs/closed_first_numeric.resources.log').read_text()
    assert "'Compact3684.ramsey_le_372' depends on axioms: [propext, Classical.choice, Quot.sound]" in checkpoint_log
    assert 'sorryAx' not in checkpoint_log and 'error:' not in checkpoint_log
    result=dict(status='CLOSED_3_72_CHECKPOINT_FULL_3_68395_KERNEL_EXECUTION_IN_PROGRESS',
        target_below_3684_lean_theorem=False,full_certificate_kernel_checked=False,
        closed_checkpoint=dict(theorem='Compact3684.ramsey_le_372',base='93/25',base_decimal='3.72',
            unconditional=True,pinned_upstream_rechecked=True,below_3684=False),
        weighted_uniform_graph_theorem=True,finite_candidate_continuation_checked=True,
        grid_continuation_and_profile_semantics=True,real_log_interval_soundness=True,
        all_351607_logarithms_kernel_checked=True,initial_profile_unconditional=True,
        all_20000_initial_tangents_kernel_checked=True,terminal_graph_transfer=True,
        full_record_path_checker_soundness=True,full_round_checker_soundness=True,
        all_126192_profile_region_checks=True,strict_terminal_base='73679/20000',
        weighted_theorem='Ramsey3683Bootstrap.isGood_of_density_weighted_card_product',
        weighted_theorem_axioms=['propext','Classical.choice','Quot.sound'],
        dependency_builds_reused=True,complete_ramsey_runtime_measured=False,
        target='921/250',finite_upper_base=exact['terminal']['base_upper_decimal'],
        simple_affine_intercept='68/125',simple_affine_slope='3811/5000',
        simple_terminal_upper=exact['simple_terminal']['base_upper_decimal'],
        records=exact['records'],path_runs=exact['path_runs'],
        shared_logarithms=exact['verified_log_catalog_entries'],resources=resources,
        remaining=['complete concrete execution of compressed record/path/profile guards',
                   'concrete affine-profile theorem and unconditional assembly',
                   'resource-monitored complete verification under the one-week budget'],source_sha256=hashes,
        certificate_sha256=certificate_hashes)
    final_path=HERE/'runs/pinned_final.resources.json'
    if final_path.exists():
        final_resource=read('runs/pinned_final.resources.json')
        if final_resource['status']=='PASS_PROCESS':
            final=read('runs/pinned_final.json')
            assert final['status']=='PASS_UNCONDITIONAL_RAMSEY_THEOREM_PINNED_UPSTREAM'
            assert final['theorem']=='Compact3684.ramsey_le_368395'
            assert final['base']=='73679/20000'
            assert final['axioms']==['propext','Classical.choice','Quot.sound']
            assert final['final_source_sha256']==hashes['lean/RamseyBelow3684.lean']
            final_log=(HERE/'runs/pinned_final_theorem.log').read_text()
            assert "'Compact3684.ramsey_le_368395' depends on axioms: [propext, Classical.choice, Quot.sound]" in final_log
            assert 'sorryAx' not in final_log and 'Lean.ofReduceBool' not in final_log and 'error:' not in final_log
            for label in ['rounds_01_06_full','round_07_full']:
                assert read('runs/'+label+'.json')['status']=='PASS_ALL_REQUESTED_ROUND_CHECKS_NOT_HEADLINE_THEOREM'
            for label in ['rounds_01_06_full','round_07_full','final_assembly_second','pinned_final']:
                from supervision_evidence import resource_passed
                r=read('runs/'+label+'.resources.json');assert resource_passed(r)
                resources[label]={k:r[k] for k in ['elapsed_seconds','peak_sampled_rss_kib','rss_limit_mib']}
                if r['status']=='PASS_DURABLE_VERIFICATION':
                    resources[label].update(supervision_status=r['status'],
                        continuous_memory_measurement=False,
                        original_exit_code=None,measurement_gap_note=r['measurement_gap_note'])
            assert read('runs/stable_dependency_exports.json')['status']=='PASS_EXACT_STABLE_EXPORT_EXPRESSIONS'
            assert read('runs/dependency_reference_boundary.resources.json')['status']=='PASS_PROCESS'
            budget=read('verification_budget.json')
            origin=datetime.fromisoformat(budget['verification_budget_origin_utc'].replace('Z','+00:00'))
            ended=datetime.fromtimestamp(final_path.stat().st_mtime,timezone.utc)
            elapsed=(ended-origin).total_seconds()
            assert 0<elapsed<=budget['complete_verification_wall_time_limit_seconds']
            result.update(status='PASS_COMPLETE_UNCONDITIONAL_RAMSEY_BASE_3_68395',
                target_below_3684_lean_theorem=True,full_certificate_kernel_checked=True,
                complete_ramsey_runtime_measured=True,final_theorem=final,remaining=[],
                measured_verification=dict(origin_utc=origin.isoformat(),completion_utc=ended.isoformat(),
                    elapsed_seconds=elapsed,one_week_limit_seconds=604800,
                    external_dependency_builds_reused=True,
                    note='Observed complete development verification, including overlapping jobs and experiments; not a fresh external dependency build'))
            aggregate=HERE/'runs/aggregate_complete_pipeline.json'
            if aggregate.exists():
                result['aggregate_rss_monitor_window']=json.loads(aggregate.read_text())
            recovered=HERE/'runs/aggregate_recovered_pipeline.json'
            if recovered.exists():
                result['aggregate_rss_recovery_window']=json.loads(recovered.read_text())
                result['continuous_memory_measurement']=False
        else:
            result['latest_final_attempt_status']=final_resource['status']
            # A failed supervising process can never promote the headline.
            # Its underlying progress remains available for a bounded repair.
    (HERE/'STATUS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['source_sha256','certificate_sha256']},indent=2))

if __name__=='__main__':main()
