#!/usr/bin/env python3
"""Protected-base verification of an accepted input publication PR; candidate is data."""
import argparse
import json
from pathlib import Path
from apply_assessment import assemble


def verify(configuration, candidate):
    if (candidate/'custodian').is_symlink() or (candidate/'custodian/deployment.json').is_symlink():raise ValueError('linked authority input')
    baseline=json.loads(configuration.read_text())
    proposed=json.loads((candidate/'custodian/deployment.json').read_text())
    if proposed==baseline:return
    evidence=candidate/'custodian/admission'
    matches=[]
    if evidence.is_symlink():raise ValueError('linked authority evidence')
    if evidence.is_dir():
        for folder in evidence.iterdir():
            if not folder.is_dir() or folder.is_symlink():continue
            try:
                if any((folder/name).is_symlink() for name in ('request.json','decision.json','decision.json.sig')):continue
                result=assemble(configuration,folder/'request.json',folder/'decision.json',folder/'decision.json.sig')
                if result==proposed:matches.append(folder.name)
            except (ValueError,KeyError,OSError,RuntimeError):continue
    if len(matches)!=1:raise ValueError('configuration advancement lacks a unique independently signed exact assessment')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--configuration',type=Path,required=True)
    p.add_argument('--candidate-tree',type=Path,required=True)
    a=p.parse_args();verify(a.configuration,a.candidate_tree)

if __name__=='__main__':main()
