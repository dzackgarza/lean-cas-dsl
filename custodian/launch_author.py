#!/usr/bin/env python3
"""Launch a fresh author with only its role MCP capabilities.

The config and this launcher come from the protected controller deployment. This
uses existing Claude Code authentication for inference, never repository authority.
No built-in shell, file, browser, connector, delegation, publication or approval tool
is exposed. An author's candidate executes only through credential-free validation.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configuration',type=Path,required=True)
    args=parser.parse_args()
    config=args.configuration.resolve()
    cfg=json.loads(config.read_text())
    if not cfg.get('independently_supplied_assignment'):
        raise ValueError('missing launcher-supplied independent task requirement')
    source=Path(cfg['source_repository']).resolve()
    # RoleServer prepares/checks source when its MCP server starts; cwd itself need
    # not exist yet, so author has no ambient source process before capability setup.
    with tempfile.TemporaryDirectory(prefix='custodian-author-') as tmp:
        mcp=Path(tmp)/'mcp.json'
        mcp.write_text(json.dumps({'mcpServers':{'role_source':{'command':sys.executable,
            'args':[str(Path(__file__).with_name('launcher.py').resolve()),'--configuration',str(config)]}}}))
        allowed=['read_assigned_input','read_source','list_source','write_source','submit_source']
        if 'validation' in cfg:allowed.append('validate_source')
        tools=','.join('mcp__role_source__'+name for name in allowed)
        result=subprocess.run(['claude','-p','--restricted','--tools','','--allowedTools',tools,
                               '--permission-mode','dontAsk','--setting-sources','',
                               '--strict-mcp-config','--mcp-config',str(mcp),
                               '--no-session-persistence','--output-format','json'],
                              input=cfg['independently_supplied_assignment'],text=True,
                              cwd=tmp)
    return result.returncode

if __name__=='__main__':raise SystemExit(main())
