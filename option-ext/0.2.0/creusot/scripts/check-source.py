#!/usr/bin/env python3
"""Check exact release correspondence with only declared specification additions."""
import hashlib, json, sys, os
from pathlib import Path
r=Path(__file__).resolve().parents[1]
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
    raise RuntimeError('Python optimization is forbidden for evidence checks')
sys.path.insert(0,str(r.parents[2]/'scripts'))
from aeneas_management import source
source.check(source.directory(r),json.loads((r/'source.lock.json').read_text()))
s=r/'.work/source/src'
for name in ('lib.rs','impl.rs'):
    original=(s/name).read_text()
    actual=(r/'src'/name).read_text()
    # Remove precisely enumerated proof imports, annotations and erased observation.
    if name=='lib.rs':
        actual=actual.removeprefix('extern crate creusot_std;\n#[cfg(creusot)]\nuse creusot_std::prelude::*;\n\n')
        observation='''
    #[cfg(creusot)]
    #[logic]
    fn option_model(self) -> Option<T>;

'''
    else:
        actual=actual.removeprefix('#[cfg(creusot)]\nuse creusot_std::prelude::*;\n\n')
        observation='''
    #[cfg(creusot)]
    #[logic]
    #[ensures(result == self)]
    fn option_model(self) -> Option<T> { self }

'''
    assert actual.count(observation)==1
    actual=actual.replace(observation,'')
    excluded='    #[cfg(not(creusot))]\n'
    assert actual.count(excluded)==2
    actual=actual.replace(excluded,'')
    obs='self.option_model()' if name=='lib.rs' else 'self'
    allowed=[
        '    #[cfg_attr(creusot, requires(match '+obs+' { None => default.precondition(()), Some(t) => f.precondition((t,)) }))]\n',
        '    #[cfg_attr(creusot, ensures(match '+obs+' { None => resolve(f) && default.postcondition_once((), result), Some(t) => resolve(default) && f.postcondition_once((t,), result) }))]\n',
    ]
    for annotation in allowed:
        assert actual.count(annotation)==1
        actual=actual.replace(annotation,'')
    assert actual==original, 'Unexpected source adaptation: '+name
    print(name,'release_sha256',hashlib.sha256(original.encode()).hexdigest(),
          'annotated_sha256',hashlib.sha256((r/'src'/name).read_bytes()).hexdigest())
print('All runtime release bytes preserved after removing enumerated proof-only additions.')
