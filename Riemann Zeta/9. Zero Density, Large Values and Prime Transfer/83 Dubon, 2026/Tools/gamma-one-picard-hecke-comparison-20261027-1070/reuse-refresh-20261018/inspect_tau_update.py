from pathlib import Path
import hashlib, json, urllib.request

p = Path(__file__).parent
head = next(x for x in json.loads((p/'latest-head-check.json').read_text())['heads']
            if x['repository'] == 'TauCetiProject/TauCeti')
assert head['changed']
out = p/'tau-update-192941'
out.mkdir(exist_ok=True)
def get(url):
    request = urllib.request.Request(url, headers={'User-Agent':'Dubon-Lean-proof-reuse-review'})
    with urllib.request.urlopen(request, timeout=40) as response:
        return response.read()
repo = head['repository']
comparison = get(f'https://api.github.com/repos/{repo}/compare/{head["previousSHA"]}...{head["sha"]}')
(out/'compare.json').write_bytes(comparison)
c = json.loads(comparison)
treeBytes = get(f'https://api.github.com/repos/{repo}/git/trees/{head["sha"]}?recursive=1')
tree = json.loads(treeBytes)
assert not tree.get('truncated')
(out/'tree.json').write_bytes(treeBytes)
blobs = {x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
previous = json.loads((p/'assessment.json').read_text(encoding='utf-8'))['sourceReceipts']['tauCeti']
review = []
for entry in previous:
    f = entry['path']
    currentBlob = blobs.get(f)
    item = {'path':f, 'previousBlob':entry['gitBlob'], 'currentBlob':currentBlob,
            'changed':currentBlob != entry['gitBlob']}
    if currentBlob and item['changed']:
        url = f'https://raw.githubusercontent.com/{repo}/{head["sha"]}/{f}'
        raw = get(url)
        assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == currentBlob
        dest = out/(f+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw)
        item.update({'url':url,'file':str(dest),'sha256':hashlib.sha256(raw).hexdigest().upper()})
    review.append(item)
receipt = {'repository':repo,'previousCommit':head['previousSHA'],'commit':head['sha'],
           'date':head['date'],'comparisonStatus':c['status'],'commits':c['total_commits'],
           'treeEntries':len(tree['tree']),'treeComplete':True,'previouslyReviewedFiles':review,
           'changedPaths':[{k:x[k] for k in ('filename','status','additions','deletions')}
                           for x in c.get('files',[])]}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(receipt))
