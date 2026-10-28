from pathlib import Path
import concurrent.futures, datetime, json, urllib.request

p = Path(__file__).parent
previous = json.loads((p/'assessment.json').read_text(encoding='utf-8'))
repos = previous['publicHeads'] + [previous['additionalRepository']]
def check(entry):
    url = 'https://api.github.com/repos/' + entry['repository'] + '/commits?per_page=1'
    request = urllib.request.Request(url, headers={'User-Agent':'Dubon-Lean-proof-reuse-review'})
    with urllib.request.urlopen(request, timeout=35) as response:
        commit = json.loads(response.read())[0]
    return {'repository':entry['repository'], 'previousSHA':entry['sha'],
            'sha':commit['sha'], 'date':commit['commit']['committer']['date'],
            'changed':commit['sha'] != entry['sha'], 'url':commit['html_url']}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
    heads = list(pool.map(check, repos))
result = {'checkedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'heads':heads}
out = p/'latest-head-check.json'
assert not out.exists()
out.write_text(json.dumps(result, indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
