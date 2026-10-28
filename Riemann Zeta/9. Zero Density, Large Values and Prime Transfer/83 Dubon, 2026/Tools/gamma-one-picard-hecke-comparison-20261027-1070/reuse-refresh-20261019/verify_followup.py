from pathlib import Path
import hashlib,json
p=Path(__file__).parent
review=json.loads((p/'direct-modular-followup-review.json').read_text(encoding='utf-8'))
for item in review['reviewedFiles']:
    data=(p/item['file']).read_bytes()
    def blobhash(b):
        return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    for candidate in [data.replace(b'\r\n',b'\n'),data[:-1],data.rstrip(b'\r\n')+b'\n']:
        if blobhash(candidate)==item['gitBlob']:
            data=candidate
            (p/item['file']).write_bytes(data)
            break
    actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert actual==item['gitBlob'], (item['file'],actual,item['gitBlob'])
    item['sha256']=hashlib.sha256(data).hexdigest()
    item['bytes']=len(data)
    item['gitBlobVerified']=True
(p/'direct-modular-followup-review.json').write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
print('PASS: both reviewed GitHub blobs reproduced exactly; no source adopted.')
