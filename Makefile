.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) AdoptCommit.v
	$(ROCQC) FastPaxos.v

clean:
	rm -f *.vo* .*.aux *.cache *.glob
