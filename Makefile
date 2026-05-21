.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) Project.v

clean:
	rm -f *.vo* .*.aux *.cache *.glob
