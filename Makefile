default: check


workers := $(or ${workers},1)
check:
	java -cp ~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar \
	-XX:+UseParallelGC tlc2.TLC SpireModel.tla -workers ${workers} \
	-tool -modelcheck -config SpireModel.cfg

sim:
	java -cp ~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar \
	-XX:+UseParallelGC tlc2.TLC SpireModel.tla -workers ${workers} \
	-tool -simulate -config SpireModel.cfg

soak: FORCE
	SOAK_CMD="make check workers=${workers}" SOAK_GITPULL=false ./soak.sh

pdf:
	./makepdf.sh Spire
	./makepdf.sh SpireModel
	./makepdf.sh SpireTlaps

FORCE:
