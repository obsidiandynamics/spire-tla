default: check

workers := $(or ${workers},1)
tools_path := ~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar
check:
	java -cp ${tools_path} \
	-XX:+UseParallelGC tlc2.TLC SpireModel.tla -workers ${workers} \
	-tool -modelcheck -config SpireModel.cfg

faircheck:
	java -cp ${tools_path} \
	-XX:+UseParallelGC tlc2.TLC SpireFair.tla -workers ${workers} \
	-tool -modelcheck -config SpireFair.cfg

sim:
	java -cp ${tools_path} \
	-XX:+UseParallelGC tlc2.TLC SpireModel.tla -workers ${workers} \
	-tool -simulate -config SpireModel.cfg

soak: FORCE
	SOAK_CMD="make check workers=${workers}" SOAK_GITPULL=false ./soak.sh

pdf:
	TOOLS_PATH=${tools_path} ./makepdf.sh Spire
	TOOLS_PATH=${tools_path} ./makepdf.sh SpireModel
	TOOLS_PATH=${tools_path} ./makepdf.sh SpireTlaps

FORCE:
