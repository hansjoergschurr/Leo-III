#!groovy
node {
    stage 'Checkout'

    checkout scm
    echo "Downloading PicoSAT"
    sh "wget http://fmv.jku.at/picosat/picosat-965.tar.gz"
    sh "tar -xf picosat-965.tar.gz -C src/native"

    stage 'Build'

    sh "sbt compile"
    sh "sbt nativeCompile"

    stage 'Run'

    sh "sbt run"

}