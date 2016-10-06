node {
    stage 'Checkout'

    checkout scm

    stage 'Build'

    sh "sbt compile"
    sh "sbt compileNative"

    stage 'Run'

    sh "sbt run"

}