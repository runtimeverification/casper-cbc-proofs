pipeline {
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options { ansiColor('xterm') }
  environment { COQ_PACKAGE = 'coq-casper-cbc.dev' }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Build and Test') {
      stages {
        stage('Build') {
          steps {
            sh '''
              eval $(opam env)
              opam pin add ${COQ_PACKAGE} . --yes --no-action --kind path
              opam config list
              opam repo list
              opam list
              opam install ${COQ_PACKAGE} --yes -j 6 --deps-only
            '''
          }
        }
        stage('Test') { steps { sh 'eval $(opam env) && opam install ${COQ_PACKAGE} --yes -j 6 --verbose' } }
      }
    }
    stage('Deploy Docs') {
      when { branch 'master' }
      steps {
        sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
          sh '''
            git clone 'ssh://github.com/runtimeverification/casper-cbc-proofs-docs.git'
            cd casper-cbc-proofs-docs
            git checkout -B gh-pages origin/gh-pages

            ## DO STUFF HERE (. is casper-cbc-proofs-docs@gh-pages, ../ is casper-cbc-proofs@master)

            git add ./
            git commit -m 'gh-pages: update content'
            git push origin gh-pages
          '''
        }
      }
    }
  }
}
