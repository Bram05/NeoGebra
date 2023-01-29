#include "MainWindowUI.h"

#include "EquationUI.h"
#include "ButtonUI.h"
#include "GraphUI.h"
#include "MenuUI.h"
#include "TabUI.h"
#include "FPSCounterUI.h"
#include "ErrorBox.h"
#include "PostulateVerifierResultUI.h"
#include "Constants.h"

MainWindowUI::MainWindowUI()
{
	m_UIElements.push_back(std::make_shared<ErrorBox>(0.5f, 1.0f, -0.5f, -1.0f));
	m_UIElements.push_back(std::make_shared<EquationUI>(-1.0f, -0.5f, 0.9f, -1.0f));
	m_UIElements.push_back(std::make_shared<PostulateVerifierResultUI>(0.5f, 1.0f, 0.9f, -0.5f));
	m_UIElements.push_back(std::make_shared<GraphUI>(-0.5f, 0.5f, 0.9f, -1.0f));
	m_GraphUIIndex = m_UIElements.size() - 1;
	m_UIElements.push_back(std::make_shared<MenuUI>(-1.0f, 1.0f, 1.0f, 0.9f));
#ifdef TIMING
	m_UIElements.push_back(std::make_shared<FPSCounterUI>(0.7f, 1.0f, 1.0f, 0.8f));
	m_FPSCounterIndex = m_UIElements.size() - 1;
#endif
}

void MainWindowUI::DisplayError(const AdvancedString& error) {
	(*(std::shared_ptr<ErrorBox>*) & m_UIElements[0])->DisplayError(error);
}

void MainWindowUI::UpdateGraphUI()
{
	for (std::shared_ptr<UIElement>& el : m_UIElements)
	{
		el->UpdateGraphUI();
	}
}

void MainWindowUI::SetFPSCounter(float fps)
{
#ifdef TIMING
	(*(std::shared_ptr<FPSCounterUI>*) & m_UIElements[m_FPSCounterIndex])->SetCounter(fps);
#endif
}

GraphUI* MainWindowUI::GetGraphUI()
{
	return (GraphUI*)m_UIElements[m_GraphUIIndex].get();
}