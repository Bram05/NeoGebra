// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "ErrorBox.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"

using namespace std::chrono_literals;
constexpr std::chrono::duration showTime = 8s;

static void RemoveText(ErrorBox* obj, bool* shouldStop)
{
	std::chrono::time_point begin = std::chrono::steady_clock::now();
	while (std::chrono::steady_clock::now() - begin < showTime)
	{
		std::this_thread::sleep_for(5ms);
		if (*shouldStop)
			return;
	}
	obj->RemoveError();
}

ErrorBox::ErrorBox(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "MenuUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	m_ErrorText = std::make_shared<Text>("", leftX + 0.01f, rightX - 0.01f, topY - 0.3f, 35.0f, true, std::array<float, 4>{1.0f, 0.0f, 0.0f, 1.0f});
	m_ErrorBoxText = std::make_shared<Text>("Error Box: any errors will be displayed in here.", m_LeftX + 0.01f, m_RightX - 0.01f, m_BottomY + 0.43f, 35.0f);// Init empty object
}

void ErrorBox::DisplayError(const AdvancedString& text)
{
	if (m_CountingThread)
	{
		*m_CountingThreadBool = true;
		m_CountingThread->join();
		delete m_CountingThread;
		delete m_CountingThreadBool;
	}
	m_ErrorText->SetText(text);
	m_CountingThreadBool = new bool{false};
	m_CountingThread = new std::thread(RemoveText, this, m_CountingThreadBool);
}

void ErrorBox::RemoveError()
{
	m_ErrorText->SetText("");
}

ErrorBox::~ErrorBox()
{
}

void ErrorBox::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_ErrorText);
	r->AddToRenderQueue(m_ErrorBoxText);

	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}

	UIElement::RenderPass(r);
}